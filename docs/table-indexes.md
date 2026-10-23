# Declarative correlated collection indexes

`table-indexes source declarations` derives a complete persistent table descriptor
in the existing `clan/poo/table` interface. The standard `table/indexes.scm` include
shares the original table/delta/Wrap implementation and `std/make extra-inputs`.
It advances the general collection proposal's future work; it does not introduce a
new database engine, global registry or automatic backend selection.

## Declare once, update one whole snapshot

Each POO declaration supplies `name` (unique symbol), `table` (persistent index
backend), `project` (pure `primary-key, admitted-row -> admitted-index-key`) and
`unique?` (Boolean). A unique index's Value Type must be exactly `source.Key`.
A grouped index's Value Type must be exactly `source`: each bucket is an existing
persistent primary-table instance, with the original checked row values.

```scheme
(def indexed (table-indexes source
  (list (.cc Type. name: 'badge table: (RationalDict (.@ source Key))
          project: (lambda (_ row) (vector-ref row 0)) unique?: #t)
        (.cc Type. name: 'team table: (SimpleTrie UInt source)
          project: (lambda (_ row) (vector-ref row 2)) unique?: #f))))
(def state (.call indexed .wrap admitted-primary))
(def next (.call indexed .apply-delta state delta))
(.call indexed .index-ref/opt next 'badge 103) ; (some primary-key) or #f
(.call indexed .index-ref/opt next 'team 20)   ; (some source-table) or #f
```

Primary key/value Types and both traversal orders stay those of `source`.
Ordinary lenses, serialization of supported children, FUN Wrap and table algorithms
reuse that protocol. `.wrap` accepts an already admitted primary; `.unwrap` returns
its same persistent root. Raw input is normalized explicitly through existing
`validate` first. Function procedures/keys must already be admitted and stable;
index construction does not discard or silently replace their wrappers.

## Atomic delta and batch semantics

1. Check snapshot ownership, all metadata origins and every primary delta
   expectation. Primary conflicts precede index callbacks and retain their key.
2. For each declaration in order, retract old entries for every edited primary key.
3. Insert the **final** primary rows for those keys. Grouped empty buckets disappear.
   Repeated edits require no additional mutable key set. A unique insertion accepts
   absence or the same owner; a different owner raises `table-index-conflict` with
   `name`, projected `key`, `existing` owner and `incoming` owner.
4. Return a single private snapshot only after all indexes succeed. A later index
   failure exposes neither the staged primary nor earlier prepared indexes.

Uniqueness applies at the atomic installation boundary. Two identifiers can swap;
a transient duplicate removed by the same composed batch is allowed. Intermediate
**primary old-value checks** are still retained, never squashed to endpoints.
`.compose-deltas` followed by `.apply-delta` defines one such boundary; separate
installations each enforce uniqueness separately. Single `.acons` / `.remove`
reuse original difference discovery and the same installer.

Only `.index-ref/opt` exposes cached observations: a unique owner or a persistent
group bucket, both optional. Missing and stored false remain distinct through the
existing Option convention. Unknown declarations, wrong projected key Types and
foreign snapshots refuse. Backend/projector exceptions preserve their causes.

## Ownership, failure and recovery

`table-styles indexed` directly derives Pure / Mutable / Linear wrappers. A failed
unique check consumes no reference and installs nothing. After success, the
existing style protocol handles mutable identity or consumes old linear aliases.
A fresh explicit retry may reuse an unchanged owner; competition keeps the winner.
No callback effect is replayed or rolled back automatically.

`invert-table-delta` reuses original before/after values and reverse edit order.
With stable projections and unchanged metadata, applying the inverse restores all
primary, unique-owner and grouped-member observations, including opaque callback
identities. Tree balance/allocation/physical root identity need not be restored.
All declarations, index backends, child Types, primary origins and later delta
origins remain dependencies, including origins introduced by empty deltas.

Persistent backend laws, immutable-by-discipline row/leaf values, stable pure
projections and agreement of primary-key equality with `equal?` are explicit
premises. Projections yield one key per row; arbitrary mutable closure state is
not tracked. Metadata changes must be serialized with operations; the existing
style lock protects owner installation, not a global metadata transaction.

## Implementation, proof and costs

`examples/service-collection.ss` declares two RationalDict unique indexes and a
Trie team index, sharing primary RationalDict buckets and checked Functions.
Regressions combine identifier swaps, repeated updates, deletion/reinsertion,
team migration, late unique refusal, old-value precedence, undo/retry, empty-origin
invalidation, all three styles and a `table-wrapper` host carrier.

`LeanPoo/Functional/TableIndex.lean` proves changed-column retraction/insertion,
whole heterogeneous-family correlation, repeated-key stability, exact unique-claim
cases, finite uniqueness soundness with complete enumeration, declaration failure
order, atomic install success/refusal, style failure retention and inverse primary /
cache observations. `Examples/TableRevision.lean` supplies a heterogeneous-key
family, identifier swap, shared callbacks, temporary rows and late conflicts.

The finite Lean validator is a reference oracle, not the Scheme hot algorithm.
Scheme maintains existing unique-owner maps and grouped tables. Under the stated
invariant, retracting all touched old entries then claiming final owners enforces
final uniqueness; the model proves claim behavior and changed-column correlation.
There is no extraction/compiler proof or blanket certification of arbitrary user
projections and comparator implementations.

Cold construction visits every primary row for each declaration. Warm delta
installation invokes at most two projections per edit per declaration; missing
old/new rows invoke fewer. Unaffected primary rows and their cached entries are
not projected or scanned by that installer. Point backend work, grouped bucket
updates, metadata admission, and recognition retain their own costs. Single writes
currently use full difference discovery; style admission/recognition may enumerate.
The 100-row regression verifies two projections for a one-row delta, not constant
end-to-end time or a wall-clock speedup. Indexes over ranges, multiple keys per row,
and automatic query/representation optimization remain separate work.

## Explicit ordered backends

Declare `table-order backend comparer` as an index table to enable `.index-range`.
It applies the same comparator and Option bounds to unique owners or grouped
primary buckets. Revision, uniqueness, retry, inverse and style ownership are
unchanged. See [table-order.md](table-order.md) for positioning on declared backends, the sorting fallback,
and explicit law, invalidation and cost boundaries.
