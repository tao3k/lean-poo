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
4. Recognize each complete cache through its declared table Type before preparing
   the next declaration. This includes the carrier, typed owner values, custom
   whole-cache refinements and every grouped bucket's source-table refinement.
5. Return a single private snapshot only after all indexes succeed. A later index
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
old/new rows invoke fewer. Unaffected primary rows are not re-projected by the delta-maintenance kernel.
Complete source/cache recognition can still scan them before publication; the
sparse projection bound is not an O(delta) whole-workflow bound. Point backend
work, grouped bucket updates, metadata admission and recognition retain their
own costs. Single writes
now capture one optional delta without a trial carrier or full difference discovery;
source/style admission and recognition may still enumerate.
The 100-row regression verifies two projections for a one-row delta, not constant
end-to-end time or a wall-clock speedup. Explicit ordered ranges and finite multiple-key projections are implemented below.
Automatic query/representation optimization remains separate work.


Local full acceptance passed all 127 modules / 1,229 cases in the standard linked
single-process runner: exit 0, wall 29.818 s, CPU 18.469 s and GC CPU 3.327 s.
The 1 GiB heap, 300 s whole-suite limit and all original checks remain unchanged.
This receipt is not a matched performance comparison.

## Explicit ordered backends

Declare `table-order backend comparer` as an index table to enable `.index-range`.
It applies the same comparator and Option bounds to unique owners or grouped
primary buckets. Revision, uniqueness, retry, inverse and style ownership are
unchanged. See [table-order.md](table-order.md) for positioning on declared backends, the sorting fallback,
and explicit law, invalidation and cost boundaries.

## Finite multiple-key declarations

`multiple?: #t` declares that `project` returns a finite proper list of index keys.
Omitting the flag means exactly one key, including a list-valued key when the
backend actually supports it. The flag is checked with Gerbil's contract mechanism;
no projection cardinality is guessed from a value. All projected keys must already
belong to the declared Key Type. No Function key or row callback is rewrapped.
The complete key list is admitted before updating that index. Gerbil's standard
`delete-duplicates/hash` retains first occurrence order; empty lists create no
membership and duplicate keys do not repeat backend updates.

Unique and grouped indexes use the same two-phase delta installer. All old keys
are retracted before any final memberships are inserted, permitting simultaneous
alias swaps and team migration. A collision retains the first projected conflict
key and both primary owners; no staged snapshot or FUN consumer escapes failure.
A fresh retry and inverse reuse the existing style/metadata/origin protocol.
Declaration edits, including cardinality changes, invalidate existing snapshots.
Callback effects are not rolled back. Stable pure finite projections and backend
key equality agreeing with `equal?` remain explicit premises.

`make-tagged-services` combines unique aliases, ordered shared-team buckets,
nested checked Functions, linear ownership/FUN consumption, refusal, repair and
undo. Lean's `indexKeysView` / `reviseIndexKeys` prove membership correlation,
changed-column framing, accepted delta reconstruction, duplicate invariance and
single-key correspondence. `claimIndexKeys` reuses the existing ordered unique
claim rule and proves exact head-failure propagation. These are finite semantic
laws advancing the collection proposal, not extraction or compiler proofs.

Projection counts remain at most two per edit/declaration. Backend work additionally
scales with the number of distinct old and final memberships; standard list
admission/deduplication retains its own cost. This is not constant work per row,
a wall-time claim, automatic query optimization or discovery of callback purity.

## Protected declaration preparation

`table-indexes` captures the finite proper declaration-list spine before any
metadata getter. Existing `with-table-sources` protects the source and every
captured declaration while discovering their backends; it then protects those
backends while collecting child/origin Types. Recipe compilation, duplicate-name
and Value compatibility checks, and initial empty-state construction run inside
the complete nested protection. The private compiler receives the same captured
backend list instead of reading `table` again. No second mutation/invalidation
engine or public namespace is introduced.

This closes a real construction omission: a later computed `project` getter could
rewrite an earlier declaration after its recipe had been captured. Sampling all
revisions only afterwards incorrectly certified the old recipe against the new
revision. Supported peer writes now refuse with the exact existing
`object mutation during computation` error. A changed caller-owned list affects
future requests, never the already captured family. Backend discovery precedes
ordered recipe compilation; original getter errors short-circuit the current
phase. Effects already performed by callbacks are not rolled back.

`examples/service-collection.ss` `publish-indexed-services` composes preparation,
initial wrapping and the existing linear FUN/IO revision action. Tests combine
computed-metadata refusal, unique conflict, explicit fresh retry, shared checked
Functions, inverse restoration and stale-family refusal; additional controls cover
backend/child/source mutation and request-spine replacement. Later supported
metadata revisions continue to invalidate the completed family normally.

Lean's `indexPreparation_frame` reuses `applyChanges_frame` and the existing
`extendProtection` scope laws: every successful finite supported edit outside the
nested scopes preserves all declaration, backend and child/origin observations.
`indexPreparation_current` derives current complete stamps. Faithful scope/source
interpretation and supported edits are premises. Raw setters, concurrent metadata
mutation, hidden callback dependencies, arbitrary initialization hooks and callback
termination/effect rollback are not established by these finite future-work laws.

Local final functional acceptance passed the standard linked single-process suite:
128 modules / 1,270 cases, normal status 0, wall 38.324 s, CPU 21.311 s, GC CPU
3.608 s under the unchanged 1 GiB / 300 s bound. This is a correctness receipt,
not a paired timing claim. The three new cases cover computed peer edits, the
backend/child/source scope, and caller-buffer capture, with full publication and
inverse/refusal controls inside them.


## Complete cache admission

Cold construction and warm revisions share `checked-entry` in the existing
`table/indexes.scm` module. Gerbil's standard `for/collect` prepares declarations
in order; after one backend finishes, `require-table` recognizes its complete
cache before the next recipe starts. It never normalizes or reconstructs the
accepted cache. Shape-only backend updates and uniqueness claims cannot stand
in for this full Type boundary. No new namespace or transaction mechanism is used.

This closes a reproducible omission: a unique cache declared to have even
cardinality previously accepted three owners without invoking its recognizer.
Grouped indexes similarly stored buckets that violated `Value = source` when
the primary Type imposed a whole-root refinement. A valid final primary alone
does not imply that every group bucket is admitted.

Primary conflicts precede cache work. Within each declaration, backend/projection
and uniqueness failure precede final recognition; an earlier recognition failure
suppresses all later recipes. Recognizer exceptions retain their exact cause;
false membership raises the existing TypeError. Supported metadata writes remain
blocked under the complete origin guard. No partial primary or cache family is
published, and styles retain the old owner for explicit retry. An empty delta
still recognizes every completed cache rather than inferring approval from no
changed keys. Arbitrary callback effects are not rolled back.

`make-cohort-services` combines a RationalDict service primary, unique badge map
and UInt Trie team cache. The same source Type requires even membership in the
primary and in each team bucket. A one-service team migration refuses; a single
atomic team exchange plus badge swap succeeds. The existing Wrapper, five
styles and Reader/FUN/IO publisher retain checked callback identities. Regression
controls include both cache backends, failure ordering, bad carrier/owner outputs,
no-op admission, late refusal, retry and inverse restoration.

`TableIndex.lean` models preparation/recognition of genuinely heterogeneous cache
Types. It proves declaration order, complete per-entry admission, unchanged
accepted payloads, exact refusal, complete-family publication and old-owner
retention. `Examples/CollectionStyles.lean` uses opaque callback-bearing cohorts
and different badge/team cache Types. Correlation, persistent backend fidelity,
complete Type recognition and stable projections remain explicit host premises.
These laws advance the collection proposal's future work; they do not prove
arbitrary user recognizers, compiler execution, GC behavior or universal latency.

Each successful recipe performs one top-level complete recognition. Child
recognizers and custom root predicates may enumerate all cached bindings or all
group members, including untouched rows. Cold scans, changed-key maintenance,
cache recognition, conversions and consumer work are distinct costs. No bounded
projection count or unchanged-cache identity is used to omit these checks.
