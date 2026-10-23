# Explicit table order and range queries

This is a concrete extension of the proposed incremental/isomorphism-aware
collection library, not a claim that the original Racket construction already
specifies this API. Existing `methods.table`, typed Wrappers, correlated indexes
and FUN/IO styles remain the implementation boundary. Scheme has no dependency
on the companion Lean checkout.

## Protocol

- `table-comparer Key compare [dependencies]` binds a pure three-way procedure
  returning exactly -1, 0 or 1 to a key Type and metadata revisions. Use existing
  comparers such as `support/base`'s `number-comparer`.
- `table-comparer-wrapper comparer key-wrapper` requires the exact Domain Type
  and transports comparison by the Wrapper's inverse. Both encountered inverse
  laws and child membership are checked by the existing isomorphism validator.
- `table-order source comparer` requires identical key Types. It derives the
  standard table protocol from `methods.table` and delegates persistent carrier
  primitives to `source`. This rebinding matters: copying an instantiated source
  would leave its derived methods bound to the old traversal. Extensions beyond
  the table protocol are not copied; declare ordered index backends explicitly.
- `.seek state lower [inclusive?]` returns the first binding as `(some pair)`,
  or `#f` at EOF. It shares range admission and metadata failure semantics.
- `.range state lower upper [lower-inclusive? upper-inclusive?]` returns ordered
  `(key . value)` bindings. Bounds are `#f` (unbounded) or `(some key)`; `(some #f)`
  is a real bound when false belongs to the key Type. Inclusivity defaults true.
- `.index-range snapshot name lower upper [lower-inclusive? upper-inclusive?]`
  delegates to that declared backend's `.range`, retaining index ownership,
  freshness, unknown-name checks and callback guards. An unordered backend refuses.
  Grouped indexes return original primary-table buckets; unique indexes return
  primary owners. Private cache roots never escape.

Negative external keys can retain increasing *source* priority: transporting
numeric comparison through negation orders -10, -20, -30 in that sequence. Host
numeric order is never guessed. Values, including checked Functions, are merely
reordered with their keys. No row normalization occurs during comparison/query.

## Laws, invalidation and refusal

The explicit comparer must be pure, total and transitive, have reversed signs
when arguments are exchanged, and return zero exactly for equal keys. Backend
key equality must agree with `equal?`, as for existing correlated indexes. Runtime
checks reject non-sign results and encountered zero/equality disagreement; finite
checks cannot establish universal transitivity. A key Wrapper must be a genuine
isomorphism, with all mutable callback dependencies declared.

Malformed or ill-typed bounds refuse before enumeration. Reversed bounds refuse;
equal endpoints with either side open yield an empty interval. Callback exceptions
keep their original cause. Queries never publish partial lists or install state.
External callback effects cannot be rolled back. Supported mutations of active
metadata are guarded; cross-thread metadata revisions must be serialized as in
the existing collection protocol.

Comparer, key Wrapper, key Type and source revisions participate in origins. An
old ordered descriptor or retained indexed snapshot refuses after a dependency
changes. Reconstruct the comparer/view/index family explicitly. No hidden sort
cache can survive a revision. Deltas, multi-index uniqueness, inverse installation
and all pure/mutable/linear transitions retain their existing failure/ownership
semantics. Failed unique publication keeps the old owned capability usable;
repaired retry and inverse recovery restore the corresponding range observations.

## Positioned backends and validation reuse

A backend explicitly advertises `Comparer` and `.seek<- state lower inclusive?`
returning a Gerbil Iterator. Its laws require the exact lower-filtered enumeration
in its declared order, pure shape recognition and persistent, immutable-by-discipline
roots. `table-order` selects it only when Key identities and `.procedure` identities
match its explicit comparer. Constructor-owned weak revision seals also require
unchanged compare/procedure pairs; copied/overridden methods cannot borrow an old
procedure's capability. Equal-looking procedures are not assumed equivalent;
a mismatched comparer uses the reference sort/filter route.

Trie supplies this capability by reusing its standard `.iter<-` traversal. The
lower-bound path skips preceding branches and prefix-disjoint subtrees instead of
constructing a split table. `.range` stops at the first upper-bound failure.
`table-wrapper` transfers the capability through its existing typed key/value and
carrier isomorphisms. Boundary decoding uses the original inverse checks; each
iterator pull, including EOF, holds source guards. Use the derived `Comparer`
explicitly, so an xor-key representation follows source order rather than numeric
external order. Gerbil's public RBTree API in the installed release has no seek;
RationalDict retains the sorting route without reaching into private tree nodes.

For declared positioning backends, the standard weak-key table records successful
shape admission by root identity. Values are booleans and cannot retain the keys.
First admission still validates the whole structure; failed admission is never
cached. Metadata checks precede every cache lookup. Reclaimed cache entries may
require fresh admission. In-place structural mutation violates the persistent
backend premise and is not justified by this cache. Arbitrary backends without
the capability retain their original shape checking behavior. Admission does not
normalize rows or cache Function approvals.

## Cost and proof scope

After successful retained admission, Trie positioning takes a boundary spine and
range traversal visits the returned entries plus one boundary/EOF pull. Under
constant node operations its structural cost is O(h + m), with trie height h and
result size m; sparse large integers do not imply h = log n. First admission remains
O(n). Metadata, typed bounds, bignum operations, Wrapper inverses, source-specific
recognition and representation equality are additional costs. Wide/unbounded
queries still visit all returned rows. The fallback enumerates/sorts each query,
with O(n log n) comparisons under the host sort contract. No universal speedup or
runtime/GC proof is asserted.

`TableOrder.lean` formalizes comparer transport and interval observations, the
lawful backend window partition, equality of early stop with the full filter,
and the loop's exact output-length-plus-one pull count. Its total abstract work
bound explicitly assumes a height-bounded positioning cost certificate. These
laws do not verify Gerbil's coroutine, collector or concrete Trie implementation.
Backend-order, purity, persistence and interval-contiguity laws are explicit
premises; Scheme oracle regressions exercise the concrete implementation.

The existing `collection-paired-benchmark` additionally covers `order-cold`,
`order-seek`, `order-range` and `order-workflow`. Both sides share admitted inputs,
projection, indexes, ownership and inverse recovery. Only explicit capability
selection differs; the reference uses a separate but equivalent comparison
procedure. Cold includes new factories and index preparation. Workflow includes
difference discovery, linear installation, conversion, query and inverse. The
unchanged harness retains AB/BA, A/A, fixed prefix, natural/collected regimes,
wall/CPU/GC/allocation and history records. All original phases remain enabled.
Full observations go to stdout/local temporary logs, not versioned datasets.

## Local paired receipt

macOS arm64, Gerbil `1cfb032`, Gambit `ea114fc`; command
`just benchmark-collections 256 3 6` (256 UInt bindings, narrow four-row window,
three operations per observation, six AB/BA pairs, four A/A controls, prefix two).
All ten study phases completed. Values below are microseconds per operation;
wall columns are side medians, delta columns are medians of *paired* differences
(candidate minus reference). Non-GC CPU subtracts measured GC CPU from each sample.

| Phase | Regime | Reference wall | Positioned wall | Paired wall delta | Non-GC CPU delta | GC CPU delta |
|---|---|---:|---:|---:|---:|---:|
| Cold factory/index | natural | 64929.13 | 63781.70 | -1461.31 | -1137.17 | -287.00 |
| Cold factory/index | collected | 65512.18 | 64333.36 | -1037.48 | -680.83 | -286.67 |
| Seek | natural | 1125.06 | 5.84 | -1119.57 | -915.83 | -200.83 |
| Seek | collected | 1146.83 | 5.88 | -1140.16 | -927.67 | -201.50 |
| Range | natural | 1193.17 | 13.51 | -1179.66 | -933.50 | -230.17 |
| Range | collected | 911.20 | 13.47 | -897.21 | -896.83 | 0.00 |
| Workflow | natural | 8284.49 | 6123.82 | -2160.31 | -1851.83 | -305.33 |
| Workflow | collected | 8221.51 | 5817.49 | -2359.35 | -1860.50 | -454.67 |

Cold construction is **not qualified as a stable speedup**: it retains full shape
and index preparation, and collected A/A deltas span -1764.30 to -362.40 us,
overlapping its AB evidence. An earlier collected cold run had a +2431.00 us
median and a large positive outlier; it remains a local diagnostic, not a rewritten
pass. Source-origin preparation now deduplicates shared descriptors once using
`delete-duplicates/hash`. Collected workflow A/A also has a +5117.26 us outlier;
these finite observations do not establish a universal timing bound.

The independent structural regression uses 2048 bindings and four hits: after
explicit first admission, positioning unwraps 19 nodes versus the reference's
4095. Both return identical bindings; the counter has positive traversal controls.
First admission and failed-admission retry are tested separately. This work count
is not substituted for the wall/CPU/GC measurements above. Full pair/history data
remain in local logs; no generated dataset or archive is committed.
