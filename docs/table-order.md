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

## Cost and proof scope

Gerbil's existing `list-sort` supplies sorting; `filter`, `foldl` and `foldr`
supply traversal. This implementation enumerates and sorts each ordered query or
fold. Under the host sort's cost contract, n bindings cost O(n log n) comparisons
plus enumeration, O(n) filter work and result storage; comparator, inverse,
recognition, metadata and backend costs are additional. There is no logarithmic
seek, balanced secondary tree, retained sorted cache or measured speedup claim.
Warm correlated updates still use changed keys; ordered observations do not
change that installer. Source-specific seek and automatic query optimization
remain separate work, not failures of this finite protocol.

`TableOrder.lean` formalizes sign/equality/order laws, their isomorphic transport,
interval membership, payload-preserving range transport, preservation of sorted
input, reversed-bound refusal and extensional recovery. Host sorting correctness
is an explicit premise, not a Lean proof of Gerbil's sorting/runtime. Existing
index/style theorems cover atomic installation and ownership; Scheme regressions
exercise their composition with order, failures, invalidation and inverse retry.
