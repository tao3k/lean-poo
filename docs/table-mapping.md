# Checked bulk binding maps

This closes a concrete collection TODO: `.map/2` was listed but absent from
`methods.table`, while Trie exposed only its carrier-specific traversal. The new
standard include `table/mapping.scm` stays inside `clan/poo/table`. This advances
the collection proposal's future work, reusing existing folds, writes, Option,
metadata guards, FUN/IO and declared Trie mapping, without a new tree or namespace.

## One key-preserving protocol

* `.map/2 transform input` calls `transform key value` once per ORIGINAL binding
  and retains that key with the returned admitted Value. False is a stored false
  when the Value descriptor accepts it.
* `.filter-map/2 transform input` accepts only `#f` (remove) or `(some value)`
  (retain/replace). `(some #f)` differs from removal. Invalid Option shells and
  incompatible values refuse with the existing Option/type failure conventions.
* Input and complete output are recognized without normalization. Original keys
  and retained Function leaves keep exact identities; new Function payloads must
  be admitted explicitly before being returned. There is no Any fallback.
* The callback order is the existing backend fold order. Traversal always uses
  the captured original root, never partially updated rows or reentrant additions.
  Required mapping preserves the domain; optional mapping can only shrink it.
* Whole-table refinements may refuse a well-typed result, including an empty one.
  Callback and recognition failure exposes no partial root; external effects are
  observable and are not rolled back. Supported edits to declared table/Type
  origins are blocked throughout traversal and admission.

Both methods are available through all five `table-styles` protocols and through
Gerbil receiver `map/2` / `filter-map/2`. They reuse one original `step`, so all
results and postconditions finish before a single head comparison/installation.
Pure/posh retain the predecessor, mutable/classy retain identity, and linear retires
it once, even for an identity mapping. Foreign/consumed owners and stale metadata
refuse under the same guards. A reentrant winner remains visible; an older mapped
snapshot cannot overwrite it. FUN `.map` still transforms one whole root: it is
not renamed or overloaded with a binding callback. On `set-styles`, these explicit
binding APIs operate on its backing Unit-valued map; they do not remap elements.

`map-ledger-action` composes optional mapping under a local linear owner with the
existing Reader/FUN map. Only a completely admitted result reaches IO. Failure
suppresses the consumer; retry uses the caller's unchanged persistent base. The
result remains an ordinary table, so existing delta discovery, inverse recovery,
indexes and representation wrappers need no separate mapping data format.

## Backend reuse and costs

A declared `.map/key/opt` capability uses the existing specialized traversal,
with checked callback outputs. Trie already supplies this left-to-right routine.
Otherwise the shared algorithm visits the original snapshot, captures only changed
optional bindings with the standard list builder, and installs one ordinary delta.
Correlated indexes therefore retract all old owners before inserting the final
ones: valid unique-value swaps do not fail on an intermediate point update.
Representation Wrappers conjugate visible key/value callbacks through their
existing conversions and delegate one source bulk operation, preserving this
final-state discipline. Both paths retain the
original root by identity when every result compares equal under the existing
`.update/opt` `equal?` convention. A specialized backend may nevertheless allocate
temporary nodes before detecting that no-op: identity is not zero allocation.

For n original bindings, the callback runs n times on success; the generic path
emits at most n primary changes, exactly one per changed optional binding. The
ordinary primary backend performs one write per accepted change; index retraction,
insertion and projection preparation, conversions and their equality checks are
additional costs, not included in that primary-write bound.
Full initial/final recognition and per-payload recognition remain charged. A
specialized backend rebuild has its own node/allocation cost; no changed-write or
host wall-time bound is claimed for it. Unexpected user/backend exceptions retain
their original cause. Pure lawful persistent backend operations, stable leaves,
correct declared traversal and terminating callbacks are explicit premises.

## Verification

Regression controls compare RationalDict and Trie against an independent 16-mask
oracle; check original callback order, no-op identity, both required and optional
semantics, all five styles, receiver calls, unchanged FUN mapping, late refusal,
refinement failure, foreign/stale owners and reentrant publication. Reused Option
shells cannot rewrite prior outputs; opaque Function keys and values stay exact.
Unique swaps and genuine collision/refusal are tested through both direct indexed
carriers and key-negating representations across all five styles, with synchronized
unique and grouped observations. An instrumented generic backend verifies zero
primary writes for no-op, one for one update
or deletion, and no callback on an empty input. Reader/IO retry and inverse delta
recovery complete the workflow. Full checking and resource bounds are unchanged.

`TableMapping.lean` proves stable pure filterMap/map agreement, identity for opaque
payloads, output length bound, no new keys, callback and whole-root failure before
installation, consumed/linear no-op behavior and stale-winner rejection. A conditional representation-transfer law aligns source and visible callback
results. Generic
changed-primary-write accounting is bounded by one decision per visited original binding.
These are finite semantic and conditional work laws, not compiler, allocation or
GC proofs. The service examples combine shared callbacks, capacity reservation,
row removal, late failure, explicit retry and a required-service postcondition.
