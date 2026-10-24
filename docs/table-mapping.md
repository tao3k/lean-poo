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

## Explicit heterogeneous entry projection

`(.call source .map/into target project input)` accepts one target Pair per
original binding. `filter-map/into` accepts the existing Option protocol: `#f`
drops a row, while `(some (cons key #f))` retains a false target value. A present
non-Pair is a TypeError; a malformed Option retains the existing table refusal.
Both keys and values may change Type. No inverse or Any fallback is inferred.

The common entry boundary protects both descriptors and their declared origins,
admits the original source, then obtains the target's existing typed `.key-table`
capability. Missing/incompatible capability refuses before any project callback,
even on an empty input. Each original row is visited once in backend order. The
callback-owned Option/Pair shells are copied before child recognition; admitted
Function leaves stay identical. The target registry checks its own lookup equality
rather than host hashing/equal?. The first duplicate raises the existing
`table-index-conflict` with name `primary` and both source owners, before later
callbacks or target construction. A late callback failure retains its exact cause.

Only the complete row list reaches one target `.<-list` call, followed by whole
recognition. Business refinements, represented carriers and correlated indexes
therefore see the final target, without requiring an admitted empty or singleton
prefix. Cache uniqueness failures keep their existing index names. No partial
target is returned and IO is suppressed on any refusal. External callback effects
and mutations inside shared payload leaves are not rolled back.

All five source styles and the receiver methods expose the same projection as a
nonconsuming snapshot observation. The result is a raw target root; use the
existing target style `.ap` to choose its presentation. A cross-type result never
replaces a source owner. Reentrant source publications remain visible; observing
an earlier captured snapshot does not assert freshness for a later publication.
`map-ledger-into-action` composes the source FUN protocol with Reader/IO. The
worked service flow reorders Pair/Function fields into Tuple rows, changes the key
Type, builds unique badge/endpoint and shared-team indexes, retries after genuine
constraint refusal, and uses ordinary target deltas for revision/inverse recovery.
An inverse of those target edits is not an inverse of the general projection.

Lean `mapEntries` uses target logical key classes and standard Except/Sum/List
sequencing. It proves first callback/collision refusal, no duplicate published
keys, avoidance of prior keys, the output-length bound and correspondence with
the existing ordered `mapBindings` traversal, without equality on payloads.
`prepareEntryMap` proves source/projection/whole-target failure order and exact,
faithfully admitted publication. Existing `observeStyle` laws supply stale and
consumed-source refusal for the different target type. The backend registry must
implement these logical key classes; traversal, bulk construction, callback
termination, faithful recognizers and stable leaves remain premises. This does
not verify the Gerbil compiler, arbitrary predicate implication or wall time.

For n source bindings and m retained rows, a successful projection invokes n
callbacks and performs m target-registry lookups and insertions. It allocates a
finite row list and constructs the target once. Source/result recognition, child
checks, registry preparation, target/index construction, comparisons, converters,
allocation and GC are additional charged costs; no O(edits) or speedup is claimed.

## Incremental heterogeneous projection

Gerbil `table-projection` reuses the existing Wrapper, source/target typed key
registries and ordered deltas. `.ap` initializes; `.unap`/`.get` observe admitted
source/target roots; `.apply-delta` returns an immutable successor. Source delta
conflicts and complete source admission precede callbacks. First-touch source-key
coalescing projects only final present rows; cached rows of deleted keys are
retracted without calling the callback. All affected old owners are released before
new reservations, permitting final swaps. New/untouched collisions still refuse.
One ordinary target delta retains complete correlated index and root admission.
Failure returns no new state and the predecessor is available for fresh retry.

`LeanPoo/Functional/TableProjection.lean` supplies these finite laws in the existing
OrderedDictionary namespace:

* `refreshEntryCache_observe`, `_frame`, `_complete`: successful selective refresh
  agrees with a full stable key-local projection at every source key, retaining
  exact cached opaque Function leaves outside the touched inventory.
* `projection_changes_covered`: existing successful ordered changes provide the
  required untouched-source frame. First-touch deduplication uses backend logical
  equality; callbacks respect that equivalence.
* `reserveProjection_unique`: cached untouched owners plus newly reserved rows
  have no duplicate target keys, using existing `mapEntries` uniqueness/avoidance.
* `prepareProjectionRevision_*`: source, projection and final target refusal order;
  complete exact source/cache/target publication after all phases succeed.
* `publishProjection_*`: immutable predecessor on failure, complete successor on
  success. External effects/GC/thread scheduling are outside this law.
* `projectionCalls_bound`: final-present callback demands are bounded by touched
  key count, not by total snapshot size. Recognition/backend work is separate.

`Examples/CollectionStyles.lean` adds Function-bearing key swaps, shared untouched
callbacks, collision refusal and deletion without a demanded callback. Scheme
regressions compose repeated-key batches, 32-round full-oracle comparison across
RationalDict/Trie, primary and unique-index refusal, metadata lineage, retries,
shared-team migration and FUN/IO with target Linear style recovery.

Stable pure key-local callbacks, stable admitted leaves, faithful backend equality,
registry/traversal laws, complete recognizers and persistent atomic target installers
are premises. Explicit callback origins invalidate all stale states; undeclared
mutable dependencies cannot be made incremental automatically. There is no inferred
inverse projection, arbitrary Function equality, global publication freshness,
physical ownership or compiler/runtime verification. Source/target full admission,
registry preparation, index operations, comparisons, allocation and GC remain
charged; callback selectivity is not an end-to-end O(edits) or wall-time claim.

## Direct target-delta delivery and style publication

The optional `receive` argument of Gerbil projection `.apply-delta` receives the
admitted successor and the EXACT target delta used by private installation.
Standard `values` returns both; default use returns only the state. No previous
state/history slot, full `.diff` scan or new delta representation is introduced.
`publish-projected-ledger-action` reuses Reader/FUN/IO and the existing target style
installer before returning state/target/delta. Failures before public installation
suppress that publication and IO; postcommit IO is not rolled back.

`TableProjection.lean` now contains:

* `deliverProjection_*`: exact state/delta handoff, default state-only and pair
  correspondence, preparation suppression and unchanged receiver refusal.
* `publishProjectionDelivery_*`: existing style ownership on success, target
  conflict/admission failure retaining the predecessor, and consumed refusal.
* Changed-key conflict, target inverse and untouched-frame laws reused directly
  from `TableRevision`; generation rejection reused from `TableStyle`.

The canonical projection cache and public target are distinct observations under
changed-key rebase: public unrelated rows remain, including during inverse recovery.
The delivered inverse restores the actual public predecessor when its recognition
succeeds. It does not invert arbitrary projection callbacks or authenticate a
one-shot publication ticket. Opaque Function-bearing cache handoff needs no
payload equality; target replay's old-value relation, carrier fidelity and complete
recognizers remain premises. Empty deltas retain origins and may be replayable.

The top-level collection examples cover opaque Function state, changed public
expectations and explicit target inverse recovery. Scheme controls cover five
styles, source/target refusal, public-only constraints, new-key occupation,
reentrant winners, stale empty origins, receiver exceptions and retry. The service
workflow swaps primary keys and unique badge/endpoint indexes, migrates shared
memberships, preserves checked Functions and uses the delivered inverse. Its
`.diff` is deliberately unavailable; another control rejects difference traversal
and checks identity of installed and delivered deltas.

Private preparation and public style installation still charge their own complete
validation/backend/index work. The source-level removal of difference discovery
is not a proof of compiler/runtime behavior, concurrency, allocation, GC or wall
speedup. All existing check inventories and resource bounds are retained.


## Two-source lookup maintenance

The finite `lookupJoinView` retains each left row and its exact optional right
observation. `lookupJoin_frame` derives unchanged enriched rows from left/right
source frames and coverage of left edits plus original/final right-reference
buckets. `lookupJoin_repair` proves selective repair agrees with full enrichment;
`lookupJoin_refresh` reuses the existing complete projection-cache theorem rather
than introducing another reservation/collision algorithm. Explicit inverses of
both source deltas restore the joined observations. Ordered paired admission
retains left-before-right failure causes and exposes no pair on refusal.

These laws correspond to Gerbil `table-lookup-join`, which composes grouped indexes,
a private typed Pair/Sum carrier and existing table-projection delivery with the
same five-style Reader/FUN/IO publisher. Top-level `Examples/ServiceCollection.lean`
covers shared false policies, absent policies, selective revision and inverse
controls. The host regressions retain typed Function identity, output key swaps,
source/target refusal, independent snapshot branches and corrected retry.
Logical key equality, stable pure callbacks, persistent backends, complete source
frames and sound affected inventories remain premises. Full preparation,
validation, bucket enumeration and public installation are charged separately;
there is no GC/compiler proof, machine speedup claim, automatic query discovery,
many-to-many expansion or public two-source-owner transaction claim. This advances
the collection proposal's future work with explicit finite lookup construction.


## Finite grouped many-to-many expansion

The Scheme `table-group-join` protocol composes two existing grouped indexes with
the existing entry projection and Reader/FUN/IO delivery chain. Explicit group-key
and Pair-key backends define equality. Old/final buckets for edited endpoints
cover finite insertion, deletion and migration without reprojecting unrelated
groups. Complete source admission precedes classifiers; existing output claims
reject collisions and preserve immutable retry. Source inverses and delivered
target inverses are separate recovery operations. Five-style public installation
does not consume two independently owned public sources atomically or roll back
callback/postcommit effects.

`groupJoinView`, `groupJoinAffected_covers`, `groupJoinAffected_frame`,
`groupJoin_refresh` and `groupJoin_inverse` establish the logical observation,
finite-inventory coverage, unchanged-pair frame, selective/full-cache equivalence
and checked inverse recovery. `groupJoinAffected_bound` bounds only the finite
filtered pair inventory. The existing projection claim/refusal/delivery laws are
reused. No equality on opaque Function payloads is needed for the frame/cache
laws; inverse source delta laws retain their explicit payload-equality premise.

Premises are stable pure callbacks, faithful group/componentwise pair equality,
complete old/final matching buckets and persistent atomic installers. Preparation
includes two indexes, matched-pair expansion, metadata and full recognition. Warm
cost includes source/index installs, bucket traversal and coalescing, affected
projection and private/public target installation. Large matched groups can have
quadratic output; neither callback counts nor finite laws prove GC or wall-clock
performance or verify the Gerbil compiler/runtime. Top-level
`Examples/ServiceCollection.lean` covers shared groups, double migration, untouched
observations, finite affected inventories and inverse recovery.
