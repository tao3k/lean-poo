# Persistent table revision semantics

`LeanPoo/Functional/TableRevision.lean` extends the existing
`Functional.OrderedDictionary` namespace with finite optional-binding deltas.
This advances the paper's future collection-library work, reusing dictionary
observation and lens laws rather than claiming a new construction in the paper.

The completed unit includes:

* finite discovery completeness for a unique key inventory covering all differences;
* sequential application and exact first-conflict refusal;
* inverse restoration after successful installation and an untouched-key frame law;
* a total optional-binding lens, including absent keys and stored false;
* a `TableCarrier` refinement: lookup after a backend write must equal optional
  replacement in the existing observation model;
* cross-carrier delta transport retaining successful observations and exact errors.

`Examples/TableRevision.lean` combines deletion, false-valued insertion, conflict
at a later edit, rediscovery/retry, service metadata and composed lens laws.
Gerbil `methods.table` implements the same ordered optimistic operations with its
existing RationalDict and Trie backends. Its `examples/service-collection.ss`
connects proposal admission and installation to Reader/FUN and IO consumption.
Its existing collection regression module includes 48 revisions against an
independent alist oracle and recursive Function-wrapper retention.

The Gerbil discovery order is source updates/deletions followed by target-only
insertions; the Lean inventory abstracts that order. Discovery scans snapshots;
application accesses only changed bindings after carrier admission. Empty deltas
return the original Scheme table. These are source-level operation facts, not
measured speedups or allocator/GC claims.

The backend lookup/write law, descriptor equality, stable admitted values and
pure backend operations are assumptions. Opaque callback handles can model
procedure identity; no extensional equality procedure is derived. Gerbil's actual
tree runtime, collector, compiler, arbitrary callback termination and concurrent
publication are not verified by this model. Scheme has no Lean dependency.

Conflict checking concerns changed keys, allowing unrelated edits to rebase. It
is not global revision fencing and does not reject ABA at equal bindings. Scheme
separately refuses captured descriptor revisions; those runtime guards are tested,
not proved by the abstract delta equations.

## Explicit key/value conversion

The next completed unit reuses `Prototype.DictionaryBridge` for explicit typed
bijections. `transportView`, `transportChange` and `transportChanges` lift those
to observations and ordered deltas. Proofs establish key injectivity, optional
expectation equality reflection, complete view/edit roundtrips, undo commutation,
finite discovery commutation, write commutation and installation commutation on
both success and the exact first mapped conflict key.

Gerbil's existing `Wrapper.` `.ap/.unap` and `methods.table` implement the same
protocol. `table-isomorphism` takes explicit source/target table descriptors and
key/value Wrappers with matching Domain/Codomain. Its `Delta` Wrapper converts
`(admitted-base . delta)` pairs, installing the origin first and converting both
snapshots through one target-backend collision registry. This rejects aliases
across deleted/inserted keys as well as within either snapshot. Edit order and
origin/converter metadata lineage are preserved. Failures expose no partial result;
FUN composition suppresses the IO consumer and allows rediscovery/retry.

Both inverse laws, preservation of admitted values, pure stable callbacks, and
agreement between backend equality and the logical observation model are premises.
Runtime recognition/roundtrip checks are finite controls, not a universal callback
proof. Reordering already admitted Tuple/Pair Function leaves preserves their exact
procedure identities without wrapping again; arbitrary raw callbacks are not made
safe by membership recognition. The Lean service example uses opaque callback
handles, shared services, deletion/insertion, conflicting publication and inverse
recovery. It does not prove Scheme procedure semantics or arbitrary termination.

Conversion includes complete snapshot scans, original delta installation, private
carrier construction, registry lookups and metadata checks; it is not O(edits) in
general. No runtime performance improvement is inferred from these algebraic laws.
Automatically inferred conversions remain future work.

## Delta-driven folds

`foldl_correct` proves a general optional-write law sufficient for arbitrary
accumulators: the complete fold after one write must equal a sparse step using
the actual old optional binding. No group structure is inferred for user code.
The concrete `contribution`/`foldView`/`foldStep`/`foldChanges` construction uses
exact integer contributions; `foldView_replace` derives the write law from a
unique finite inventory containing every updated key. `foldChanges_correct` and
`applyFold_correct` prove sparse/full agreement and unchanged first-conflict
refusal. `foldChanges_inverse` proves accumulator restoration. Full reference
folds, sparse steps and complete source/aggregate installation commute with the
existing explicit key/value bridges (`transport_applyFold`), pulling scores back
through their inverse maps.

`foldWork_bound` counts at most two projections per supplied edit. It excludes
initial scans, shape admission, equality, backend writes, descriptor preparation,
metadata lineage, arithmetic, allocation and GC. The model makes no wall-clock
or general O(delta-count) workflow claim. In particular, isomorphism conversion
still scans both snapshots, and Trie shape admission may scan its structure.

Gerbil `table-fold` uses the existing Wrapper and `.zero/.add/.sub` protocol.
Its opaque state retains the admitted source alongside its aggregate; `.unap`
recovers that source rather than inverting a lossy numeric total. Initial `.ap`
performs full recognition/folding. `.apply-delta` completes old-value/origin
checks before any aggregate callback, then returns the privately staged source
and sparse aggregate together. `.get` and `.unap` enforce owner and metadata
freshness, including converted delta origins retained through empty/inverse
updates. FUN composition suppresses the consumer on failure and permits retry.
Pointwise count/weighted-sum examples retain shared checked Function handles.
The regression compares 24 rounds on each RationalDict/Trie carrier with an
independent sum and forbids accidental fold enumeration during sparse updates.

The proof premises include stable admitted values, pure successful operations,
backend refinement and the optional-write law. Exact integer sums are proved;
product metrics satisfy the law coordinatewise. Arbitrary floating-point or
order-sensitive folds are not covered by the retractable law merely because
methods exist. Runtime type checks and metadata guards are tested controls,
not universal proofs of arbitrary Scheme callbacks, external effects, concurrency
or termination. The examples remain in top-level Examples/TableRevision.lean.


## Aggregate reuse and scoped invalidation

The next unit derives a target fold from the source fold and explicit inverse
maps. Gerbil retains one private source/target-state pair and a live key-ownership
registry. Hits reuse state identity without conversion; warm source deltas update
only mapped bindings and adopt the source aggregate rather than initializing or
updating a second aggregate. Paired inverse recovery returns the source state;
nonpaired valid targets use full inverse conversion and key reconstruction.

`writeChanges` abstracts private persistent replay after all source conflicts pass.
`applyChanges_writeChanges` justifies that replay; `transport_writeChanges`
preserves the cached correspondence. `reuseFold_correct` proves equality with the
complete existing target fold execution, including mapped first conflicts.
`retained_fold_inverse` uses the existing inverse law. `fold_dependency_frame`
instantiates the existing table frame theorem for metadata stamps, while
`fold_dependency_changed` rejects a changed captured stamp. The example separates
source/aggregate scope from converter scope: converter changes invalidate derived
representations without discarding a still-current original source aggregate.
Incoming origins remain captured, including through inverse fallback. Independently
fresh states with the exact same immutable root can rebind the cached representation
and use the new source aggregate/origins; neither stale input is thereby made fresh.
`rebind_fold_view` states the observation-equivalence premise for that reuse.

`reuseFoldWork_bound` counts at most two source projections per edit, zero target
projections and no full target snapshot replay on the paired path. Cold conversion,
source carrier admission, metadata and lineage checks, inverse-law controls,
backend registry/write costs, allocation and GC remain outside that count. Runtime
identity and complete failure/cache publication behavior are tested controls,
not pointer-level or compiler proofs. Stable admitted leaves, pure callbacks,
explicit bijection/fold laws and carrier refinement remain premises.

Gerbil's capacity example composes the existing optional lenses and FUN consumer
with checked shared callbacks, two representations and inverse recovery. The
regression refuses accidental warm scans and covers chained metadata invalidation,
unrelated converter edits, stale origins, collision refusal and retry. Its Scheme
paired study compares full and reused paths, with matched setup, AB/BA and A/A
controls, natural/collected GC, fresh factories, hot hits, revision/undo, complete
discovery workflows and failed-attempt/retry phases. No performance or correctness
claim for the compiler, runtime or arbitrary user callbacks is inferred from these
algebraic proofs or finite measurements.

The companion local compiled-module study (64 bindings, 10 operations, six AB/BA
and four A/A pairs per phase/GC regime) observed complete-workflow median wall
differences of -16.907/-15.943 ms (natural/collected) and CPU differences of
-4.573/-4.597 ms per operation. Cold natural wall time regressed +5.211 ms and
A/A controls were noisy; neither universal speedup nor reduced GC cost is claimed.
The Scheme document retains all phase summaries and the unsuccessful 90-second
static-link attempt separately from successful module compilation/execution.


## Shared preparation and benchmark linkage

`stampMatches_append`, `stampMatches_dedup` and `prepareStamped_fuse` justify
preparing the union of finite metadata scopes once on a stable revision snapshot,
with the same success/refusal result. Gerbil shares its typed direction preparation
between ordinary isomorphisms and fold derivation, eliminating two unused private
Wrappers, a duplicate forward direction and an unused revision capture. Existing
source/derived fold guards and inverse/collision controls remain authoritative.
The proof does not cover runtime allocation, GC, locking or compiler behavior.

The Scheme study separately measures factory preparation and complete cold
materialization. Its compiled module runs in the existing statically linked test
program through Gerbil's loader, avoiding a second copy of the shared C link closure.
Shared-binary preparation retains its original 300-second stage bound; workload
compilation retains 90 seconds. The 123-module test inventory and one-process
execution remain intact. These source/build changes need paired measurements;
the earlier noisy +5.211 ms cold median is not itself evidence of a GC cause.

The linked program runs directly with Gerbil's official home from activation or
compiler discovery. This removes an extra tools VM without inventing a load path.
A harness OK followed by timeout remains a failed acceptance, not a completed run.

The linked-runtime paired run completed 240 observations. Factory CPU medians
were -0.028/-0.005 ms and cold CPU medians -0.338/-0.397 ms (natural/collected).
Cold wall medians were -0.870/+0.085 ms with larger A/A noise, so cold wall-time
improvement remains unproved. Module compilation completed within 90 seconds
(41.30 s first, 26.21 s unchanged repeat); the repeat did no compile or link jobs.
Shared-binary preparation still cost 192.89 s under its original 300-second stage.
Full Scheme acceptance passed 123 modules and naturally exited 0; earlier
harness-OK/timeouts remain failures. All phase summaries and limits are recorded
in the Scheme document, separate from the finite metadata-fusion theorem.


## Constant-time protection scope reuse

`extendProtection` models the selected guard list: an empty outer scope retains
the incoming list, exact sharing retains the active list, and partial overlap
keeps the original append. A true sharing flag must imply equal scope contents.
`mem_extendProtection` proves the same protected dependency set under that premise;
`stampMatches_extendProtection` preserves both metadata acceptance and refusal.
`extendProtection_length_le` bounds list entries, not heap allocation or GC time.
All descriptor instantiation checks, recursive-construction refusal, metadata
revision checks and callback mutation guards remain in the Gerbil implementation.

A general membership-filtering version was measured and rejected: reduced list
duplication added hot-call and retry costs. The admitted implementation uses only
constant-time identity/empty checks. Examples include shared scopes, empty outer
scopes, retained partial overlaps and rejection of a newly changed origin.

The build change uses Gerbil's existing `defbuild-script` with the existing
`clan/poo/t` prefix and t/ source directory for benchmark consumers. The complete
library check still precedes public study preparation. Standard make owns input
and dependency freshness; no custom cache or load path is added. Timing and GC
observations belong to the Scheme study, not these finite semantic theorems.

## Faithful metadata across consumer scopes

`stampMatches_transport` and `prepareStamped_transport` permit relabeling a finite
dependency scope only when captured and current stamps agree at every source
label and corresponding interface label. Acceptance and refusal are both preserved.
`prepareStamped_stale_producer` proves that an outdated producer refuses before
consumer admission, even when the consumer's own interface view agrees with itself.
The executable example covers all three dependencies and an obsolete producer.

This models the obligation behind reusing checked interfaces. It does not prove
Gerbil make, compiler correctness, filesystem timestamps, linker behavior or GC.
The complete producer check, standard consumer dependency check, linked runtime
root checks and live test inventory admission all remain operational prerequisites.

## Grouped module metadata

`bindingDependencies` models the repeated module label attached to individual
imported bindings. `mem_bindingDependencies`, `stampMatches_grouped` and
`prepareStamped_grouped` preserve complete dependency membership and both
acceptance/refusal when every group is positive and its single module stamp
represents the original dependency. Empty groups cannot discharge a dependency.
`bindingDependencies_length` gives the exact sum of binding counts;
`groupedDependencies_length_le` bounds grouped inspections by that sum.
These are finite metadata/work laws under one stable snapshot, not a verification
of Gerbil expansion, compiler freshness, allocation, GC or wall-clock speed.

The worked example retains a facade with 1,453 bindings, refuses a stale facade,
and demonstrates why an empty group would incorrectly omit a stale stamp.
The Gerbil regression separately verifies that the runner still imports the
complete official expander facade and resolves the same public harness entry.

`prepareStamped_regroup` also covers a retained complete module stamp together
with selected aliases, when both positive representations have the same labels.
`bindingDependencies_count_le` composes an explicit per-module inspection budget.
The examples instantiate metadata/dispatch facades with 82 original versus ten
retained records and the same stale-facade refusal. The Gerbil source/loader audit
checks 73 modules' public interface, ordered module coverage and initialization
code, while executable regression checks selected alias identity and whole-facade
freshness. These controls do not upgrade the finite laws into compiler or GC
correctness proofs. Wall-time and allocation results, including rejected candidates
and unresolved variance, are recorded separately in the companion study.

## Hygienic preparation and allocation-free stamp comparison

The Scheme construction macro now uses Gerbil compiler/base's
`make-bound-identifier-table`, retaining the standard full
`bound-identifier=?` predicate. A name hash selects comparison candidates; it
never makes distinct lexical scopes equal. Existing slot normalization lives in
`support/object-syntax`, rather than adding a module or a second syntax engine.
`retainIndexedSlotIdentifiers_eq` in `Functional/SlotScope.lean` establishes
first-occurrence sequence equality for a consistent discriminator and complete
identifier equality. `matchingSlotIdentifiers_length_le` bounds candidate lists;
physical hash collisions and table resizing remain host implementation premises.

The runtime candidate replacing mapped revision snapshots with length-guarded
standard `andmap` was rejected: the paired full workflow did not establish a
speedup. Existing mapped guards remain installed. New public-reader regression
controls still reject truncated, extended and malformed captured version records.
An unguarded standard `andmap` stops at the shorter input and would be unsafe.

The accepted entry change uses standard `just` dependencies to retain the same
library, executable, workload-module and workload checks, eliminating three
nested `just` invocations. `checkedEntryCost_shared` proves a launch-cost bound
with identical ordered stage costs as an explicit premise.
`runEntryChecks_append` also preserves the ordered effectful actions and their
first failure when removing grouping boundaries in a lawful monad. It does not infer
that premise from host build scripts or prove a GC or wall-clock guarantee. The
companion Scheme document retains measured paired results and adverse controls.

## Captured optional point updates

The Scheme `.delta/opt key update before` operation captures a single optional
replacement for later installation without constructing a trial carrier or scanning
for differences. It shares existing delta origins, ordered composition, transport,
folds, inverse and style installation. Typed admission and callback failure precede
delta publication; applying the result does not replay the capture callback. Option
shells are privately copied while admitted leaves retain identity. Empty requests
retain origins and are not assertions against later changes to the written key.

`TableBatch.pointChanges` is the finite model in the existing ordered-dictionary
namespace. It equals single-key discovery and proves exact installation, rebasing
on an aligned key, stale-key refusal, complete inverse recovery, one-edit bound,
callback failure and key/value-isomorphism commutation. Existing batch/index/style
laws apply unchanged. Scheme tests additionally cover mutable public Option shells,
Function identity, no trial writes or difference scans, multi-key index refusal,
retry and FUN consumption. The model assumes stable payload observations and lawful
persistent carriers; it does not verify the host runtime or mutation of shared
leaves. Admission, metadata, recognition, callback and backend costs are outside
the emitted-edit bound; no end-to-end asymptotic or wall-clock claim follows.

### Complete fold publication boundary

Source and warm-target fold updates now recognize their complete final root;
compatible child Types or paired bindings alone do not establish root refinements.
Aggregate reuse still avoids target reinitialization/reprojection, but complete
recognition may scan both snapshots. `reuseFoldWork` explicitly charges supplied
source and target admission visits. See [table-fold.md](table-fold.md) for atomic
batch semantics, retained-pair failure/retry, service composition and proof scope.


## Selective grouped folds

`foldGroups` summarizes each nonempty finite owner bucket, preserving the distinction
between an absent group and a present zero aggregate. The generic summary function
may observe ordered bucket contents; an inverse/commutative law is not assumed.
`grouped_bucket_frame` derives unchanged buckets from coverage of original/final
group memberships of changed rows. `repairGroupFolds_correct` then proves selective
refolding agrees with full regrouping. `foldGroups_delta` proves that a direct
ordinary delta over the touched groups reconstructs the complete summary, and
`foldGroups_inverse` restores summaries from the explicit source inverse.

These laws correspond to Gerbil `table-group-fold`, which reuses existing grouped
indexes and a fold kernel shared with ordinary `table-fold`. Whole source admission
precedes projection; complete target recognition precedes direct delivery and the
existing style publisher. Top-level `Examples/ServiceCollection.lean` covers
zero-sum shared teams, migration, unrelated group reuse, last-owner removal and
inverse recovery. The stable finite owner inventory/reference traversal, lawful
persistent backends, repeatable pure callbacks and faithful recognizers remain
premises. Host costs include all rows of affected buckets, index preparation,
validation and public installation; no machine speedup, GC, compiler correctness,
automatic retraction law or destructive rollback is proved. This advances the
collection proposal's future work rather than claiming automatic library synthesis.

### Finite multivalued grouped aggregation

`table-group-fold` accepts `multiple?: #t`: classify returns a finite proper
list of typed cohort keys. Default classification still returns one key, even when
that key is itself a list. Duplicate memberships contribute once; empty membership
retains the primary row without contributing to any group. A live zero summary
remains present, and deleting its last owner removes the group.

The implementation extends the existing grouped index, fold kernel, owned cache,
exact target delta and five-style publication chain. A shared private admission
function captures the classifier list spine, checks its keys without normalizing
Function leaves, and uses standard stable deduplication. It replaces the duplicated
index checks rather than wrapping each operation. Classifiers, logical keys and
contributions must remain stable and pure; capturing a spine does not freeze keys.

Warm repair refolds only old/final affected groups. Every surviving row in each
affected bucket is charged; finite classification, spine copying, key recognition,
index preparation, whole-root recognition and style installation remain costs.
There is no constant-time, GC or wall-clock speedup claim. Invalid membership,
stale origins, final refinement refusal or callback failure exposes no successor;
the old persistent cache remains available for corrected explicit retry. Inverting
the delivered target delta restores observations, not information discarded by an
aggregate.

The service example combines duplicate cohorts, checked Function capacities,
migration and untouched-group reuse. Regressions cover Trie/RationalDict oracles,
all five styles, inverse recovery, malformed membership, callback-owned list
mutation, refinement retry, origin invalidation and list-valued single keys.
Lean proves the old/final membership frame, selective repair, exact target delta
and duplicate-membership invariance; finite service examples include zero-valued
live groups and inverse recovery. These laws assume faithful equality/recognizers,
finite owner inventories and persistent backend laws. This advances the collection
proposal's future work and does not prove host callbacks, GC or compiler behavior.

Design review: no second grouping algorithm, cache representation, installer or
namespace was added. The explicit multiplicity flag follows the existing index
and projection interface. The necessary list ownership copy is visible in the cost
boundary; further automatic dependency/algebra discovery remains research work.

### Multivalued grouped joins

`table-group-join` accepts `multiple?: #t` for both classifiers. Each returns a
finite proper list of admitted group keys. Default classifiers still return one
group key, including a list-valued key. A pair exists exactly when both rows are
present and share at least one group; empty memberships contribute no pairs.
Repeated tags or several shared groups never multiply its projection.

Both existing grouped indexes own membership admission and invalidation. Cold
multivalued construction uses the existing pair-key backend to coalesce witnesses
before projection; ordinary single-group construction skips that registry work.
Warm repair reuses the old/final edited-endpoint inventory and pair registry.
Finding a match in one bucket is not undone by absence in a later bucket. The
same projection cache still owns target-key collisions, exact delivered deltas,
callback identity and all five styles of atomic publication.
Delivery retains the existing old-owner retraction followed by final insertion;
an exact replayable delta is not promised to be a minimal edit list.

`make-service-placement-join` exposes the same option. The integrated example
places checked service Functions onto workers with overlapping cohort lists,
migrates both sides, retains surviving associations and publishes through FUN/IO.
Independent Cartesian oracles cover Trie/RationalDict, mixed insertion/deletion,
empty memberships, duplicate tags and inverse recovery. Other regressions cover
malformed lists, stale expectations before projection, downstream collision,
explicit corrected retry, origins and ordinary list-valued keys.

Costs include complete source/index recognition, finite membership admission and
spine ownership, every encountered matching bucket, logical pair deduplication,
projection and target installation. Shared groups can repeat bucket visits even
though they do not repeat a user projection; dense relations can produce a
Cartesian number of pairs. No sublinear backend, wall-clock or GC bound is claimed.
Classifiers, keys and callbacks must be stable/pure, logical group and pair
equality must agree with their backends, and roots must be persistent. Callback
effects before refusal are not rolled back.

Lean's existing TableProjection namespace now shares a row-local relation model
and frame/inverse laws between ordinary equality joins and finite-membership joins.
It proves duplicate-witness invariance, singleton correspondence, preservation of
any shared cohort and full-refresh equivalence under the complete old/final
affected-pair inventory premise. Existing reservation/delivery/publication laws
remain the collision and failure boundary; host recognizers, mutable leaves and
compiler/GC correctness are not proved.

Design reflection: no new public engine, cache state, namespace or publication
wrapper was added. The finite multiplicity option follows the existing index and
projection interfaces; membership validation is shared rather than stacked on
individual operations. This closes an explicit association-composition unit of
the proposed collection library's future work, not automatic relation discovery.

### Incremental value-table combination

`(table-combination Left Right Target choose [origins])` maintains a key-preserving
merge of two persistent tables. All three Key descriptors must be identical and
their backend logical equalities coherent; Value descriptors may differ.
`choose key left-option right-option` returns an admitted target Option, without
normalizing Function leaves. Both absent bypasses choose and removes the result.
Stored false is present. Resolution must be stable and key-local; external callback
dependencies belong in explicit origins.

Cold preparation admits both roots, enumerates their union through the target's
key registry and resolves each logical key once. Warm revision installs both
guarded source deltas before resolving any key, coalesces their touched keys,
and skips target writes when the selected optional value is unchanged. Source
conflict, malformed response, target refinement or arbitrary resolver failure
exposes no successor and does not call the consumer. The original persistent cache
remains available for corrected explicit retry. Effects inside callbacks are not
rolled back. No target snapshot scan or .diff is used to deliver the exact delta.

The implementation generalizes the existing set-combination engine rather than
adding another installer. Set/Elt refinements and invalidation retain their own
admission boundary; Unit-valued algebra now uses the same private state, key
registry, conflict checks and update loop. Wrapper, view composition and the
existing binary FUN/IO publisher preserve all five ownership styles. The service
override example merges checked default Functions with enabled typed override
records, then publishes their exact retained Function identities. Another example
feeds merged values directly into grouped aggregation.

Regressions cover heterogeneous values, all styles, independent full-merge
oracles on Trie/RationalDict, simultaneous edits, deletion of the final owner,
zero/no-op writes, stale source conflicts, malformed Options, original exception
identity, refinement refusal/retry, origin invalidation and inverse recovery.
Lean's TableProjection laws reuse the existing selective repair and delta
operators: union-domain absence, two-source frame, complete sparse repair, exact
target delta, coalesced inventories and source inverse recovery. SetAlgebra proves
that the shared resolver specializes exactly to all four Unit-valued operations. Faithful
recognizers/equality, finite inventories, pure callbacks and persistent backend
laws remain premises; compiler/GC and arbitrary mutation are not proved.

Design reflection: this is the missing value-carrying counterpart of snapshot
.merge and incremental Set algebra. One shared engine replaces the Set-specific
copy; there is no new namespace, per-operation wrapper stack or compatibility
path. Cold union enumeration, complete admission, metadata preparation and target
installation remain costs. Warm resolver count is bounded by distinct edited
keys, but complete backend/admission work is still charged; no wall-clock speedup
or generally sublinear workflow is asserted. Automatic resolver/dependency
discovery remains research work within the proposed collection library.
