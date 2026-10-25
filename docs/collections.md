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

### Demand-driven bounded range cursors

`.range<- root lower upper [lower-inclusive? #t] [upper-inclusive? #t]` returns a
standard Gerbil Iterator over the same ordered bindings as `.range`. Lower/upper
are Options: false denotes an unbounded end, while some false can be a real typed
key. Malformed bounds, non-Boolean inclusion flags and reversed bounds refuse
during construction. Both Option shells are captured before child predicates or
comparisons run; logical key immutability remains a caller premise.

`table-order` reuses its declared seek cursor or its existing sort/filter fallback.
Gerbil `in-coroutine` owns suspended traversal and terminal EOF; no new iterator
class or scheduler is introduced. Each demand consumes one backend row until
EOF or the first upper-bound rejection. That boundary row is not returned. Further
EOF observations perform no backend pull, but still check current descriptor and
origin revisions. Comparator exceptions retain their original cause; corrected
retry constructs a fresh cursor over the retained persistent root.

The list-returning `.range` collects this same cursor. All five table/set styles
and Posh/Classy receivers expose `.range<-` through the existing deferred-observe
boundary; Set projects elements with the existing iterator mapper. Creating or
draining a cursor does not consume ownership. Later supported owner publication
does not rewrite its captured root; origin/descriptor invalidation refuses even
after EOF. Nested order views and explicit Wrapper transport reuse positioned
traversal; clients apply table-order to the transported seek capability.

`observe-ledger-range` uses the existing Reader/FUN/IO Observation to hand a
bounded stream to an application inspector. The inspector can stop early;
inspection failure suppresses consume, while already executed callback effects
are not rolled back. Regression controls cover seek/fallback correspondence,
all boundary flags, no-prefetch and sticky EOF pull counts, captured bound shells,
comparator failure/retry, nested origins, all styles/receivers, Function identity
and successful/refused service inspection.

Lean TableOrder reuses the existing finite range-prefix and ordered-window laws.
One demanded-step equation preserves the original prefix observation and exact
payload/tail, terminal observations cost zero backend pulls, rejection reads one
boundary row, and stale revisions refuse before any backend work including EOF.
Top-level service examples exercise bounded output, rejected boundaries and
current/stale terminal observations. Faithful ordered backend windows, metadata
admission, persistent roots and stable pure comparisons are premises, not proofs
of the Gerbil coroutine implementation, compiler or GC.

Design reflection: the absent bounded streaming capability is added to the
existing order protocol; eager range selection no longer has a parallel loop.
Standard coroutine/Iterator and existing guard/mapping abstractions supply the
mechanism. Seek retains its direct one-row observation rather than gaining a
redundant deferred wrapper. Fallback sorting still materializes the complete source;
initial recognition, positioning, metadata checks and boundary comparison are
charged separately. Partial consumption saves subsequent demands, not initial
fallback sorting or admission, and no wall-clock speedup is asserted. This is
finite collection-library future work, not automatic backend/order discovery.

### Deferred named-index observations

Indexed tables now expose `.index-iter<- state name`,
`.index-seek<- state name lower [inclusive? #t]` and
`.index-range<- state name lower upper [lower-inclusive? #t] [upper-inclusive? #t]`.
The first delegates ordinary backend iteration; the latter two require those
explicit ordered capabilities. Names, bounds, order and backend errors are not
guessed or coerced. Existing `.index-fold` is also available through every style
and receiver, alongside point lookup and materialized range observation.

One private with-index continuation now owns name resolution and family admission
for both old and new queries. Deferred results reuse iterator-map and the backend's
Iterator, with no cache copy, second sort or payload normalization. Unique indexes
yield admitted owner keys; grouped indexes yield their persistent source buckets.
The private complete index-cache root is not exposed.

Every delayed pull checks the complete owning family's revisions, including
primary and sibling declarations and inherited delta origins. The selected
backend retains its own order/comparer guard. These scopes are distinct: changing
an unrelated declaration invalidates a family cursor even when the selected
backend is unchanged. Terminal EOF never bypasses either required scope.
Supported publication creates a new immutable snapshot; a previously created
cursor retains the old root. Changing declarations requires fresh construction.

All five table styles and Posh/Classy receivers use the existing deferred-observe
boundary. Observation never consumes ownership. observe-indexed-range is a thin
named-query presentation of the existing bounded Reader/FUN/IO inspector; its
failure suppresses the consumer, with no rollback of prior callback effects.

Regressions compare lazy/eager ordered observations, unique/grouped outputs and
folds, retained Function identity, atomic priority swaps/shared-bucket migration,
inverse recovery, original snapshots, partial/terminal sibling invalidation,
unknown names, unsupported capabilities, foreign states, styles and service IO.
Lean TableOrder reuses ordinary range-pull semantics to establish family/backend
refusal before work, exact current forwarding and terminal zero backend pulls.
Named selection laws retain admission/lookup/backend failure order. Finite service
examples show unique/grouped observations and family-stale/selected-current EOF.
Faithful source stamps, persistent roots, ordered backend laws and pure metadata
callbacks are premises; compiler/GC and arbitrary external mutation are not proved.

Design reflection: this closes named-index traversal through the existing
collection observation chain, not a parallel query engine. Three repeated lookup
blocks were replaced by one continuation; the new cursor helper only delegates
and guards. Full family admission, metadata checks, positioning, fallback sorting
and selected-bucket traversal remain charged. Laziness avoids unrequested pulls;
it does not imply zero preparation cost or a wall-clock speedup. Automatic index
selection and backend/order discovery remain collection-library research work.

### Checked finite collection division

`.divide root` returns two optional nonempty parts; `.divide/list root` returns
the same zero, one or two parts as a list. Empty input returns no carriers.
A singleton returns the original admitted root, with no manufactured empty
remainder. Missing parts use false independently of the backend's empty-root
representation. The protocol requires no key order or comparator.

The shared table boundary admits the original root before invoking a backend.
Trie exposes its existing structural algorithm as `.divide/key`; public calls
now pass through ordinary complete admission. Other tables reuse the existing
partition in visitation order, selecting a ceiling-half prefix. Every complete
part must satisfy the same table refinement, be nonempty and strictly smaller
for a nontrivial input; part counts must sum to the original count. Invalid
structural progress and recognition failures return no part. Count fidelity,
disjointness and lookup-preserving reconstruction remain backend laws, rather
than being inferred from method names or counts alone.

Set division delegates that table boundary and checks its existing Set refinement.
All five styles and Posh/Classy receivers reuse the original multi-result staging
and one generation installation. For nonempty output, mutable/classy retains the
input identity as the first part; additional owners are fresh. Linear retires its
input once, including successful empty division with no successors. Pure/posh
retains the predecessor. Empty mutable division keeps the original empty head.
No part or new capability escapes until the whole request and owner installation
accepts. Refusal preserves the owner for explicit corrected-input retry; external
callback effects are not rolled back.

The service example composes checked Function ledgers with linear division and
Reader/FUN/IO consumption. Regressions cover RationalDict/Trie/boxed carriers,
empty/singleton/multirow inputs, reconstruction, correlated unique/shared indexes,
Function identity, every style/receiver, late branch refinement, corrected retry,
invalid backend progress, original exceptions and suppressed IO on refusal.
Lean's TableSelection reuses finite take/drop and branch admission: exact ordered
reconstruction, uniqueness, strictly smaller nonempty parts, unchanged output
observations, original refusal and zero-result ownership. Top-level service
examples include late second-part refusal and corrected retry.

Design reflection: the old first-element split and raw-empty assumptions were
replaced at the public boundary; no parallel tree algorithm, namespace or owner
installer was added. The existing stage now admits an empty result list with the
same commit rule. Structural backends retain their division strategy; only the
generic path promises ceiling-half sizes. Complete source/part admission, count
queries, partition/index preparation and style construction remain costs.
Strictly decreasing finite sizes justify explicit recursion under faithful backend
laws, not arbitrary callback termination, physical disjoint ownership, automatic
parallelism, compiler/GC correctness or wall-clock speedups. This advances the
proposed collection library's future work without declaring the project complete.

Checked predicate observations now share the finite `TableSelection.queryBindings`
kernel. The Gerbil Table predicate receives key and value; the Set presentation
projects to elements. Public first/last searches and any/every admit the complete
snapshot before short-circuiting, with strict Boolean decisions and original
failure identity. Recognition bypasses public admission to avoid self-recursion.
The incorrect Trie key-only monotonic specialization is removed from this general
interface; explicit seek remains the ordered capability. Existing five-style and
Gerbil receiver paths observe without consuming ownership, and the service example
composes a retained Function lookup with Reader/FUN/IO.

Proofs establish source membership and satisfaction, absence and universal
interpretation, decided-prefix shielding, reverse membership, refusal precedence,
unchanged/consumed ownership and a source-length bound on predicate invocations.
The model assumes faithful persistent backend traversal and stable admitted leaves;
complete recognition, backend/guard/conversion/allocation/GC costs remain charged.
A short predicate prefix does not prove a sublinear total query. No host callback
termination, runtime/compiler correctness or wall-clock claim is made. This is an
explicit future-work extension. Design reflection: reuse one traversal and the
existing admission/ownership boundaries, remove the false optimization premise,
and keep raw recognition separate from public query admission; add no namespace.


Finite Iterable import now reuses the existing table key-space capability and
ordinary final-state delta installer. A private registry captures each admitted
Pair before further pulls and coalesces duplicate keys with last-write precedence.
Seedless import uses the existing bulk constructor on unique final bindings;
seeded import reads only touched old values and installs once, without seed listing
or a snapshot diff. Set maps lazily to Unit entries. Five styles, standard receivers
and `import-ledger-action` share the ordinary ownership and Reader/FUN/IO paths.

`TableBatch` proves ordered last writes, unchanged keys, one-delta reconstruction,
inverse recovery, per-entry failure/cardinality and seed/read/final admission.
Registry enumeration distinctness, coverage and no-extra-key properties are explicit
backend premises; delta cardinality is bounded by touched keys, themselves bounded
by input rows. The existing `TableStyle.styleStep_failure` law supplies failure retention. Service
examples include duplicate supersession, an indexed-priority swap and inverse.
Physical Iterator/EOF behavior, persistence and stable admitted leaves remain
premises. Stream progress and external effects are not rolled back; retry needs a
fresh stream. Complete recognition, key registry construction, backend/index work,
allocation and GC remain charged. Infinite streaming, physical ownership and host
runtime/compiler proofs are not claimed. This is finite collection future work.

Design reflection: one key registry and one existing installer replace pointwise
business-root construction and Set snapshot rebuilding; no new namespace, ownership
engine, duplicate validation layer or implicit equality policy is introduced.


Ordered whole-collection comparison now shares a complete admission boundary
between the existing Trie structural comparison and standard ordered Iterators.
The original union-key convention puts absence before presence; common payloads
use the caller's exact Integer comparator, which may equate distinct Function
handles. Raw unordered tables remain unsupported. Explicit order/representation
views, Set and five nonconsuming styles/receivers delegate the same protocol.
Pair shells are captured before later pulls; no merge root, alternate tree engine
or repeated Function wrapper is introduced. `compare-ledger-action` composes
indexed service snapshots with Reader/FUN/IO; failure suppresses the consumer.

The finite `TableOrder` laws establish reflexivity/reversal under caller comparer
laws, first deciding key/value and original refusal, exact key-bridge transport,
complete left/right admission precedence and a bound of the shorter row count on
paired decisions. Existing `TableObservation` laws cover delegated, stale and
consumed snapshot observation. Sorted/persistent faithful enumeration and the
structural capability's order laws remain premises; no arbitrary callback order
laws, joint atomic read, physical ownership or compiler/runtime correctness is
inferred. Complete recognition, key/value comparison, fallback sorting/positioning,
conversion, allocation and GC remain costs. This advances finite collection
future work. Design reflection: preserve the original comparison meaning and
reuse one boundary, existing algorithms and snapshot readers, without a namespace
or a fabricated empty merge result.

Checked public list/singleton construction now captures the input spine and Pair
shells before child admission, passes every admitted occurrence to the existing
bulk or Trie singleton capability, then recognizes the complete business root.
The old builders remain the implementation: default foldr retains first-write
precedence and Gerbil RBTree retains last-write precedence. Order, representation
and indexed constructors delegate complete roots; no intermediate business-root
refinement is required. Normalization is still explicit and admitted Function
leaves keep identity. Fresh five-style factories reuse ordinary owner creation;
`construct-ledger-action` composes the boundary with Reader/FUN/IO.

The finite `TableBatch` model proves unchanged captured row order/multiplicity,
leaf/backend/final refusal precedence, preservation of any supplied backend
observation law and a bound of source length on row checks. Existing stream and
new default foldr examples distinguish duplicate policies. Physical input capture
and callbacks are Scheme controls; immutable captured rows, stable leaves and
persistent backend laws are premises. Full copying/recognition/construction,
index/owner preparation, allocation and GC remain charged. No arbitrary callback
termination, physical ownership, inferred backend complexity or runtime/compiler
correctness is claimed. This is finite collection future work. Design reflection:
one public boundary reuses raw constructor strategies and owner creation without
normalization, a namespace, cache or another storage/validation engine.


Optional association now delegates the old `.acons/opt` entrypoint to the same
captured point-update boundary. Absence retains the old binding (unlike replacement,
where absence removes); present false and opaque Function handles remain values.
The caller-owned Option shell is copied before any metadata or source recognition.
Trie removes its redundant public zipper-update override and inherits the same
checked delta path, retaining its original persistent insertion/removal algorithms.
All five styles and Gerbil receivers retain generation capture, final refinement/
index admission and failure retry; successful linear no-ops still retire the source.
The integrated service action composes Reader/FUN and IO with inverse recovery.

`TableFocus.associateOption` and `admitAssociation` formalize the modifier without
another installer. Existing point-delta and focus laws prove no-op omission, exact
installation/inverse, changed-key stale refusal, at most one edit, original-cause
refusal and linear retirement. Source/key/final-root admission, stable leaves and
lawful persistent backends are explicit premises. Whole recognition, metadata,
copying, lookup, construction, GC and allocation remain charged; no runtime lock,
callback termination or compiler correctness follows. This is finite collection
future work. Design reflection: remove the unchecked Option branch, share one
modifier, and preserve the established validation and ownership abstractions.


Whole-collection equality now uses one complete-admission boundary before backend
shortcuts. RationalDict's existing standard Iterator/RBTree algorithm and Trie's
shared-subtree algorithm remain private structural capabilities; the generic path
retains two-sided domain checks. Every encountered value decision and backend result
must be Boolean. Five Table styles and standard receivers reuse the existing
nonconsuming Set/Table relation reader. Pure roots remain duplicable; no owner is
invented for them. Source/key/value/origin checks cannot be skipped on identical roots.

The existing `prepareBindingComparison` is generalized over its result type so
Bool observations reuse all left/right refusal and exact-result laws. `equalViewKeys`
proves optional-presence soundness, first false/error short-circuiting, finite lookup
soundness/completeness and full view equality with a covering key sequence. Its
visited-key bound charges neither hidden recognition nor lookup/callback costs as
constant. Stable leaves, lawful persistent backend enumeration and reflexive/sound
payload equality are premises. No joint atomic read of owners, Function extensional
equality, callback rollback/termination, GC or compiler claim is made. The service
Reader/FUN/IO example retains failure retry and exact Function identity after undo.
This is finite collection future work. Design reflection: keep mature backend
algorithms, remove their public validation bypass and lift the existing relation
protocol; add no equality/ownership engine or namespace.
