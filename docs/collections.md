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
