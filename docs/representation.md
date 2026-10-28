# Persistent prototype maps and guarded slot layouts

This implements the representation protocol acceptance target from TODO.md. The
Racket paper's “Different instance representation” uses balanced maps and delayed
sharing; “Same instance representation, different prototype representation” makes
explicit slot specifications compatible with the same final-self semantics.
Shape sharing, vector offsets and inline sites advance the implementation ideas
in the original representation TODO; they are not a new claim of a complete MOP.

## Protocol and public operations

`prototype-map.ss` uses private compact vectors and V19 `std/struct/rbtree`, not a second tree implementation.
It stores ordered contributions and a first-name index. Persistent updates copy
balanced-tree paths, preserve later same-name methods and append new names. Input
and reflection list spines/entry pairs are owned; values and SlotSpecs are shared.
`prototype-map-remove` removes all direct contributions for a name, rebuilding the
order tree. There is no logarithmic removal or deep-value immutability claim.

The actual `object.ss` constructor, defaults, setters, `.putslot!`, `.putdefault!`
and `.cc` use these snapshots. `.cc` shares unaffected tree paths and rebinds
formulas to the new receiver; it does not retain an evaluated parent instance.
`.removeslot!` and `.removedefault!` expose inherited contributions again.

`slot-layout.ss` weakly interns a sorted unique symbolic shape. Symbol identities,
including uninterned names, determine its process-local order. No serial number
is a disk format or cross-process identity. Each live shape shares its name/index
mapping; each receiver owns its vector cells. Ordinary lookup retains the existing
hash interface. The vector is prepared only by an explicit `object-layout` or
`.ref/inline` access, and successful ordinary reads keep it coherent. This is an
opt-in representation protocol, not a claim that every hash instance was replaced.

A caller creates `make-slot-cache 'total`, then uses `.ref/inline receiver site`.
The site retains one owner, revision, layout and certified index, never a separate
cached result. Every hit requires exact owner/revision/layout identity. Equal
shapes on distinct receivers cannot share cells. Supported parent, protocol,
declaration, slot, default, topology and instance edits invalidate existing values,
compiled methods, ordering, reflection AND layout through the same registered
reverse-dependency closure. A diamond advances each affected owner once. Failed
preflight changes neither snapshots nor guards. Missing slots/errors never install
a successful index; present false remains a real value. An ABA value/shape change
still rejects the previous generation. Removal of a method does not erase an
explicit instance assignment; these are separate existing protocols.

## Integrated acceptance

`t/representation-test.ss` exercises persistent snapshots, duplicate method order,
uninterned symbols, live shape sharing, receiver switching, shared-parent diamonds,
computed values, insert/delete/default/topology changes, failed edits, cycles and
retry. `examples/representation-service.ss` composes checked ObjectContract/refine
with existing Reader/FUN bind and a reusable total access site. Every invocation
still validates the candidate; a layout hit does not substitute for admission.

Lean `Prototype/Representation.lean` proves first-write/frame/removal laws, current
index observations, owner/revision/layout rejection, present-false behavior and
connects stale-revision rejection to existing finite graph invalidation. Executable
controls live in top-level `Examples/Representation.lean`.

The proofs model source-level behavior. They do not verify the RBTree library,
weak table, collector, compiler or physical vector implementation. Token identity
must denote a fixed shape and receiver-local cells. All dependencies must be
registered; supported edits/evaluation are serialized. Raw generated struct setters,
raw instance-hash mutations and unregistered callback dependencies bypass the
protocol. No host process termination, concurrent atomicity, retained-function
revocation or speed/allocation improvement is claimed.

## Remaining optimization ideas

This closes the mapping/layout/invalidation protocol, not every speculative
performance idea in the historical TODO. Patricia trees,
frequency sorting, automatic JIT/PIC selection, full hash removal and compiler
constant-folding qualification remain unimplemented. Matched complete-workflow
benchmarks are required before claiming any strategy is faster.

## Compact persistent prototype maps

The concrete small-map item in the representation TODO is now implemented through
`prototype-map.ss`, without another public namespace or object API. The default policy remains `tree`. Explicit
`prototype-map entries policy: 'compact` selects private vectors through eight
**contributions**, including duplicates. Existing snapshots preserve their policy;
explicit `tree`/`compact` conversion owns a new snapshot with identical entries.
`prototype-map-policy` reports the selected policy, not the current physical backend. A first-name
identity scan selects replacement; appending the ninth contribution promotes to
Gerbil's existing RBTree representation. Removing all contributions for a name
can demote the remaining ordered entries only under the selected compact policy. Missing removal retains the snapshot.
The vector, entry pairs and mutable tree handles never escape; list observations
return fresh spines/pairs, while values and SlotSpecs remain intentionally shared.
This is source-level persistence, not deep immutability of arbitrary values.

The limit bounds a compact scan at eight identity comparisons and a compact
write's resulting row at nine cells, including promotion. Standard vector copying,
`std/vector/vector` filtering and `std/struct/rbtree` perform the storage work.
Promotion still pays tree construction; tree removal still rebuilds in order.
There is no logarithmic removal, universal speedup or allocator/GC cost theorem.

`representation-test.ss` compares 96 mixed revisions and every retained snapshot
with an independent ordered-list oracle. Boundary, duplicate-name, index-zero,
present-false, uninterned-symbol and failed-preflight controls cover both stores.
`expanded-service` crosses the bound through actual persistent object construction;
contraction, overrides, subsequent source edits, checked FUN observation, policy
refusal and retry keep the existing source invalidation/contract protocol.

Lean's existing `Prototype.Representation` namespace proves complete ordered
observations, first-write/frame laws, representation and policy selection/preservation, bounded compact
search/copy and arbitrary finite revision-trace equivalence. Its tree observation
assumes faithful standard-library iteration; distinct Scheme symbol identities
must map to distinct model keys. It does not verify RBTree balancing, vector
primitives, the collector or compiler. Existing revision/layout theorems still
supply cache rejection; changing map storage grants no new cache authority.

`object-scale-benchmark` now records CPU, wall, GC CPU, collection count and raw
allocation deltas via the existing shared Scheme sampler. Both natural and
pre-collected regimes retain the complete cold construction/read, clone-only and
clone/read workflows. Widths 1/4/8/9/16 supplement the original 8/64/256 cases;
all original depths remain. The final executable accepts `natural|collected` and `tree|compact`, exercising
both current policies through the same public map constructor and standard build.
The added cold construction/clone/read phase includes the first promotion inside
its measured workload. Balanced ABBA process order retains all widths/depths. Raw observations stay outside
Git, and GC/history differences must not be reported as selector-only speedups.

## Explicit policy after a rejected default experiment

The first automatic compact candidate was rejected as a default: two ABBA samples
per GC regime showed eight-contribution clone-only CPU increasing by 61.1% under
natural GC and 90.9% after collection, aggregating the three retained depths.
Tree reconstruction at persistent promotion is real work; lower aggregate wall
observations did not certify this path. The latest design defaults to standard
trees and exposes compact storage as a deliberate constructor policy. Writes,
promotion, removal/demotion and conversion preserve that choice. Core `using`
rejects unknown policies before construction; the standard `length<=n?` bounds
compact admission without scanning a large input just to choose the backend.

Lean now carries that policy in tree snapshots, proves selection/observation
identity and write/removal/whole-trace policy preservation, and proves that a
default tree write remains a tree even for small rows. A compact scan bound is
not a total allocation bound: promotion still pays the standard tree builder.
This implements the concrete selectable representation protocol. Automatic
JIT/PIC selection and a universal speedup remain unimplemented qualification work.

## Cross-receiver shape offsets and current cells

`Prototype.Representation.reuseIndex` separates an immutable shape/name offset
from `read`'s existing owner/revision/layout value guard. `readPrepared` reads only
the CURRENT view at that offset; an uncomputed cell or mismatched shape retains
the ordinary lazy fallback and its original refusal. False and opaque Functions
remain exact values. `resolutionWork` explicitly counts named-map resolutions,
not guards, object/layout preparation, tracking, evaluator work, allocation or GC.
Shape pointer fidelity, current receiver-local cells after serialized supported
invalidation, stable leaves and complete dependency declarations are premises.
The original stale-owner/revision/token rejection theorems remain unchanged.

Scheme uses the existing slot layout and inline entry, without another namespace
or result cache. Tracked reads delegate directly to ordinary `.ref` before vector preparation, preserving bootstrap/read-record delivery,
including transitive dependencies and stale replay refusal. Checked service
FUN/IO still performs contract/refine admission on every invocation. Standard
cached module loading preserves recipe identity; fresh clone/layout preparation
does not force unrelated business bodies. Parent PROTOTYPE definitions are
revised through `.putslot!`; parent instance assignments are not inherited values.

The complete existing collection study adds preparation, cold evaluation,
monomorphic/switching access, tracked reads, shared-parent revision and cached
module-load consumer phases. Monomorphic/switching references preserve the prior
untracked inline algorithm; other phases compare ordinary symbolic reads.
AB/BA, A/A, B/B, natural/collected histories and first/post-GC/full-entry work remain
charged. Cold layout costs cannot be inferred away from an offset-resolution law.

This does NOT complete full-vector instance storage, automatic PIC/JIT selection,
fresh module expansion/compile/link/initialization performance or the Gerbil
loader/evaluator implementation. The loader retains its standard registry,
loading synchronization and error/reload semantics. No host runtime, collector,
compiler or universal wall-time improvement is proved by these finite laws.

The first paired study found real extra cost for the vector route under active
read observation. The final `selectRead` policy therefore delegates such accesses
to existing `.ref` before preparing a layout. Three selection laws preserve both
branches and exact refusal. A concrete regression keeps the receiver layout absent
after an observed read. The untracked reference retains the original observation-
status check; omitting that check would make its hot-read comparison unfair.

### Cold hook selection and prepared-layout reuse

`selectLayoutRead` separates ordinary observation/cold pinned-hook reads from a
live prepared layout and genuinely cold field preparation. Its route and exact
refusal laws keep both unchosen actions lazy; a cold anchor can retain its opaque
Function even when unrelated metadata preparation refuses. A non-anchor cannot
borrow this bypass. Top-level executable examples include refusal and retry.
The Gerbil bridge assumes that supported invalidation clears the instance and
layout together, as implemented by `clear-object-cache!`; raw setters bypass that
protocol. Existing value-guard/current-cell proofs still apply on the ready path.
No callback termination, compiler, loader or physical timing theorem is implied.

### Explicit downstream startup and complete consumer traces

The same exported Gerbil service workflow can run through ordinary module
loading or the standard `exe:` build graph. It uses existing ObjectContract
refinement and Reader/FUN composition, with an explicit symbolic/indexed access
choice captured once when the action is created. The one-shot default is symbolic;
it creates no access-site/vector preparation and still retains ordinary lazy
value caches. Live recipe revisions use explicit inherited children; `.cc` source
copies are snapshots and do not imply a live source dependency.

`demandRead_sound` and `demandBatch_sound` lift the existing `readPrepared` laws
to an arbitrary finite ordered batch, including empty input and the first exact
refusal. Faithful current cells/evaluation after supported invalidation are
premises. Different shapes and uncomputed cells retain ordinary evaluation.
Executable top-level examples cover initial observations, refusal and new-view
retry. These are source-result laws; they neither prove Gerbil module initialization
or host process equivalence nor turn operation counts into startup timing bounds.
The actual module and linked executable must execute the same source lifecycle
and retain all process-cold/wall/GC controls separately.

### Demand-filled receiver cells

The source model now distinguishes ordinary cached values from the promoted
subset in a receiver layout. `deferCells` keeps the exact owner/generation/shape
and has no promoted fields. `readPrepared_deferred` preserves any ordinary value
or original refusal. `rememberCell` denotes writing the certified current index
of a unique canonical name after a successful read; its identity/frame/fidelity
laws do not assume Value equality. The opaque Function and present-false examples
therefore need neither revalidation nor reconstruction. The ordinary evaluator
may independently populate dependency cells; the promotion frame theorem does
not claim evaluation is effect-free or rolls back those successful dependencies.

`demandBatch_deferred` lifts this to whole finite batches and exact first-refusal
semantics. Registered supported invalidation and faithful current cells remain
premises. `seedingLookups` counts only initial VALUE-table probes: eager seeding
uses one per canonical name, while deferred creation uses zero. Shape inventory,
sorting/interning, dense vector allocation/fill, demand reads, possible repeated
writes, guards and GC stay charged. This is neither constant-time construction
nor full removal of per-receiver hash storage. Dynamic module initialization and
compiler behavior are still outside these source laws.

## Certified reuse during static-layout construction

Gerbil's existing access site may supply its previous layout as a construction
hint. The shape stores its canonical ordered names beside its standard identity
hash index. After standard identity-based duplicate removal, equal cardinality
and membership of EVERY current name certify reuse. Reordered/duplicate names
are harmless; different uninterned symbols, additions and removals take the
original sort/weak-intern path. The hint never supplies old cells. Eager seeding
still reads only the current ordinary instance; demand-filled construction keeps
its private sentinel. Owner/revision/layout guards and ordinary evaluation remain
unchanged. Supported invalidation discards the receiver layout as before.

The existing Representation model proves full field-set preservation from the
actual cardinality/membership check (assuming identity-faithful distinct current
names), current owner/revision/token/field preservation, certified-index presence,
whole-cache fidelity and composition with the existing value/refusal access law.
The source cost law counts skipped canonical-sort entries only. Name inventory,
deduplication, membership checks, vector allocation, seeding, callbacks, GC and
module loading remain separate costs; no compiler or loader proof is claimed.

This follows the author source's representation/cache distinction in
`poof.scrbl` (prototype metadata and cache invalidation sections). Standard Gerbil
`load-module` already owns module initialization and failure caching. Reusing an
initialized module's recipe does not mean sharing evaluated receiver values.
Scheme has no dependency on this checkout, and adds no module registry or loader.

## Standard runtime entries with a shared foundation

The runtime-entry client is `io.module-action module binding`. It captures a
private copy of the module path and an explicit canonical runtime identifier,
without loading the requested business module. The returned Reader-compatible IO
action accepts the original argument row, delegates to standard `load-module`,
resolves the CURRENT binding with standard `eval`, and tail-applies it. It adds no
registry, path search, export-alias inference or retained procedure. Standard
initialization/error memoization and explicit reload remain authoritative;
business failures are invocation results, and multiple values remain intact.

The existing example executable now links the common POO/FUN/IO foundation and
dynamically selects the SAME compiled business module/binding as the independently
built dynamic-entry reference. The official `gerbil test` harness owns the paired
study; neither reference launches generated interpreter expressions.
It does not link every optional business module. The core's initialization still
runs at process bootstrap; only repeated entry-time discovery and dynamic loading
of already linked dependencies are avoided. Build/link/startup and optional
module initialization remain charged. This advances the author's shared/lazy
representation and staged-computation ideas, rather than proving the Gerbil standard loader.

Representation's entry-stage laws preserve load/lookup failure order, original
causes, original arguments and current binding results. A ghost observation of
published standard-loader readiness distinguishes initialization errors from
business failures. Finite declared common dependencies count bootstrap and entry
initializers separately and preserve the total initialization count. Counts denote
logical source operations, not OS file probes, image maps, linking, GC or latency.
Faithful registration, canonical binding identity and supported finite dependency
initialization remain assumptions. The model does not prove arbitrary initializer
effects, module cycles, compiler behavior or concurrent loader implementation.

## Bounded descriptor offset history

The source cache now offers explicit capacity one or two in the existing
`slot-layout` module. The default single-shape record is unchanged; the opt-in
record retains one extra immutable shape/index pair, never a foreign receiver's
cells. Gerbil's standard records and existing name hashes remain the mechanisms.
A general LRU would add hashed lookup and linked-node maintenance to this small
identity-guard path. The author's efficient implementation Caching subsection
(`poof` source 9affa8f, lines 1140–1148) describes precisely this finite option.

`Offset` and `Offsets` in `Prototype.Representation` certify each field/index and
prove two-descriptor warming, current-view false/Function delivery, lazy refusal,
missing-index clearing and failure-preserved publication. Model strings identify
symbols injectively, including uninterned symbols; pointer identity must imply
immutable canonical-shape equality. The existing receiver/revision/layout guard
and supported finite invalidation discipline remain premises. No receiver value,
module initialization state or validation approval is granted by a shape hit.

After two successful indexed reads, either descriptor avoids named resolution;
an unknown third descriptor retains one named lookup. The model proves this
layout name-to-index probe bound relative to a primary-only site, not a CPU/GC or total-time
improvement. Scheme's complete paired study includes record preparation, warmed
switching, three-shape churn and dynamic-module checked service revisions, using
AB/BA and A/A/B/B across natural/collected histories. Allocation, comparisons,
construction, seeding, refinement, binding and module costs remain charged.
Automatic PIC/JIT selection, vector-only storage and arbitrary cold-module
initialization are separate boundaries; none is declared complete here.

## Indexed persistent contribution deletion

Gerbil's existing prototype map now delegates indexed contribution removal to
`std/struct/rbtree` instead of filtering and rebuilding the entire map. Private
name entries retain the first replacement ordinal and every duplicate ordinal.
Deletion leaves gaps; an independent monotone next ordinal prevents reinsertion
from overwriting unrelated survivors. Live count controls compact demotion.
Existing invalidation, shared inheritance and FUN/contract boundaries still own
publication and refusal.

`Prototype.RepresentationIndex` uses the existing Representation namespace and
finite ordered payloads. Under `IndexMatches`, deletion by ordinals is equal to
the original name filter, removes all same-name methods and preserves remaining
indices. `PositionsBelow` survives removal and advances on append, proving fresh
insertion after gaps. Remembering positions preserves the first method ordinal
and grows the logical position count by one per contribution. Scheme stores a
singleton ordinal directly and allocates position spines only for duplicates.
False and opaque
Function payloads require no equality oracle. Symbol identities are injective
String keys, not display spelling.

For a present name with k contributions, delegated work is k ordered removals,
one name lookup and one name removal; bounded compact demotion is separate.
The cost theorem requires a permutation of the canonical matching index: semantic
membership alone would allow unused extra ordinals. Duplicate insertion preserves
that permutation while keeping the first replacement ordinal.
The model does not verify RBTree balancing, sharing, allocator, compiler or wall
time. Index construction, extra retained/temporary cons cells, ordinal bit costs,
snapshot export, refinement, invalidation and GC remain real costs. Scheme's
complete paired hot/cold/reinsert/publication controls include current construction
and snapshot observation, comparing current supported strategies rather than
claiming previous-revision constructor equivalence.

## Structural names ownership and selective metadata repair

`Prototype.RepresentationNames` extends the existing Representation namespace.
It models private canonical names, separately exposed mutable name links and
existing registered read identity. Symbol identities use injective String keys;
printed spelling is not an identity oracle. Authentication recurses over the
finite private sequence, proving at most length + 1 logical link inspections even
for cyclic or improper presentations. The registered issuer, faithful standard
list copying and serialized supported edits are premises.

The laws preserve unissued-before-stale refusal and the exact consumer outcome,
including false, opaque Functions or business errors. Metadata repair changes
only the live names-record identity: canonical names, preparation parents,
current value view and existing static access remain unchanged. Restoring old
contents cannot revive a replaced identity. These are local frame laws, not an
automatic rewrite of dependent cached graphs; Gerbil rejects those old graphs
and requires its existing explicit flush before recomputation.

Public export uses standard List.map and owns no authority. Replacing its view
leaves private names and value reads unchanged. Logical name-copy cells equal
fields * (public queries + new names records). Internal borrowed enumeration
adds no public copy, while issuance still pays its snapshot copy. Record closures,
canonical construction, result pairs, GC and wall time are excluded from this
source count and remain charged by the paired Gerbil study. No runtime allocator,
compiler, general mutable-heap isolation or pervasive invalidation is verified.

The author source's purity-by-default caching and explicit flushing discussion
(`poof.scrbl`, lines 1533–1553) motivates this finite protocol. The Scheme service
example combines shared inheritance, owned reflection, false/Function identity,
live revisions, refinement, exact evidence and module-action/FUN/IO publication.
The model does not claim original Racket API equivalence or whole-paper closure.

## Super-independent SlotSpec construction

The original TODO explicitly proposes treating methods which ignore super
specially, including lossy/K-style composition. The existing SlotSpec constructors
already supply the required distinction: constant, thunk and self ignore super;
computed remains opaque. The engine previously interpreted every contribution
into an effective thunk before a later explicit override discarded that thunk.
It now keeps a private most-specific-first stack in its existing temporary slot
hash, resetting that stack at those three explicit constructors. Defaults are
ordinary constant specifications. No body analysis, new cache or compiler is added.

Every incoming specification is still admitted in chronological source order.
A malformed earlier specification cannot be hidden by a later valid override.
All retained fields are compiled before invoking ANY compute-slot hook, preserving
payload capture time across fields. Final-self binding, computed super order,
lazy missing-super refusal, false/Function identity, original body exceptions and
failure retry continue through the original evaluator and object/cache engine.

`Prototype.SlotSpec` extends its existing four-constructor model rather than
introducing another interpretation. General compile/fold equivalence, reset-suffix,
original validation error order, final-self and opaque-computed laws accompany
finite retained-length and preparation-work bounds. The preparation counter
charges source visits and retained reversal cells; interpretation and hash
iteration are separate. Effective builder requests exclude reused thunk
procedures. No actual Scheme closure bytes, hash
complexity, allocator, GC, runtime or compiler correctness is proved. Defaults,
declaration preparation, prototype traversal, contracts, result observation and
hooks remain real costs, including in the complete paired workflow.

The Gerbil example reuses the existing shared-service reflection/refinement/FUN
workflow with additional contributions, rather than copying its publication
pipeline. The paired reference encodes the same super-independent body as opaque
computed; the candidate uses explicit self. Both use the CURRENT engine and
charge fresh metadata in cold operations. This comparison qualifies explicit
representation choices, not a before/after revision speedup. Single-contribution,
64-prefix, warmed-cache and complete module/revision/refusal/retry phases retain
AB/BA and A/A/B/B controls with natural, collected and inclusive post-GC samples.

The local current-encoding study retains a real negative control: single-field
collected pairs have +0.75 microseconds median and +8.26 mean (range -4.23 to
+47.04). With 64 overwritten contributions, cold collected pairs have -5.38
median / -4.71 mean, but one adverse tail reaches +2.73. Complete workflow
collected pairs all improve (-53.99 to -13.68; mean -30.96), as do post-GC
batch pairs (-60.19 to -6.30; mean -33.56). The separate CHARGED inclusive
workflow includes forced GC and first invocation: mean -18.13, median -33.76,
range -95.59 to +138.06, four wins and two losses. Natural workflow differences are
heavily affected by GC; no stable 769-microsecond gain is inferred. Same-side
noise remains visible, and these current representations do not establish
previous-revision constructor costs, faster arbitrary module startup or universal
policy superiority. See the Scheme receipt for complete scope.

These laws concern one slot's normalized chronological sequence. Faithful Symbol
identity grouping by the existing standard hash and the unchanged declaration
preparation/capture order remain host premises, checked by integrated regressions;
the model does not verify the standard hash implementation itself.

## Ordered prototype traversal and composition sharing

The author's different-representation construction (`poof.scrbl`, lines 980–1031)
separates equivalent record observations from representation choice and warns
against recomputing whole dictionaries instead of sharing them. The TODO's
persistent-map sharing item also applies to POO's own preparation: it previously
exported owned lists/pairs merely to traverse internal direct specifications, and
`.+` exported then rebuilt both direct maps. These operations did not need a new
snapshot or a new receiver's already computed values.

The existing prototype-map module now supplies ordered callbacks and an owned
name projection over its SAME standard vector/RBTree iterator. Internal assembly
uses one consumer for normalized declaration maps and direct maps, preserving their
concatenation order and admission semantics without direct-map export. Public
reflection still owns its spines/pairs and shares only names/payload identities.
Composition shares immutable direct slots/defaults, preserving their explicit
policy, while the normal constructor owns fresh receiver caches and registered
parent/protocol/descriptor dependencies. Instance assignments remain separate;
only prototype specification revisions propagate as inherited definitions.

`RepresentationIndex` proves ordered traversal/public-snapshot equivalence for
arbitrary state/error consumers, concatenation order and exact first refusal.
Name projection preserves duplicates and identities. Composition retains direct
contribution observations and policies while starting with an empty logical
cache. Persistent successors leave the retained source map unchanged. Finite
export-cell counts exclude iterator state, callbacks, tree construction, C3,
refinement, metadata, GC and machine time. Faithful standard iteration, persistent
maps and serialized supported edits remain host premises; no standard tree,
mutable heap, module loader or compiler verification is asserted.

Five integrated regressions cover declaration re-elaboration, compact/promoted/sparse roots, duplicate and
same-spelling uninterned names, false/Function identity, callback refusal,
mutation of public key snapshots, persistent successor isolation, fresh composed
caches and supported shared-parent revision. The existing reflection/FUN pipeline
is shared by the composed service example rather than duplicated. Paired current
strategies charge complete observations; full workflows also charge templates,
warming, refinement, source revisions, business refusal and retry. This advances
implementation future work, not whole-paper or arbitrary cold-loading closure.

The final current-strategy study measures the full width-64 composition plus
observation at -75.59 microseconds collected median, but retains a +2,249.73 wall
tail. A higher-resolution complete workflow (32 calls/batch, twelve cross-side
pairs) has -70.33 collected mean with eleven wins/one loss; the adverse tail is
+2.24. CHARGED forced-GC/first-call/full-batch mean is -103.27, with ten wins/two
losses and a +174.30 tail. Forced GC CPU contributes +10.12 mean microseconds,
so no universal GC or tail acceleration is claimed. These safe current APIs do
not prove a previous-revision or arbitrary cold-module-loading speedup. The Scheme
receipt preserves the initial inconclusive probe, same-side controls and separate
batch/inclusive costs; raw samples are not committed.

### Declaration catalog ownership

Declaration membership now uses the existing persistent prototype map, alongside
direct slots/defaults. Constructor input and reflected catalog entry pairs are
owned snapshots; public edits cannot change the retained membership, layout names
or descriptor identity. `.+`/`.cc` share immutable catalog roots and retain fresh
receiver caches. Descriptor objects stay live registered sources: supported edits
invalidate owners and re-elaborate current visibility/value constraints.

The constructor rejects malformed finite symbolic catalogs before hooks; capture
does not evaluate descriptors. Private descriptor preparation propagates its exact
refusal and publishes no partially successful state; a corrected retry starts with
fresh scratch. `RepresentationIndex` proves these logical capture, public-view
frame and preparation laws. Physical pair non-aliasing, faithful standard storage,
registered-source propagation and serialized edits remain host premises. Empty
roots retain explicit policy; persistent successors cannot mutate them. Logical
export savings exclude initial capture, descriptor/tree construction, dependency
registration, receiver preparation, hooks, GC and machine time.

Integrated Gerbil controls cover input/output tampering, clone sharing, descriptor
visibility/value invalidation, grammar-before-hook refusal, corrected retry and
full standard module/refine/FUN-bind publication. Both safe current strategies
are measured in a matched benchmark including fresh construction and full workflow,
with same-side controls and charged GC/first-call costs. This advances the author's
future work without asserting arbitrary module loading or whole-paper closure.

The macOS catalog study uses base Gerbil commit `81732d5` and current safe
recapture/reuse strategies (64 fields, sixteen calls/batch, six AB/BA pairs,
four A/A and B/B pairs). The command passed in 43.22 seconds; inclusive study
was 35.40 seconds. Collected cold catalog median was -80.60 microseconds with
six wins and no losses. Full publication remained mixed: collected median
-97.62, range -479.76 / +443.06; charged collection/first/batch median -106.99,
range -322.08 / +201.41 with five wins/one loss. Natural workflow had only one
win/five losses despite its negative mean, and large same-side differences;
this does not establish consistent end-to-end tail or GC acceleration. The
Scheme receipt retains all phases, controls, component means and adverse tails.
Negative allocation counters are unavailable data, not measured byte savings.
The new proof laws concern ordered capture, source frames, refusal/retry and
logical exported cells, not those timings or a collector/compiler theorem.

Gerbil local acceptance completed with 149 modules / 1,859 cases (192.54 s),
then the complete paired collection entry (11.55 s), whole command 204.52 s.
The original per-phase deadlines and heap bounds remain unchanged. Focused Lean
module/examples also passed at 1 GiB/two threads; the full repository gate and
remote CI remain distinct evidence from those focused checks.

### Effective declaration index and observed membership

This advances the author's purity-by-default / explicit-flush future work. The
Gerbil receiver now owns a lazy effective catalog and separately prepared visibility
map, using the existing compact/RBTree prototype map. Source invalidation clears
this optional field with methods, layouts and reads; fresh clones retain no index.
First C3 declarations win before visibility, so a hidden override cannot expose a
public ancestor. Public reflection owns its pairs; descriptor objects remain live
registered sources. Hidden-inclusive inspection does not demand visibility flags.

Observed requests authenticate owner membership through the existing names issuer
and retain ordered hidden-field deliveries. This deliberately adds the structural
owner obligation missing from descriptor-only reflection. Supported source edits
during metadata callbacks refuse the old query before publication; original getter
refusals retain precedence, and a corrected retry starts with current sources.
Unobserved warm point queries reuse metadata only: concrete value/Slot admission
still runs on every invocation, and refused writes retain the prior source state.

`RepresentationDeclarations` proves first-entry selection, seen-name exclusion,
right-to-left first refusal, observed cache bypass, explicit cache-fidelity
refinement, empty-success distinction, revision fencing/retry and logical work
counts. Existing owner-names evidence proves old-revision rejection. Finite private
storage, standard indexed lookup, source registration and serialized supported edits
remain premises; no heap-alias, RBTree balance, GC, compiler or machine-time theorem
is claimed. Initial merge/capture/map construction, the additional optional object
field, concrete value checks and public copies remain paid costs, measured in the
matched cold/hot/observed and complete standard module/FUN/refinement workflow.

The matched macOS index study (base Gerbil `6701463`, width 32, sixteen calls,
six AB/BA pairs plus four A/A and B/B controls) passed in 79.81 seconds; its
inclusive study was 67.27 seconds. Collected point/hot median was -9.06 us,
missing -9.82 us, observed -5.77 us, and full workflow -7,972.91 us with six
wins/no losses. Cold collected wall was +351.31 us while CPU median was -24.59;
the adverse wall result and large same-side tails do not qualify stable cold
improvement. Charged GC/first/batch workflow had median -5,197.92, five wins/
one loss and range -12,211.25 / +4,013.90. Natural workflow also retained a
+7,098.32 tail. The Scheme receipt includes all phase ranges, controls, component
means and unavailable allocation counters. These current-strategy measurements
are separate from finite proof laws and do not establish universal latency,
physical allocation savings or an arbitrary cold-module-loading speedup.

Final Gerbil acceptance retained all 150 modules / 1,866 cases, with module phase
245.29 s, complete paired collection entry 19.73 s and whole command 265.64 s.
The original per-phase 300-second/1 GiB limits remain. Seven new regressions
passed independently, and module/example proofs passed at 1 GiB/two threads.
These full-entry numbers are admission evidence, not a paired old/new compiler
or whole-check latency claim. Full Lean gate and remote CI are separate evidence.

### Cold-query root and policy-view reuse

`prototype-map-merge-first` reuses a sole distinct immutable catalog; multiple
roots/duplicates keep ordered first selection. Large policy-only views retain
standard backend trees and sparse ordinal history, while small backend changes
still capture entries. Visibility filtering shares an all-pass root and rebuilds
partial results with the same policy. No cache flag, registry or namespace is
added. The existing post-callback revision fence still runs before publication.

`RepresentationDeclarations` proves unique first-selection identity, successful
visibility sublists, equal-retained-length identity and observation-preserving
filtered roots for arbitrary payloads (including Functions). Logical builder and
policy-entry-copy counts exclude uniqueness/visibility scans, callbacks, snapshots,
new wrapper records, initialization, value admission, GC and machine time. Runtime
regressions exercise sparse policy conversion, immutable successors, reverse
callback/failure order, hidden overrides and source edits during all-pass reuse.

The macOS full study passed in 75.41 s (inclusive 63.58 s). Isolated directory
and full visibility collected medians improved by 21.87 / 15.84 us; mixed
visibility was +0.16 us. Short cold batches still had +56.66 us collected median
and a +1,483.87 tail. Additional 32-call/twelve-pair cold/full confirmation passed
in 50.93 s (inclusive 45.84 s): cold collected median -0.89 us, mean +14.37,
range -24.02 / +84.72 with seven wins/five losses. Charged cold median was -8.75
but forced GC contributed -6.36 mean us; batch/first costs remained positive.
This does not prove uniform cold acceleration or explain away the adverse tail.

Confirmation full workflow collected median was -3,526.77 us, charged median
-3,238.95 us; all twelve pairs improved in both regimes. Natural full workflow
retained a +9,552.44 tail. The Scheme receipt preserves short/long samples,
A/A/B/B, non-GC/GC/residual component means and unavailable allocation counters.
The source-level no-rebuild laws do not imply those wall-time results.

After preserving independent build-entry/progress fixes from upstream Scheme
commits `688555b` and `3ba1b34`, final local acceptance passed 150 modules /
1,871 cases: module phase 223.15 s, complete paired entry 12.91 s, whole command
236.61 s. Query/benchmark source was unchanged by that integration; benchmark
cohorts above were not resampled. Original checks and resource caps remain.


The private visibility filter now delegates reverse traversal to Gerbil's standard
RBTree/vector folds instead of exporting a public snapshot first. The finite
`foldVisibility_eq` theorem identifies its `Except` reverse fold with the original
ordered visibility specification, including the original first refusal.
`visibilityExportCells_direct` counts elimination of the input's owned spine and
entry pairs only: partial capture, output spines, callbacks, actual heap/GC and
wall time remain outside that count. Standard storage traversal and serialized
registered-source changes remain host premises. Public snapshots remain owned,
and no cache rule or concrete value-admission requirement is weakened.

The paired Gerbil receipt is in `doc/prototype-maps.md` in the independent Scheme
repository. The longer twelve-pair cold collected mean/max were +0.55/+53.13 us;
the worst pair had +42.84 us non-GC CPU and +10.29 us residual, with zero batch GC.
Identical-construction controls also varied. Charged full workflow won 12/12,
mean -3.55 ms, but collected and natural workflow retained positive wall tails
despite lower CPU. These measurements are not consequences of the finite theorem
and do not establish universal wall-time or GC bounds. No raw benchmark archive
or dependency on this Lean checkout is added to Scheme.


## Finite carrier admission before representation selection

A source witness found the tree constructor accepting a vector through generic
iteration, while compact construction refused the same carrier. A producer could
also run on the tree path despite the constructor's declared finite list grammar.
The standard `using` / `list?` boundary now admits proper finite lists before
storage selection, and the C3 catalog merge admits a proper list before filtering
its roots. Existing opaque roots retain their sharing/conversion path. No generic
Iterable evaluation, additional map implementation or per-query guard is added.

This is implementation future work guided by the author's representation-
equivalence argument (`poof.scrbl:980–1031`), not a claim that the paper prescribes
this host API grammar. Existing `captureCatalog` and `prepareCatalog` are composed
by `captureThenPrepareCatalog`; theorems prove grammar-error precedence, policy-
independent observations/failure, and corrected finite-request retry. Standard
host proper-list/Symbol recognition, immutable storage, registered sources and
serialized edits remain premises. The finite model does not encode arbitrary
Scheme cycles, prove the runtime list predicate, roll back argument/callback
side effects, or assert wall-time/GC bounds.

The retained-cache regression also rejects malformed public source replacements
before invalidation: source/child revisions, instances, layouts and issued read
credentials stay current. A corrected proper-list replacement then invalidates
both owners once and revokes the old reads. `captureThenPrepareCatalog_refused_frame`
reuses the existing `Object.publishEdit` boundary to retain the whole abstract
source/cache state on grammar failure.

The test-package preparation allocation is also modeled in the existing
representation module. `parallelPreparation` repartitions existing slots toward
more independent standard-make frontends, retaining two asynchronous backends
when selected. Its theorems bound declared slots, aggregate workers/backends and
Scheme heap while preserving package capacity. The 3-by-3 to 4-by-2 example uses
12 slots and the same 24 GiB declared heap envelope. These are resource accounting
claims, not physical RSS, GC, OS scheduling or wall-time guarantees; execution of
the unchanged package inventory is checked by the actual Gerbil build/test
receipts. The separately authorized 2 GiB root compiler is unchanged.

Concrete declaration admission now shares the existing revision fence with
visibility preparation. `finishVisibility` is generalized over the prepared
payload; `publishDeclaredValue` composes it with an installer. Theorems establish
original-error precedence, refusal before installation after successful but stale
validation, exact stable retry and retention of the post-callback state on refusal.
Function payloads are covered without invoking their bodies. This is not rollback
of checker effects, proof of arbitrary callbacks, host contract correctness or
concurrent synchronization. Registered-source invalidation and serial supported
edits remain premises. The Gerbil regression and shared service publication
example exercise the corresponding actual cache/credential lifecycle.

Checked C3 publication now retains the canonical reference after a successful
hook, while the Gerbil public query and inherited continuation expose separate
standard list copies. The existing `InheritedMOP.checkedOrder` model has canonical
admission, changed-order refusal, original-hook-error and final-cache soundness/
refusal theorems. `Examples/InheritedHooks.lean` covers diamond reordering, retained
canonical admission and exact refusal. Lean lists are immutable: physical host
spine isolation is a premise, tested by actual public and retained-continuation
mutation regressions, not a proved allocator or compiler property. Object payloads
remain shared and supported source edits retain their ordinary invalidation rules.
