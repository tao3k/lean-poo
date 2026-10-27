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
