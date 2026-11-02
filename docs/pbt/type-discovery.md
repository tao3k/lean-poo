# Typed descriptor discovery

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Source-consistent scalar stages in recursive derivation](#source-consistent-scalar-stages-in-recursive-derivation)
- [First-observation snapshots during recursive descriptor discovery](#first-observation-snapshots-during-recursive-descriptor-discovery)
- [Constructor-bound typed sampler declarations and mandatory owners](#constructor-bound-typed-sampler-declarations-and-mandatory-owners)
- [Bounded tagged Sum derivation and retained branch identity](#bounded-tagged-sum-derivation-and-retained-branch-identity)
- [First-observation admission for explicit Map factories](#first-observation-admission-for-explicit-map-factories)
- [Shared sampler declaration snapshots](#shared-sampler-declaration-snapshots)
- [Ordered fixed-carrier edge discovery](#ordered-fixed-carrier-edge-discovery)
- [Shared opaque sampler admission before optional metadata](#shared-opaque-sampler-admission-before-optional-metadata)
- [Prepared finite hash directories before typed declaration binding](#prepared-finite-hash-directories-before-typed-declaration-binding)
- [Bounded known carrier directories before edge observation](#bounded-known-carrier-directories-before-edge-observation)
- [First-observed Sum metadata and bounded tag directories](#first-observed-sum-metadata-and-bounded-tag-directories)
- [Shared sampler declarations owned at first return](#shared-sampler-declarations-owned-at-first-return)

## Source-consistent scalar stages in recursive derivation

The recursive carrier audit reproduced late refusal in the existing interpreter:
while admitting a two-field Tuple, the first custom leaf predicate revised its
registered owner. The parser still called both leaf predicates and both measures
before `run` finally refused stale. After the fix the same control calls one
predicate and zero measures. This concerns declared graph dependencies, not
inference of hidden mutation or a new recursive Type semantics.

`testing/recursive-generation.ss` now scopes its existing graph check with
`with-generation-check` during bridge preparation and each recursive observation.
Primitive membership, weight, scalar shrink and bridge construction reuse
`with-sources`. A revision therefore stops before measurement, a sibling request
or a later bridge. The checker retains POO's `GenerationRefusal(stale)` category
for direct callers; outer property scopes retain their own nonlocal refusal.
Original exceptions bypass trailing checks unchanged. The transient checker is
not retained in sample nodes; existing graph observers still own returned trees.
The Interaction program, solver, source stamps, natural quota accounting,
carrier packing and retained-tree shrinking are unchanged. No second evaluator,
source registry, compatibility path or namespace is introduced.

Four regression cases cover direct admission/measurement/shrink, measure revision,
exact measure/shrink exceptions, and distinct scalar bridges sharing one owner.
The Record/FUN example `source-tree-tests` in `examples/recursive-trees.ss` shares
one strict Record leaf across List, Pair, Maybe and Tuple carriers. Its Function
field keeps call validation. Declared predicate/measure revisions prevent the
property from running; a fresh action shrinks an intentionally false service claim
and exercises seed and concrete replay. Old reports keep their captured authority.
The independent generic package remains 92 cases; no POO dependency is added.

Eight `checkLeaf` laws in `RecursiveGeneration.lean` reuse `guardedThen` rather
than modeling another interpreter: stale preflight, predicate revision, ordinary
membership refusal, original predicate/measure causes, measure revision, exact
fresh weight/state publication, and suppression of later continuations. Existing
finite grammar/depth/node laws remain unchanged. Faithful host stage encoding,
accurate pure graph observers, natural measure admission and serial terminating
callbacks are premises. Guards operate between callbacks, not inside arbitrary
caller code or Type contract evaluation. Host GC, unwinding, arbitrary termination,
concurrent mutation and wall-clock behavior are outside these laws.

The implementation retains Rackcheck's [predicate-before-subtree and lazy mapping structure](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt),
using Gerbil's existing scoped checks for this project's registered revisions.
Source checking adds active-ledger/graph walks at primitive boundaries; no
zero-cost or timing improvement is claimed. No process, search, observation,
depth, node or proposal limit is widened, and complete local/CI gates remain.

## First-observation snapshots during recursive descriptor discovery

The audit reproduced an accepted mixed preparation: the first custom `.generator`
changed an already discovered, unvisited sibling descriptor; the sibling's epoch
was then captured only when visited. Both factories ran and the property returned
`passed`. Previously declared sampler dependencies had the same late-snapshot
hole. Runtime bridge checks could refuse changes to earlier Types but could not
recover the earlier epochs that discovery never retained.

Graph discovery now owns one identity-deduplicated ledger. `intern` captures each
Type at its first discovered edge; each returned sampler and explicit dependency
is registered once before another factory runs. Rediscovery never updates an
owned epoch. The shared `graph-sources-current?` predicate checks both revisions
and opaque sampler hooks during discovery and evaluation. A temporary standard
`with-generation-check` scope and the existing `with-sources` action protect custom
factories and their nested checked work; the checker is not stored on the graph.
Original callback causes escape unchanged. A stale preparation publishes no sampler
or replayable witness; factory side effects are not rolled back.

The evaluator reuses the original graph stamps instead of taking a second late
snapshot. Its scalar sampler list is prepared once using Gerbil's `filter-map`,
removing the per-observation vector-to-list/map work of the previous hook scan.
The official runtime utility is reused, not reimplemented. Existing graph,
carrier, fixed-point, source and FUN protocols retain their ownership.

Seven standard `discovery-test` cases cover known sibling changes, earlier declared
dependencies, opaque refusal/errors, original factory causes, inherited producer
sources, deduplicated shared identities and runtime refusal. The complex
`preparation-tree-tests` example composes shared Record leaves, Function fields,
Tuple/Pair carriers and automatic property Reader/FUN preparation. Both a sibling
revision and a shared dependency revision refuse before later work. Explicit retry
then shrinks a real typed witness, preserves Function wrapping, supports both replay
modes, rejects old reports and can reprepare after another owner revision. The
generic stdlib-only kernel is unchanged and still requires all 109 cases.

Six `captureRevision` laws in PropertyScopes establish first-capture preservation,
new-source registration, the one-entry growth bound, identity uniqueness, the
impossibility of refreshing a stale ledger and preservation of fresh ledgers.
Existing guarded-stage laws supply callback refusal/exception semantics. Top-level
examples show an early revision suppressing the later factory. The finite model
assumes truthful identity/revision observations, serial terminating factories and
faithful host scope/ledger implementation; host hash equality, callbacks, GC and
wall-clock behavior remain executable or explicit premises.

This is a first-observation discipline, not an eager scan of hidden dependencies.
A Type below an undiscovered edge, or a dependency first declared by a returning
factory, is captured when discovered. Hidden closure state, concurrent atomic
snapshots and arbitrary factory termination are not inferred. Descriptor/edge,
depth, node and search caps remain unchanged. Registration uses the standard
identity table; each controlled action checks the growing unique-source ledger
and captured sampler hooks. For D descriptor actions and final A owners/S samplers,
those checks can cost O(D*(A+S)), excluding nested actions and callback costs. The
ledger growth law is not a constant-time hashing, allocation or timing theorem.

Rackcheck's pinned generator/property sources retain compositional generation and
use standard dynamic parameter lifetime for callback ownership. This unit applies
that abstraction style through existing Gerbil checked actions to the POO-specific
Type discovery extension. It does not assert missing recursive Type metadata
features in Rackcheck, add a second runner, change draw/seed order or force omitted
Function inputs. No speedup is claimed from metadata deduplication alone.


## Constructor-bound typed sampler declarations and mandatory owners

Two soundness reproductions selected this unit. Relabeling an automatic Integer
sampler as `(Exactly 999)` preserved its old bounded acceptance hook: the property
ran once and returned `passed` for a value outside that declaration. Separately,
replacing `sources` with an empty list hid a real descriptor revision and permitted
a pass. The trace variant was also reproduced: changing a model's Command after
construction let a List-of-Integer sampler publish string commands and pass while
membership in its declared Type was false.

The existing private GeneratorRecord now stores the constructor's `bound-descriptor`
as Type metadata. The shared `generator-sources` preparation boundary checks its
identity against the actual descriptor and always contributes sampler + actual
Type before additional dependencies. Producer bridging, products, Map preparation,
inspection and portable import already use that boundary. No per-value predicate,
extra generation-factory call, new namespace or wrapper per consumer is added.
Bounded recursive acceptance remains intact: blindly adding a universal Type
predicate would reintroduce unsafe/unbounded membership checking.

A different descriptor requires a fresh `make-generator`, `from-generator` or
controlled `generator` construction. The example uses an explicit value projection
and normal Record initialization, rather than relabeling an inherited parser/tree.
Same-descriptor draw/shrink overrides retain their existing fallback semantics.
The binding is constructor-owned protocol metadata, not a new user tuning field;
this is not a security proof against forging private metadata or untruthful custom
acceptance hooks. Hidden callback dependencies remain the application's obligation.

Trace's compiled model/List acceptance now captures its existing declaration
sources through `snapshot`/`source-guard` at construction, outside lazy slot
initialization. This matches products, Maps and recursive graph ownership. Model,
List or captured metadata revisions retire the old sampler even before its first
run and even if optional dependencies are replaced. Fresh `trace-generator`
construction establishes the new protocol. Source precedence and ordinary callback
exception behavior remain unchanged; a fresh declaration mismatch is a preparation
error, while an already retired protocol retains normal stale refusal.

Seven `sampler-binding-test` cases cover raw/recursive/trace retargeting, mandatory
revision observations during draw/property/measure/shrink/labels, pre-read refusal,
no generator invocation during concrete import, products/Maps/Function inputs,
trace declaration changes, and lawful callback overrides with both replay modes.
The existing generated-products example adds a complete service schema migration:
strict Record inheritance, a projected region field, retained Function wrapping,
Reader/FUN report delivery, shrinking, both replay forms, target revision rejection
and explicit retry. There are eight new standard cases overall. The independent
stdlib-only kernel remains unchanged at 109 cases.

Six laws in PropertyScopes use the existing source union:
mandatory owner membership/currentness, descriptor refusal independent of optional
dependencies, equal-binding admission, unequal-binding rejection, and preservation
of binding/required identities after successful preparation. Top-level negative and
fresh-construction controls accompany them. These finite identity/observer laws
assume faithful constructor metadata, truthful bounded acceptance hooks, accurate
source clocks and serial terminating callbacks. They do not prove arbitrary user
predicates, host heap immutability, universal subtyping or concurrent snapshots.

Rackcheck's pinned property executor consumes a generator together with the
property's argument bindings; its retained shrink-tree algebra does not
implicitly convert one application declaration into another. This unit preserves
that compositional separation in the POO Type extension, rather than introducing
a second validator or assuming Racket has this mutable descriptor protocol.
The metadata field and preparation identity/source reads have costs; no timing or
allocation speedup is claimed. Existing random schedules, lazy trees, generator
factories, source failure priorities and all process/heap/depth/proposal caps remain
unchanged. Concrete import still reads no input before failed preparation and
performs no draws or child forcing. Port failures still have no rollback guarantee.

## Bounded tagged Sum derivation and retained branch identity

The audit found a concrete gap in the existing finite container algebra: Sum had
validation, wrapping and serialization, but automatic PBT derivation required a
custom scalar generator. Union/Or support did not supply tagged construction or
preserve distinct labels sharing one payload Type. This extends the existing
finite derivation protocol; it does not add unrestricted Type inference.

`type.ss` now gives the existing Sum constructor the nominal `Sum.` carrier
prototype. Existing fields, validation and serialization remain on that constructor;
recognition does not guess from arbitrary slot names or printed declarations.
Explicit `.generator` overrides retain precedence. The existing generation graph
owns ordered `(tag . child-index)` alternatives, while shared payload Types still
have one graph identity. Only depth/node-feasible branches participate in drawing.
A Sum record contributes one constructor node; a recursive Sum edge is a concrete
carrier, unlike an unguarded transparent Union alias. Empty/no-feasible branches
report controlled exhaustion under the existing limits.

Preparation reads the effective `variants` directory, captures its epoch before
reading tags, and discovers each payload Type before reading another branch.
The shared edge-discovery action reserves descriptor fuel before a metadata
getter and interns its returned Type immediately. The finite, distinct symbolic
tag spine is copied; source checks surround metadata callbacks. Neither the old
`types` snapshot nor a later revision may refresh already captured authority.
Malformed catalogs are preparation errors; no branch resampling hides failures.

Construction uses the descriptor's existing `make` method once per emitted value.
Its result must retain the selected tag and exact payload. Constructor/getter
callbacks retain original errors and source checks between stages. Inspection
checks a known tag before reading payload and uses only that captured branch; it
retains the original carrier without invoking `make` again. Both retained-tree
and value-only shrinking keep the tag and child provenance. No tag switching,
payload redraw, arbitrary Function synthesis or extra validator chain is added.
The existing scalar/Record protocols retain Function wrappers.

`examples/recursive-trees.ss` exposes `JournalCommand`, `JournalObservation`,
`journal-observation` and `tagged-journal-tests`. A normal Record/FUN action compares
credit/debit/clear journals with an implementation that ignores debit. The
regression reduces this fault to one debit of one, replays its seed and integer/
symbol corpus, refuses retired directory ownership, then prepares the corrected
service. Additional controls cover shared payload nodes, recursive Sum/List
carriers, empty/depth/node limits, unknown labels without payload reads, exact
constructor errors, changed constructor output, nested Record/Function payloads,
metadata invalidation and descriptor-budget refusal before later getters.

`PropertySequences.lean` proves ordered feasible-branch membership, residual node
bounds, tag/payload shrink provenance, preservation of strict measure descent,
unknown-tag getter suppression, original getter errors and successful tagged
inspection. Top-level `Examples/PropertySequences.lean` covers shared-node labels
and forbidden getters. Existing recursive-evaluation, source-snapshot and retained
sample laws supply the enclosing protocol assumptions. These are finite source
laws, not proofs of Scheme execution, PRNG distribution, arbitrary callback
termination, concurrent mutation or macOS loading time. Accurate revision clocks,
faithful metadata/callback interpretation and the existing ownership discipline
remain premises. This advances the paper's future-work direction.

Preparation visits one edge per declared tag, with the existing descriptor quota;
choosing or looking up a tag scans at most the captured finite directory. Payload
inspection and shrinking retain their existing search/proposal/node budgets.
These operation counts do not imply constant lookup cost, allocation bounds or a
wall-clock speedup. No upstream changes, runner, namespace or resource-limit
changes are required; the independent generic package remains POO-free.

## First-observation admission for explicit Map factories

The concentrated audit reproduced a concrete preparation defect: a Map Value
getter could revise the previously read Key Type, after which `map-generator`
captured the new revision and invoked both key validators. The old factory
therefore admitted authority it had already observed becoming obsolete. This is
an explicit factory defect, not a request for arbitrary Type inference. Self-
mutation of the object currently computing a slot was already forbidden by the
object guard and retains its original error; it is not claimed as a new gap.

Map preparation now copies caller-owned key/dependency spines before callbacks,
captures known request owners before validation, and records each effective Key/
Value identity before Type validation and the next getter. A shared private
`retain-source-stamps!` uses the product factory's existing identity hash policy;
rediscovery never replaces old stamps. The transient checker reads only epochs.
The sampler observer is captured once and invoked at explicit checked actions,
so it cannot recursively enter itself through that checker. The retained guard
rechecks epochs after a successful observer result; a true result cannot authorize
a source the observer itself retired. The no-hook path keeps one epoch pass. There is one retained
Map guard and the transient checker is not copied into trees or reports.

The existing generic finite-domain constructor still owns key shape/duplicates/
quota admission before application key validators. Those validators still must
preserve key identity. Original callback exceptions, including false, propagate
unchanged even when a callback also invalidates a source. Revisions refuse before
a later getter, binding or key validator; empty domains retain all owners. A fresh
factory is the only retry path. Failed preparation does not roll back user effects
or renew an earlier sampler/report.

The existing Record/Function/FUN service example now exports `map-service-action`
for a declared directory; `map-service-tests` reuses it. Its deterministic two-key
tree and typed sampler share the original Map guard instead of losing Key authority
behind a custom generation recipe. The regression first refuses a directory whose
Value getter revises Key, then freshly prepares a failing service, shrinks values
while retaining Function wrappers, replays seed/concrete/corpus witnesses, rejects
a later Key revision and explicitly prepares a new report. No fixture parser or
new framework is involved.

The sampler suite is moved intact to `t/representations/property-testing/samplers.scm`,
with standard `extra-inputs` tracking. All old cases remain, and controls cover
effective-Type ordering, known roots/dependencies, sampler-validation side effects,
request-spine mutation, false exceptions, observer re-entry and fresh repair.
The independent generic package stays at 148 cases; it does not import POO.

`PropertyScopes.lean` composes the existing `observeDeclaration`/`captureRevision`
protocol as `observeMap`: preflight refusal, first/second-read errors, Value retiring
Key, original error causes, stable exact publication and a bound of two added
metadata identities. `mapObserver_revised` additionally rejects an observer that
returns true after changing a known owner. Alias and fresh-epoch examples retain
the same ledger. Exact
host source clocks, faithful metadata/validation, terminating callbacks and the
existing observer discipline remain premises. These finite source/model laws
advance the paper's future work; they do not prove concurrent atomicity, compiler
execution or physical performance.

Preparation checks traverse the finite unique owner ledger; source registration
uses the existing hash policy. The retained guard has that closed ledger and one
optional sampler hook, with no extra per-value factory/checker stack. The two-Type
metadata bound is not a byte/time bound for arbitrary dependencies or callbacks.
No latency improvement is claimed. No upstream changes, new namespace, scheduler,
resource-limit changes or acceptance reductions are introduced.

## Shared sampler declaration snapshots

The audit reproduced a shared late-capture defect beyond explicit Map factories:
`.sources` could revise the Type previously returned by `.descriptor`, then the
old snapshot registered its new epoch and a direct bridge invoked draw successfully.
The same path served checks, diagnostics and products. This is a finite declaration
admission defect, not a request for unrestricted Type inference or deep freezing.

`generator-sources` now reads actual declaration, bound declaration and finite
sources in that order under the existing source boundary. An internal retention
callback records each identity immediately. Identity retargeting still fails with
the original binding error before dependencies are read. Returned source spines
are copied; malformed declarations remain errors. `snapshot` freezes explicit
request dependencies, captures known owners before getters and uses the same
`retain-source-stamps!` identity-hash policy as products and Maps. Repeated/aliased
identities retain their first stamp. Its transient checker reads only epochs,
never sampler metadata or observer hooks, and is not retained on trees/reports.

Map preparation now uses that shared capture before valid raw sampler declarations
are admitted as a GeneratorRecord. Missing declarations retain ordinary Record
errors. No separate per-entry snapshot implementation or validation wrapper is
added. Original getter exceptions, including false, propagate unchanged; failed
preparation does not roll back effects. A fresh snapshot/bridge is required to
retry. Existing root/child source limits and generation/shrink budgets are unchanged.

Controls cover direct bridge, inspection, property check, product and finite Map
entrypoints. A bound getter retiring the actual Type cannot reach sources. Tests
also cover explicit dependency-spine mutation, original causes, alias/self sources,
nested source reads without recursive checking and fresh retry. The existing service
value generator is extracted once as `service-value-generator`; both Map services
and `service-batch-action` reuse its Record/Function construction. The shared-field
batch refuses obsolete source preparation, then freshly runs through FUN, shrinks,
retains Function wrappers, replays seed/concrete/corpus data, rejects a later Type
revision and retries with a newly prepared action.

`PropertyScopes.lean` adds nine finite laws for source-list registration and sampler
preparation: stale history cannot be repaired, fresh capture stays fresh, added
identities are bounded by declaration count, known identities keep exact stamps,
failed declaration reads suppress dependencies, binding mismatch stays distinct,
later dependencies cannot renew an earlier Type, original causes remain exact and
stable preparation publishes the closed source set. Examples distinguish early
bound failure, stale versus false causes, aliases and stable source capture.
Clock fidelity, standard dynamic-scope behavior, faithful metadata and callback
termination remain premises; no compiler/runtime or concurrent atomicity proof is
claimed. Raw dependency payloads are not deep-frozen and hidden callback dependencies
are not inferred. This advances the paper's future-work direction.

The finite owner ledger uses standard identity hashing. Clock checks visit its
unique entries; registration adds at most one identity per declared occurrence.
These are preparation bookkeeping bounds, not callback-time, byte or wall-clock
bounds. Draw/shrink retain their existing tree protocol; no transient checker is
retained and no latency improvement is claimed. The independent generic library
remains POO-free at 148 cases. No upstream, namespace, scheduler, resource-limit
or complete-acceptance changes are required.

## Ordered fixed-carrier edge discovery

The source audit reproduced two related defects in the finite recursive graph:
Pair evaluated both child getters before registering either child; its right
computed declaration could therefore revise the left Type and the resulting
sampler still returned current. List also evaluated its child getter after the
remaining descriptor occurrence budget was zero. Both probes use lazy declarations
and confirm zero getter calls/unchanged owner revisions before public generator
entry. Caller-side initialized-object effects are outside this observation.

List, Pair, Maybe and OrFalse now use one local ordered field traversal through
the existing discover action, as Sum's named branches already do. Each edge checks
remaining occurrence fuel before its getter, brackets the getter with the existing
source scope, then interns/captures the returned identity before the next field.
No alternate graph, cache, validation wrapper or dispatcher is introduced. Dynamic
Tuple/Union rows keep their existing directory admission and ordered traversal.
Repeated/shared identities still spend occurrence fuel and occupy one graph node;
edge order, PRNG schedule, carrier packing and lazy shrinking are unchanged.

Five regression cases cover earlier-Type retirement before factories, unary and
Pair quota boundaries, exact false/object exceptions and scope restoration,
repeated/shared identity accounting, and an integrated Record/Function service.
The service shares a Pair through Tuple/List and its Record leaf through Maybe;
a computed right edge retires the first-observed left Type. Initial preparation
returns a non-replayable stale report without opening any leaf factory. Explicit
fresh preparation uses the completed metadata, derives the shared leaf once,
shrinks a real service fault, preserves nested Function contracts, agrees on
concrete/seeded replay, refuses old reports after dependency revision and retries
through the same FUN action. Reusing a new attempt never renews old receipts.

Eight finite PropertyPreparation laws reuse guardedGeneration and captureRevision:
zero-fuel getter suppression, stale preflight, original exceptions, post-getter
retirement refusal, exact stable state/fuel/identity, shared occurrence accounting,
current first-observation capture and bounded ledger growth. Top-level examples
exercise exhausted throwing getters, sibling retirement, aliasing and false causes.
Faithful revision clocks, sequential supported edits, standard dynamic-scope
restoration and terminating callbacks remain premises. Edge fuel bounds discovery
occurrences and registration cardinality, not arbitrary getter cost or latency.
This continues the finite future-work protocol; full checks and process limits
remain unchanged, and no compiler/runtime or unversioned-heap proof is claimed.

## Shared opaque sampler admission before optional metadata

The audit reproduced an opaque-leaf source-order defect. A custom sampler declared
an owner in sources, then its delayed .inhabited? getter retired that owner. The
recursive compiler inspected availability before registering the sampler/dependencies,
so it captured the newer epoch and returned current. The frozen public generator
probe starts with owner revision/read count zero and previously accepted-current.
Construction-side effects before a factory returns remain outside this observation.

The existing generator-sources implementation now lives in generation-graph and
is imported by the typed bridge through the standard module system. Graph leaves
use that SAME constructor binding and first-observation protocol before optional
metadata: sampler identity, actual/bound Type identities, then declared source
spine and objects. The recursive compiler no longer separately reads sources after
availability, and scalar dispatch no longer reads descriptor before sampler capture.
There is no second validator, registry, cache, guard chain or namespace. Generated
errors for constructor mismatch use the shared binding protocol; original callback
exceptions retain exact identity, including false after a source change.

False availability still means an empty alternative. Such a leaf keeps its source
obligations, contributes no finite inhabitant and is never drawn to retry another
branch. True availability and absence of the optional field retain their prior
meaning. Shared identities still compile once, descriptor occurrence budgets and
PRNG schedules are unchanged, and runtime trees keep the original captured epochs.
Explicit fresh construction can retry; existing reports cannot renew authority.

Six regression cases cover source retirement in optional metadata, actual/bound
retargeting before optional reads, malformed source declarations, exact exceptions
and scope restoration, source-owning empty alternatives without draws, and a
shared Record/Function service through Tuple/List/Pair. The service reveals its
owner only through the returned sampler. Initial preparation stops after that
sampler's metadata, before a later factory. Fresh FUN preparation derives the
shared leaf once, shrinks the service fault, preserves nested Function contracts,
agrees on concrete/seeded replay, rejects obsolete receipts and admits a corrected
service on explicit retry. The independent generic library keeps its POO-free
module boundary.

Six PropertyPreparation laws compose existing observeSamplerSources and
guardedGeneration: admission refusal skips metadata, stale preflight skips it,
retirement refuses publication, exact metadata causes survive, stable preparation
keeps declaration/state/ledger, and refused preparation cannot enter later work.
Top-level examples distinguish false availability, false exceptions and stale
refusal, and reject binding mismatch before a throwing optional getter. The model
is conditional on the existing constructor/source admission result, faithful host
revision clocks, normalized availability classification and terminating callbacks.
It does not discover hidden callback dependencies, prove arbitrary Type predicates
or model effects before a factory returns. Bookkeeping remains one declared-source
traversal with first-identity retention; no wall-clock improvement is claimed.
The finite future-work scope, complete checks and resource limits are unchanged.

## Prepared finite hash directories before typed declaration binding

A public Map probe with one key and `domain-limit: 0` refused only after one
computed Key read and two generation-factory metadata reads. This violates the
existing request-before-preparation ordering: an invalid finite directory must
not execute declarations or replace its own error with an unrelated factory cause.
This is a finite protocol defect, not unrestricted Type inference.

`testing/property/generator` now owns `prepare-hash-generator`: it checks finite
shape, a natural key limit and uniqueness using Gerbil HashTable equality, then
captures the ordered key spine. The result is an ordinary higher-order constructor
for value generators. The existing `generator-hash` delegates to it; typed Map
prepares it before snapshots/computed declarations and binds it later under the
same source guard. No duplicate key-validation algorithm, cache, runtime wrapper,
namespace, registry, PRNG or test framework is added. Each binding still has its
own producer authority; each draw has fresh selected rows and retained trees.
Payload keys retain their existing caller-owned immutability/source obligations.

Malformed topology, invalid/exceeded limits and duplicate keys are ordinary
preparation errors. Valid requests retain the original source checks, exact
callback exceptions, key-representation rule, Function wrapping, shrinking and
replay. Empty directories fit a zero limit but still bind typed declarations and
retain mandatory Map value-source authority. Prepared key-directory reuse never
refreshes retired source epochs. Static request refusal precedes subsequent
metadata, including malformed metadata, as it already does at other public PBT
boundaries.

Three independent-library cases cover invalid directories, owned topology and
independent producer binding, plus direct/prepared full checks, shrinking, seeded
and concrete replay, and stale refusal without another draw. The isolated package
now requires exactly 208 cases. Typed regressions suppress Key/factory/hook reads
on invalid requests and retain empty-Map source authority. A complex existing
collection example composes Record, wrapped Function fields and FUN delivery:
budget refusal, explicit repaired preparation, real shrinking, both replay forms,
old-report rejection and fresh-source retry use the same normal workflow.

Eight finite Lean laws in PropertySequences prove malformed/budget/duplicate
refusal, exact valid-directory preservation, bounded unique results, suppression
of later continuations, reusable binding and unchanged later failure causes.
Five top-level examples cover oversized/duplicate/empty/Boolean directories and
stale binding. Accurate host list recognition/copying, equality/hash agreement,
key stability, pure revision observers and terminating sequential callbacks are
premises. These laws do not certify hash collision complexity, host allocation,
compiler/runtime behavior or wall-clock speedup. This advances the paper's future
work. Existing heaps, cancellation, complete checks and natural compiler/test
completion remain unchanged.

The Racket comparison remains the pinned Rackcheck `gen:bind`/shrink-tree algebra
and Quickcheck's sequence/binding separation: preparation builds reusable ordinary
combinators; execution alone owns randomness and retained sample provenance. This
unit changes neither the seed splitting schedule nor the existing shrink policy.

## Bounded known carrier directories before edge observation

The audit reproduced two first-observation holes in Tuple/Union/Or discovery.
An inherited checked action rewrote the returned child-list spine during its
first edge: the graph silently replaced the originally declared sibling Type.
A second probe changed a known unvisited sibling's revision at the same point;
preparation captured that later epoch and returned a current graph. The reproduced
outputs were `changed=#t original=#f` and `changed=#t current=#t`. These concern
already returned finite directory topology and known identities, not arbitrary
Type inference or discovery of hidden callback dependencies.

The existing graph owner now prepares known child directories in one private
operation. It admits a proper finite list, compares its entire occurrence width
with remaining descriptor fuel, copies the spine and records every known Type's
first epoch through the existing identity ledger. Only then does the SAME ordered
discover/intern traversal run. No extra fuel is spent on registration: intern
still charges every shared occurrence. A too-wide directory refuses with the
existing descriptors category before copying or child checks; malformed shape
keeps its existing error. This stage follows the parent's metadata getter and
its existing initial scope: it does not suppress or infer that getter's effects.

Tuple, Union and Or reuse this one operation; branch order and repeated edge
positions are preserved. Known epochs cannot be refreshed by the first inherited
checker. Dynamic Pair/Maybe/OrFalse fields and Sum payload getters keep their
existing quota-before-getter path; their Types are not guessed before return.
Per-edge source checks and original callback causes, including thrown false,
remain. This is a shallow topology snapshot, not a freeze of mutable Type payloads
or a substitute for explicit revision updates. Old reports cannot acquire new
authority by repairing a declaration; callers prepare again under fresh epochs.

Five focused regression cases cover all three carrier kinds, replaced/improper/
cyclic caller spines, pre-edge sibling retirement with zero factories, occurrence
fuel for repeated identities, legal empty Tuple directories at zero remaining
edge fuel, malformed requests and exact callback causes. The complex standard
recursive-trees example shares Record/Function leaves through Tuple, Pair, Union
and List via FUN. Directory retargeting cannot change its declared carrier or
produce an out-of-domain witness; sibling revision refuses before binding.
Explicit corrected publication starts a fresh run, shrinks a real false witness,
preserves Function contracts and both replay paths, rejects old root/owner epochs,
and admits a corrected property only after fresh preparation. The independent
standard-library PBT kernel is unchanged and retains all 231 cases.

Existing Function-input and dynamic-edge discovery definitions/laws move from
PropertyPreparation into the functionally named PropertyDiscovery module. The
namespace and declaration names remain; Preparation imports that actual owner,
without aliases or a compatibility layer. Nine new finite directory laws reuse
captureSources and discoverCarrierEdge for malformed/quota refusal, complete row
retention, empty rows, known-epoch retention, copied-width and ledger-growth bounds,
stale-first-edge refusal and exact error causes. Six top-level examples distinguish
repeated occurrences, exact fuel, an advanced sibling clock, false causes and
empty versus malformed input.

The copied directory width is bounded by remaining occurrence fuel, and source
registration adds at most one entry per declaration. Full-list recognition and
source checks still have costs; this is not a constant-time refusal, GC/RSS proof
or latency improvement. Faithful host shape recognition/shallow copying, primitive
revision reads, identity hashing, accurate observers and terminating sequential
callbacks remain premises. Arbitrary untracked payload mutation, concurrent writes,
Gerbil/Gambit and compiler verification remain outside the claim. This advances
the paper's future work.

The author/Racket comparison remains an abstraction reference: keep finite
construction, source ownership and ordered higher-order traversal at their
existing boundary, rather than add an executor or per-carrier wrappers. Gerbil's
list-copy, for-each and map-in-order serve the implementation; the graph's existing
registry and controlled recursive evaluator retain all runtime ownership. Complete
checks, original heaps, natural compiler/test completion and cancellation stay.

## First-observed Sum metadata and bounded tag directories

The next audit reproduced a first-observation gap in the existing tagged Sum
compiler: a checked inherited observer changed a returned `(first second)` tag
spine before discovery copied it, and the resulting graph used `(first foreign)`.
The variants object also acquired its revision only after the returning observer,
so that observer could retire the returned directory before its first capture.
These are existing supported metadata boundaries, not requests for unrestricted
inference or a new recursive carrier language.

Sum now captures the variants object's first epoch inside its existing checked
getter action. The subsequent returning observer therefore sees that participant.
The tag getter uses the SAME checked boundary to admit proper distinct symbol
labels, enforce complete occurrence width, and copy the spine before its returning
observer runs. Tag order and identity remain unchanged. Payload Types are still
dynamic: each original ordered edge is read through discover, and shared payload
identities still spend one descriptor credit per occurrence. No hidden payload
Types are guessed, and no payload getter runs when the entire tag width exceeds
remaining occurrence fuel.

The graph's private own-directory operation serves both this tag admission and
[Bounded known carrier directories before edge observation](type-discovery.md#bounded-known-carrier-directories-before-edge-observation) known Type rows. It replaces the earlier inline proper-list/width/copy steps,
with an optional semantic grammar predicate; it adds no runtime wrapper, registry,
public interface or namespace. Invalid Sum grammar retains the existing message;
valid over-width rows now refuse with descriptors before child effects. Accepted
rows retain ordinary source checks, exact original callback causes (including
false), payload sharing and explicit fresh preparation. Shallow copying owns only
the label spine, not arbitrary mutable payloads or callback effects.

Four discovery regressions cover replacement/improper/cyclic edits after return,
directory retirement before any label/payload/factory access, insufficient versus
exact fuel for three shared payload occurrences, and malformed/duplicate/nonsymbol
labels plus exact throwing getters. The existing recursive-trees TestSuite adds a
complete shared Record/Function Sum service through property-action: returning
directory retirement yields a non-replayable stale report with zero factories;
explicit fresh publication then really shrinks, retains Function validation,
replays the seed and concrete witness, refuses obsolete owner epochs and retries
a corrected property. It reuses standard module registration, FUN, Record and the
current typed generator; the independent generic PBT package is unchanged.

Eight finite PropertyDiscovery laws model normalized tag admission, width refusal,
first-epoch observation, post-observer retirement, exact causes and retained ordered
labels, plus known-epoch retention and at-most-one directory ledger growth. Four
top-level examples distinguish revised metadata, shared-label order, quota before
a throwing observer and a thrown false. The clock is sampled at metadata return;
Option normalization of host grammar, shallow-copy fidelity, accurate primitive
revision reads and terminating sequential observers are premises. These are not
Gerbil/Gambit/compiler, concurrent-mutation, callback termination, GC/RSS or latency
proofs. This continues the paper's future work.

The author's ordered prototype composition and the Racket map/bind comparison
remain the abstraction reference: capture finite declarations at their owner,
then use the existing ordered traversal and shrink/replay machinery. No second
executor or per-container validation chain is introduced. Existing complete checks,
2 GiB main/1 GiB isolated limits and cancellation remain; compilation and semantic
tests retain their already authorized natural-completion behavior.

## Shared sampler declarations owned at first return

The global PBT audit next traced the common generator-sources boundary used by
explicit bridges, automatic recursive graphs, products and finite Maps. Its
metadata readers acquired descriptor/bound-descriptor epochs and copied dependency
spines only AFTER returning inherited source checks. The reproduced direct probe
returned `retargeted=#t original=#f`: an observer replaced an already returned
owner before the original list was copied. An observer could likewise revise a
newly returned Type or dependency before its first epoch was registered. These
are supported source declarations, not arbitrary dependency inference.

The existing shared function now reads and retains descriptor/bound-descriptor
inside the SAME with-sources action, through one private named source operation.
The sources getter validates a proper finite list, copies its spine and registers
every declared identity inside its existing action before its returning check.
All consumers continue calling generator-sources; no additional bridge, sampler
wrapper, source registry, public interface or namespace is introduced. Mandatory
sampler/Type ownership, binding identity comparisons, source ordering and duplicate
occurrences remain. The supplied retain! operations are existing pure first-epoch
bookkeeping; arbitrary user callbacks are not certified by this change.

Four regression cases cover replaced/improper/cyclic edits after dependency
return, singleton Type and finite dependency retirement before snapshot delivery,
malformed dependency spines and exact false/object getter causes, plus shared
bridge/product/Map/graph refusal before any draw. Existing binding
mismatch and invalid element cases remain unchanged. The existing recursive-trees
suite adds a complete explicit Record/Function service through property-action:
a returning observer retires a shared dependency before any draw or property,
then explicit fresh declaration publication genuinely shrinks the witness, keeps
nested Function validation, replays both seed and concrete failure, rejects old
owner epochs and admits a corrected property after fresh preparation. The generic
PBT kernel is unchanged; its independent standard-library acceptance stays 231
cases. No additional module registration or runner is needed.

Seven finite PropertyDiscovery laws expose the raw-getter-return / observer split
that the previous whole-metadata-action abstraction left implicit. The new
observeCapturedSources operation reuses captureSources and guardedGeneration for
normalized malformed input, stale preflight, returning-observer retirement, exact
causes, original row/order/duplicates, prior stale-ledger retention and refusal
before a dependent binder. Singleton rows model the two Type declarations; finite
rows model dependency lists. Four top-level examples distinguish repeated owners,
a revised singleton, a thrown false and an admitted empty row. Existing
captureSources_cost bounds ledger growth by row width; this does not introduce a
new dependency quota or claim constant-time source checks.

The captured clock is sampled at the getter's return. Host proper-list recognition,
faithful shallow copying, accurate revision reads, pure registration and terminating
sequential callbacks are premises. Payload mutation, opaque undeclared dependencies,
concurrent writes, effect rollback and compiler/runtime verification remain outside
the proof. Valid getters retain their original exceptions without a trailing check
replacing them; malformed returned spines now fail at their admission boundary.
This advances the paper's future work, without a runtime latency/GC/RSS claim.

The author's ordered composition and the Racket map/bind comparison guide the
same abstraction choice: establish finite source ownership once, then compose the
existing generation/shrink/replay operations. Gerbil's list-copy and for-each do
the list work; existing Record contracts and FUN retain application composition.
All complete checks, 2 GiB main/1 GiB isolated guards and cancellation remain;
already authorized compiler/test natural completion is unchanged.

