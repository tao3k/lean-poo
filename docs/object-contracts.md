# Structural value contracts and composed admission

The original Racket text's section 5 describes type descriptors as ordinary data
with recognizers, I/O operations and additional constraints. Appendix B explicitly
leaves generalized prototypes to future work. This implementation uses that Type
and lens vocabulary. Diagnostic composition and the checked observation workflow
advance the future work; they are not a new Scheme type system or a claim that
all type-system TODOs are closed.

## Three corresponding layers

| Responsibility | Gerbil | Lean |
| --- | --- | --- |
| Ordered refusal accumulation | `object-diagnostics` `diagnostic-all` | `ObjectDiagnostics.all`, `all_nil_iff`, `all_append` |
| Gated phases | `diagnostic-then` | `andThen`, refusal/acceptance/associativity laws |
| Finite shape and optional ancestry | `ObjectContract.` | `ObjectContract.View`, `Contract`, `diagnose_nil_iff` |
| Required field semantics | existing Type recognizers and diagnostics | `required_semantics_iff` under an explicit checker law |
| No undeclared field reads | slot-name inventory, then declared `.ref` calls | `required_lookup_congr` |
| Existing invocation boundary | `metadata.typed` / `metadata.invoke` | `predicate`, `predicate_holds_iff` |
| Value admission before a consumer | `checked-action` using existing `Observation.` bind | `checkedAction_refused`, `checkedAction_accepted` |

`View` is an explicit finite observation adapter. Its lookup must correspond to
actual Scheme slot lookup and its names must enumerate actual public slots. A
stored false value is a present value, not a missing lookup. The model has no
foreign implementation oracle: it proves the supplied finite interpretation.

## Four phases and two distinct kinds of failure

Non-object/ancestry refusal precedes field observation. Inventory and required
field errors accumulate. Only their empty result enables whole-object constraints;
only successful constraints enable obligations. Ordinary issue lists accumulate
inside a phase. Scheme callback exceptions stop execution and retain their exact
identity; malformed issue lists are programming errors, not user-field refusals.
The pure Lean list laws do not prove arbitrary callbacks terminate or model
exceptions as ordinary diagnostic issues.

Membership uses empty diagnostics. Semantic soundness/completeness of custom
Types requires the explicit law that empty diagnostics agree with that Type's
recognizer. Merely supplying a `.diagnose` slot is not a proof of that law. Path
accuracy for user callbacks is also their responsibility; format checks alone
cannot prove a domain-specific path correct.

Inheritance of a descriptor is ordinary override, not a theorem of subtyping.
Replacing required fields or obligations can weaken a contract. To retain
independent obligations, compose them with `diagnostic-all`; do not infer logical
refinement merely from prototype ancestry. Closed parent inventories can also
reject newly introduced fields; explicit schema delegation owns that policy.
General polymorphism, subtype inference and type-driven generators remain open.

## Executable composed scenario

`examples/object-contracts.ss` decodes through the existing `io` Json methods and
preserves all input keys. The shape contract runs before lens arithmetic. A
persistent revision then produces a separate candidate; the complete contract
checks capacity and transport relations before the consumer writes JSON. Two
relation failures accumulate with their full paths. Reusing the action checks each
new input; no accepted-result cache is introduced. Function Type validation still
passes its actual wrapped procedure to the consumer, including multiple returns.

`Examples/ObjectContracts.lean` uses the same five service fields, Int-valued
capacity/use, and the exact 1–65535 port interval, with an explicit port-recognizer
equivalence theorem and negative-integer controls. It checks false versus
absence, ancestry gating, accumulated relationships, invocation input refusal and
normalization boundary. Scheme tests independently exercise actual slot laziness,
receiver-local descriptor preparation, JSON I/O, persistent updates and exceptions.
Neither fixture proves the parser, arbitrary MOP overrides, compiler/runtime,
resource performance, external authorization or automatic dependency discovery.
Descriptor declarations are immutable during use; normal source/revision discipline
is still required when a consumer introduces mutation. Callback external effects
are not rolled back by refusal.

## Explicit strengthening and invocation association

`Functional.ObjectContractRefinement` adds `refine`: shape and existing constraints
stay effective, and an additional diagnostic phase runs only after the full
original contract accepts. General laws characterize acceptance as conjunction,
preserve the exact original refusal report, and prove associative regrouping.
Gerbil uses its existing `=>` inherited computation, so this phase is rebound to
the effective descriptor even after preparing a parent. This is not an inference
that ordinary descriptor inheritance is subtyping. Custom MOP overrides must
still honor the structural protocol.

`Functional.EvidenceBinding` models the companion's existing `bind-evidence`.
It relabels the original formula into an `Option` atom space and appends a fresh
binding atom, preserving all original connectives and input/output policies.
Acceptance retains the original rule and exact subject/descriptor/context
associations. Under admitted input/output and a returned candidate, mismatch
refuses in the logic phase and publication retains exactly the old state.

The identity carriers must model reference identity; equality of serialized
records is insufficient. The model assumes a total pure projection. Actual Scheme
`eq?`, receiver preparation, projection exceptions and retry behavior have
separate executable controls. Matching freely constructed fields is not authority
or freshness. Bind from the original invocation template for a new context;
nesting bindings retains the earlier obligations, including obsolete ones.

The finite publication scenario is in `Examples/ObjectContracts.lean`; the Scheme
counterpart is `examples/contract-publication.ss`. It uses checked FUN admission
before state production, then the existing invocation publication protocol. The
original paper's section 5 supplies recognizers, type descriptors and I/O; these
explicit strengthening/binding operations advance Appendix B's future work and
the user's structural contract design. They are not claimed as original Racket
APIs, an authenticated receipt system or a proof of effect rollback.

## Nested Function validation and bound publication

The companion `object-contract-validation` now distinguishes structural recognition
from explicit validation. It recursively validates declared ObjectContract fields,
reuses existing Function wrappers and receiver-bound inherited specifications on a
fresh object, then checks full diagnostics and refinement on the checked root. No change retains exact identity; Function wrapping changes the candidate.
`checked-action` and `bind-evidence` use that actual returned root.

`FunctionValidation.lean` proves input/source/output gating and successful output
normalization, including function-valued output without decidable function equality.
`ObjectContractValidation.lean` supplies the finite ordered-batch backend laws;
`ValidationRebinding.lean` below models the receiver-bound dependency backend.
Both must finish before final refinement; representation laws remain explicit.
It proves final refinement on the normalized root and combines admission with the
existing binding theorem on application-supplied reference identifiers.
`Examples/ObjectContracts.lean` adds dynamic argument/result rows, higher-order
callbacks, normalized reference binding, raw/stale refusal and current retry.

Proofs cover total pure callbacks and finite declared batches. Representation laws,
reference/identity correspondence and immutability remain premises. Scheme tests
exercise actual wrappers and exception identity; neither layer proves the parser,
compiler/runtime, arbitrary cyclic object termination or rollback of effects.
Other container families, external schema adapters, optional/keyword arities,
wrapper deduplication and higher-order blame remain open. This extends the paper's future generalized
prototype work; section 5 supplies the Type descriptor recognition/validation basis.

## Container recursion and finite schemas

The existing Scheme List/Tuple Types now recursively call child validation and
return complete wrapped containers. A shared structural traversal checks proper
lists and exact tuple arity before normalization, follows nested ObjectContract
schemas without prematurely running their refinement, and records zero-based
indices in diagnostics. No source list/vector is mutated; unchanged containers
retain host identity. Named-field schemas are existing ObjectContract descriptors,
without a new schema DSL. Arbitrary external Schema Types need explicit adapters.

`LeanPoo/Functional/ContainerValidation.lean` reuses ordered traversal and the
object validation pipeline. Its nine laws cover successful position-wise
normalization/length, unchanged values, tuple arity and positions, final checked
acceptance, original child errors and schema refinement. The previously proved
`validated_binding` law applies to the exact final container reference.
`Examples/ContainerContracts.lean` composes a task list, finite schema, heterogeneous
tuple and Function list, including two returned values, sequential transforms,
refinement failure, malformed tuple, callback output rejection and raw/stale
reference refusal followed by current retry. Scheme exercises the corresponding
actual wrappers through JSON/FUN and bound publication.

The Racket `ListOf` in section 5 provides recursive membership; the new wrapping
composition advances future generalized-prototype work. Proofs interpret finite
pure callbacks, vectors as tagged rows and immutable identities as supplied IDs.
The fixture's named inventory is fixed by its Lean record type. Host representation,
parsing/runtime correctness, arbitrary external adapters, unannotated cyclic closure, wrapper
deduplication and higher-order blame remain outside these claims.

## Pair, Map, Sum and Union

The companion `variant-validation` now integrates the four existing Type
constructors with shared structural traversal. Pair validates both positions;
Map normalizes keys and values without changing the source, preserves the host
hash policy through `hash-new`, and refuses normalized-key collisions; Sum checks
tag before payload and installs the returned wrapped payload while inheriting its
source. Union recognition remains existential, while normalization commits to the
first structural branch and checks its own returned value. Selected errors cannot
fall through to a more permissive alternative. JSON dispatch is unchanged.

`LeanPoo/Functional/VariantValidation.lean` adds sixteen laws for components,
normalized map positions/length/collision checks, Sum tag/payload preservation,
ordered structural selection, unmatched branches and committed Union errors.
Final refinement and exact-reference publication reuse the existing object laws.
`Examples/VariantContracts.lean` composes Pair → map snapshot → Sum → Union →
refined Function schema and an approval callback. It covers active/data variants,
invalid tag, collision, Union fallback refusal, wrong output, root relation and
raw/stale evidence rejection followed by retry. The Scheme example uses existing
JSON/FUN and named route execution, without relying on host map traversal order.

The finite model requires table-key equivalence to agree with actual host hashing,
valid Type declarations, total pure callbacks and immutable reference mapping.
It does not prove Scheme identity/allocation, the hash implementation, JSON parser,
compiler/runtime or external effect rollback. Ordered committed Union validation
is not equivalent to existential membership. These are explicit future-work
extensions of the section 5 descriptor constructs, not a claim of whole-paper
completion. Other Type families, unannotated cyclic closure and wrapper deduplication remain.

## Sentinel optionals and TypeValuePair

The companion `optional-validation` extends Maybe, OrFalse and TypeValuePair through
existing Type/structural methods. Void and #f keep distinct representations; absent
branches do not even demand their child Type. Present validation locks the selected
child: a wrong Function result cannot become outer absence to evade checking.
Sentinel results remain legal when the child Type explicitly accepts them.
TypeValuePair now checks the carried Type, validates the payload rather than the
whole pair, and retains that exact Type alongside the actual normalized cdr.

`LeanPoo/Functional/OptionalValidation.lean` adds ten laws for sentinel identity,
shape/child errors, selected membership, complete acceptance, invalid descriptors,
descriptor retention and dependent payload success/failure. Existing ObjectContract
refinement and binding proofs provide the final composition. The worked Scheme
pipeline uses optional typed plugin rows and optional fallback through JSON/FUN,
refinement and exact binding. `Examples/OptionalContracts.lean` executes matching
present/absent paths, wrong carried interfaces, output refusal and current retry.

The typed fixture fixes its record/container grammar, uses descriptor/reference
tokens and supplies a pure host correspondence. It does not certify dynamic
parsing, host identity/allocation, compiler/runtime correctness or effect rollback.
This advances section 5 descriptor/generalized-prototype future work. External
schema adapters, unannotated cyclic closure and wrapper deduplication remain open; the I/O formats and executable-value serialization limitations are unchanged.


## Record and Class initialization through effective Slots

Scheme `class-validation` applies the same global structure → child normalization
→ final membership sequence to Class instances. Current effective Slot metadata
selects each inherited child Type. Present fields dispatch through `.slot.validate`;
optional absent fields bypass it. A receiver-bound batch forces every selected
field on one persistent derived object that preserves source ancestry. Final `.element?`
retains custom Slot checking and sealed/constant policies. The dependency-neutral
`value-diagnostics` module lets Class and containers share recursive diagnostics.

Existing `instance` / `.new` remain lazy construction. `make-instance` and
`.new/checked` validate defaults/overrides, pass the checked instance to the
initialization hook, then revalidate its replacement even when the hook returns
the same object. Bootstrap Type descriptor validation preserves exact identity.
Record's existing C3 metadata composition provides single/multiple inheritance;
new controls force parent prototypes first and exercise overrides and diamonds.
This is structural field inheritance, with no new nominal ancestry claim.

`examples/class-publication.ss` composes two inherited Record interfaces, optional
nested Function lists, a computed audit, checked initialization, JSON/FUN,
root refinement and exact `bind-evidence`. Controls cover bad argument/result
rows, custom Slot normalization/checking, hook mutation/replacement, raw/stale
evidence, source failure and independent retry. `ClassValidation.lean` proves
15 pure laws for optional/required presence, constants, child errors, selected
metadata, initialization order, final membership and inherited refinement.
`Examples/ClassContracts.lean` executes a corresponding finite service workflow;
existing normalization/refinement/binding laws supply the publication boundary.

This advances the paper's section 5 type-descriptor construction and generalized
MOP future work, rather than closing all future work. Inherited metadata resolution,
prototype defaults and host identity are supplied interfaces. Computed functions
in the original fixture capture unchanged scalar state; the computed-dependency
extension below adds final-self rebinding. Lexical snapshots outside that protocol,
unannotated cyclic closure, arbitrary callback termination and effect rollback are not proved.
Constant equality remains strict: wrapping that changes a constant's equality is
rejected, including such Function constants. Wrapper canonicalization/deduplication
and optional/keyword Function arities remain open. No validation cache is added.


## Receiver-bound computed dependencies

The paper's final-self rule (section 2) gives parent and child the same complete
receiver; section 5 supplies recursive recognition and callable/typed-slot Type
descriptors. `validation-rebinding.ss` now uses ordinary `$computed-slot-spec`
composition to normalize inherited results on that same checked receiver. Both
Class and ObjectContract use it. Computed fields capture checked dependencies
instead of freezing getter results from the old source. Existing receiver caches
share repeated reads, and existing `CyclicSlot` detects active cycles.

Global source structure is still checked before wrapping. A fresh private receiver
then preserves explicit instance assignments (without copying computed caches),
forces every selected field, and reaches final membership/refinement only after
success. Dependencies may force a later field first; declaration order is not a
promise for side-effectful validators. Slot `.slot.validate` now receives the
inherited raw value and final receiver explicitly, avoiding an implicit recursive
read of its own active field. If all selected values retain identity, the source
is returned. The normal publication chain binds only the actual returned root.

`examples/computed-publication.ss` combines Record metadata inheritance with an
explicit inherited instance prototype/super computation, a hook replacing backend
and bias, captured callable dependencies, computed Function lists, higher-order
results, root refinement and exact evidence. It does not add implicit super
semantics to Record Slot metadata. Tests cover parent pre-observation, repeated
admission, instance assignment/hook mutation, custom Slot dependency reads, cycles,
callback failure, raw/stale evidence and current retry.

`ValidationRebinding.lean` reuses `Prototype.Recursive` interactions and certified
memo receipts. Eleven laws cover bind/step semantics, checked aliases, dependency
and source errors, direct values, inheritance composition, memo agreement and
failed-batch refusal. The executable `Examples/ComputedContracts.lean` adds a
concrete checked-alias theorem and the same 46/8 service results, nested input
refusal, shared certified memo, initialized refinement and evidence controls.
Existing Class/refinement/binding laws remain part of the composition.

This advances generalized MOP future work. Correspondence of getter specifications,
assignment snapshots, memo caches and identity tokens to Scheme remains supplied.
Structural getters still run on the raw source during the first pass; arbitrary
getter/validator effects and callback termination are not certified. Explicit
lexical captures cannot be rebound, constant equality is not weakened, and cyclic
object closure, wrapper canonicalization and post-admission mutable freshness are
not proved. Revalidate after revision; this is not an accepted-value cache or a
runtime/GC/performance proof.


## Controlled recursive objects and computed cycles

`recursive-validation.ss` closes a finite, explicitly named catalog of
`(name descriptor source)` declarations. A builder receives the current graph's
Reference-Type constructor. Source fields may contain real object backedges;
Reference Types recognize only the named source/canonical receiver and cut
structural recursion. Every named target is independently checked, including
unobserved nodes. There is no rule accepting an active node as already valid.

The phases are whole-catalog shape admission, allocation of all canonical
receivers, receiver-bound field normalization, then whole-graph admission.
Class and ObjectContract share `.validation-fields`, `prepare-rebinding` and
`force-rebinding`. Their nested whole-value obligations are deferred within this
closure attempt until all node batches finish; failures discard the pending queue.
Ordinary validation still checks immediately. A nested graph attempt owns its own
queue and owner. Cross-owner Reference descriptors cannot silently join graphs.

`closed-ref` and `closed-type` expose only a completed graph. Canonical nodes and
Reference Types are sealed through supported APIs. Registered source, descriptor,
Reference-Type and canonical-node revision stamps gate graph access and Reference
validation; explicit later Reference validation rechecks graph admission while
retaining canonical identity. Fresh attempts build fresh owner-scoped descriptors.
The node-count limit bounds catalog size, not arbitrary callback execution time.

`examples/recursive-validation.ss` composes a two-node object cycle with computed
peer-handler capture, Function argument wrappers, the existing positive least
closure (`left = true OR right`, `right = left`), safe decreasing recursive
requests and shared memo, Reader/FUN, root `refine` and `bind-evidence`. The workflow
returns 10 + 8 = 18 and proves neither arbitrary eager fixed points nor implicit
termination of cyclic method calls. Immediate computed getter cycles still reject
with `CyclicSlot`; recursive machine budget/cycle diagnostics are not values.

`Functional.RecursiveValidation` proves eleven finite catalog/graph laws: named-catalog preflight, successful
collection at every position, finite completion, three phase-failure laws, complete
shape/payload/final obligations, canonical edges/sharing/distinctness and bound
root evidence. `Examples/RecursiveContracts.lean` adds a concrete two-hop backedge
law and executes matching positive closure, memo/Function guard, refusal and
fresh-owner publication controls. Existing final-self, certified recursive memo,
positive least-closure, refinement and binding proofs are reused.

This advances generalized MOP future work. The finite catalog interpretation,
canonical host identities, receiver preparation, deferred callbacks, sealing and
revision-stamp correspondence remain supplied interfaces/local Scheme controls.
There is no universal coinductive Type checker, automatic graph discovery,
unrestricted recursive container validation, arbitrary lexical capture rewrite,
implicit invocation of construction hooks, proof of host callback termination,
concurrent mutation, or external-effect rollback. Retained arbitrary Functions
are not globally revoked by a later source edit; use immutable sources and a
fresh closure/publication after revision. Raw structural getters still execute
before wrapping. Constants retain strict equality; wrapper canonicalization is
separate work. Scheme has no runtime dependency on the Lean checkout.

## Recursive graph revision

`Functional.RecursiveRevision` combines existing certified consumer-to-dependency
reachability and all-or-error `RecursiveValidation.close`. New laws establish
clean dependency closure, shared invalidation, callback selection, local generation
preservation/advancement, rejection of earlier target generations, all-node final
admission, pure failure-state retention and current canonical-root evidence.

`Examples/RecursiveRevisions.lean` uses five nodes: a shared provider, two cyclic
services, a computed report and an independent cached node. A shared edit rebuilds
four nodes (report 23); the following peer replacement rebuilds three while retaining
provider/idle (report 30). Actual checked Function calls, Boolean argument refusal,
whole-value refinement, clean-node final refusal, old subject/context rejection and
current evidence retry are executable controls. Gerbil's matching recipes also
exercise source/descriptor watches, old-Type injection, removal and reentrant
competition. `revision-action` composes with FUN; the existing publication action
owns exact subject/descriptor/context `bind-evidence`.

This advances generalized MOP future work beyond the paper's Racket final-self and
Type descriptor constructions. Complete declared reads (including computed captures
and obligations), unchanged source/descriptor correspondence, consistent finite
indexing, canonical host identities and sequential installation are explicit
premises. Host membership/index relowering, concurrent mutation, arbitrary retained
Function revocation, callback termination, external-effect rollback and Scheme
compiler/runtime/GC behavior are outside these proofs. Scheme builds independently
of a Lean checkout. No timing or allocation improvement is claimed from these laws.

## Named recursive catalog migration

`Functional.RecursiveMigration` extends the fixed-index model with checked finite
names and actual index lookup/lowering. Ordered edges retain duplicate shared
aliases. Clean names preserve canonical identity when component removal shifts
rows; removed names refuse and their logical epoch tombstones prevent same-name
revival after readdition. Additions normalize even if an old total cache has a
latent outside-support value. Named footprint/new/body seeds reuse the existing
positive Boolean least closure, with fixed-equation, leastness, finite height,
reader propagation and clean dependency laws. Complete current admission composes
with exact bound-root evidence.

`Examples/RecursiveMigrations.lean` executes the matching Gerbil six-round workflow:
19→35→35→19→27→33, including peer SCC/provider migration, deletion/readdition,
index movement, late refusal/retry, computed-only rebuilding, checked Function
refusal, root refinement and stale subject/context evidence refusal. Gerbil's
`reconfigure-validation`/`reconfiguration-action` reject ambiguous edits before
builders and reuse the same canonical closure engine. Equal-output computed
reader replacement is also a Scheme control.

This advances generalized MOP future work. Mathematical named/index lowering is
proved here; Scheme host/source identity correspondence, complete declared reads,
custom Type laws, terminating callbacks and sequential mutation are premises.
Gerbil uses fresh identities and permanent old-reference revocation to implement
the logical epoch boundary. This does not certify runtime/compiler/GC behavior,
arbitrary eager computed fixed points, automatic dependency discovery or atomic
transactions combining graph commit with external FUN effects.

## Interleaved recursive SCC topology

`Functional.RecursiveTopology` adds fourteen laws to the existing least dependency
invalidation: deleted edges seed their consumer, so invalidation also follows every
old path; both old SCCs after splits and new SCCs after merges remain atomic. Clean
nodes preserve reads, old/new paths and exact checked membership. Changed SCC
membership thus implies dirtiness without computing SCCs on the construction path.

`Examples/RecursiveTopologies.lean` matches eight Gerbil services through seven
rounds: two simultaneous merges, two splits, crossed merge refusal/retry, original
group restoration, computed-only selection, then one-pair body revision. Totals
82→108→128→132→127→134→135 accompany exact SCC checks, persistent old-reference
refusal, root refinement and current bound evidence. Independent pairs, provider,
computed reader and idle retain identities whenever their declared closure is clean.
Gerbil's `closed-reads` and `recursive-topology` module provide optional checked
partition receipts; membership comparison treats groups as sets and never grants
cache authority or skips final approval.

This advances generalized MOP future work. Proofs use a common finite name
embedding; named membership/index changes reuse `RecursiveMigration`. The example
reserves inactive provider vertices for old/new comparison and guards exposure by
current membership, so it makes no host allocation/cost claim. Complete declared
reads, immutable metadata, host source/identity correspondence and sequential
mutation remain premises. Arbitrary eager computed fixed points, concurrent
installation and atomic external-effect transactions are outside this result.


## Deferred recursive revision requests

`recursive-staging.stage-reconfiguration` captures edit list spines, the exact
current graph and the versions of proposed recipe watches. It returns a FUN Reader
action. Staging runs no builders, normalizers, computed getters or admission
callbacks, and allocates no candidate graph. Graph identity and complete input
versions are checked before the action invokes existing `reconfigure-validation`.
A sibling commit invalidates all requests from the old snapshot even if every
node Reference remains valid. A proposed watched input can invalidate a request
without any intervening graph commit. Stage again from the actual current graph
and input versions; closure refusal leaves that graph and its References current.
The request can be retried after refusal only while its exact checkpoint remains
current; it grants no reservation or reusable approval of later states.

Gerbil `examples/recursive-staging.ss` composes guarded revision, whole-value `refine` and
existing `bind-evidence` through `Observation.` bind. Tests interleave multiple
requests across seven actual graph states: simultaneous SCC merges/splits, shared
provider addition/removal/migration, crossed merge refusal/re-staging, restored
SCCs, computed-only edits and local-pair reclosure. Obsolete requests refuse across
all later rounds; dirty old References do not revive when groups return. Extra
controls cover proposed-watch drift before any builder, copied edit list spines,
and a no-rebuild commit that retains all nodes but still expires sibling requests.
The combined publication action returns the installed graph separately from effect
success/refusal. A later effect-policy refusal preserves the old effect context;
it does not undo the completed graph revision. Fresh evidence can then retry on
that installed graph.

Lean `Functional.RecursiveStaging` proves eight laws: revision/stamp refusal,
closure failure preservation, fresh re-staging success, exact revision advance,
all-refusal preservation, sibling invalidation and permanent old-round rejection.
`Examples/RecursiveStaging.lean` uses actual selective reclosure, epochs, checked
Functions, SCC inspection and the existing refinement/evidence models. A logical
monotone revision corresponds to exact Scheme graph identity, and logical stamps
to complete watched input versions; those correspondences are explicit premises.
This advances the original text's generalized-prototype future work. Complete
reads/watches, immutable metadata, trusted terminating callbacks and sequential
mutation remain required. No automatic read discovery, concurrent CAS, side-effect
rollback or atomic graph-plus-effect transaction is claimed.


## Class full-suite resource diagnosis

The Scheme single-process failure was reproduced with the unchanged 1G heap.
All-module source import retained about 927 MB of latest-GC live data before the
first test. Failures moved between Class multiple inheritance/diamond and dense
closure; the Class-only all-import control and 1,000 independent repetitions in
both natural and controlled GC regimes passed. The dominant avoidable load is the
release expander retaining all source-module expansion contexts, not evidence of
leaked Class admission state. Loading the compiled interfaces observed about
117 MB initially and at most 154 MB at module boundaries in the diagnostic run;
these are local latest-GC observations, not peak RSS or a performance proof.

Gerbil now compiles the checked test inventory and its helper dependencies with
standard `std/make`, then passes the compiled interfaces to the original `gxtest`
harness. All cases, fixtures, order, the 1G heap and existing deadlines remain.
The runner does not insert GC or alter interpreter state. Existing test cases now
snapshot mutable traces/counters in explicit lexical sequence; no expectations
are relaxed. New Class controls exercise warmed diamond metadata, failed cyclic
admission and fresh checked-Function retries in both GC regimes. Independent CI
jobs remain, and an additional job executes the full suite in one process from
the same exact-source compiled artifact.

This repairs test loading and test observation ordering. The supplied Class,
recursive-validation and inheritance proof interpretations remain unchanged; this
is not a new compiler/GC verification obligation for the original paper. See the
companion `doc/test-execution.md` for the controls and evidence boundaries.


## Explicit preparation with older requests still pending

`recursive-staging.restaging-action` lifts a FUN Reader of three edit lists
(additions, removals, replacements) into a Reader of guarded requests. Each
explicit invocation computes edits against the actual current catalog, then uses
`stage-reconfiguration` to capture that graph identity and all proposed watches.
Preparation does not build a graph, reserve publication or rewrite old requests.
Preparation exceptions produce no request; closure refusal preserves the current
graph. Retry consists of running preparation again, then publishing the new
request through the existing guard. Preparation must terminate locally and leave
the installed graph and metadata immutable.

`examples/recursive-restaging.ss` derives provider additions/removals from current
membership using standard map/filter, retaining the existing service, checked
Function, computed summary and publication recipes. Eight rounds merge/split SCCs,
migrate shared dependencies, restore primary-only membership, reintroduce the same
secondary recipe, and change computed readers/local bodies. Each round prepares new
requests while historical requests remain pending, attempts historical work,
refuses late admission, explicitly prepares again, and publishes through the
existing whole-value `refine` and exact `bind-evidence` FUN chain. Old requests are
attempted again after installation. Historical graph/reference capabilities never
revive when old names and groups return; an independent node retains identity.

Lean `Functional.RecursiveRestaging` proves preparation failure, exact new request
capture, successful prepared publication, refusal followed by retry, preservation
under any finite list of obsolete attempts, and successful fresh publication
interleaved with old attempts on both sides. `Examples/RecursiveRestaging.lean`
runs the same eight actual selective closures and checks old-reference rejection,
current refinement and wrong-context refusal followed by exact-evidence retry.
These extend the generalized-prototype **future work**. Exact graph identity and
complete watched-version correspondence, explicit dependency footprints, pure
locally terminating preparation/closure and sequential attempts remain premises.
The list theorem describes serialized observations; it proves neither concurrent
host installation nor atomic graph/effect rollback or arbitrary callback effects.


## Multiple entry points sharing one recursive graph

`recursive-publication.publication` creates one sequential handle for a checked
recursive graph. All entry points use `current` and `stage-with` on that handle;
there is one authoritative installed graph, rather than private per-entry heads.
`stage-with` accepts the existing FUN restaging Reader. `submit!` invokes its guarded
request and records a successful new graph before calling the entry observer.
Graph rejection leaves the head untouched and never invokes the observer.

`observe!` runs a fresh observer over the current graph without reconstructing it.
An entry's refinement, evidence or policy refusal therefore cannot resurrect the
retired graph; it can retry observation against the installed graph with its own
unchanged context. Exceptions also release the operation guard and keep any graph
already installed. The guard rejects nested preparation/publication before user
callbacks run. Access must be serialized by the caller: the guard is not a thread
lock, and each revision family must use one handle. Graph requests must be existing
guarded staging actions. Callbacks must return locally and leave graph metadata
immutable outside supported operations.

`examples/recursive-publication.ss` composes existing service `refine` and exact
`bind-evidence` observers with per-entry contexts. Three entry points rotate across
eight actual revisions: simultaneous SCC merges/splits, shared provider migration,
provider removal/reintroduction, computed-reader changes and a local SCC body edit.
Fresh requests are prepared while historical generations remain pending. Late
closure refusal is followed by explicit restaging; after installation, policy
refusal is followed by an effect-only retry. Requests from all other entries and
prior rounds refuse; old dirty References never revive. Foreign entry contexts
refuse at the exact evidence gate; independent-node identity is retained. Separate
controls cover real refinement exceptions, observer exceptions and reentrant calls.

Lean `Functional.RecursivePublication` proves eight laws: observation preserves the
shared graph; observation refusal preserves the whole world; other entry contexts
are preserved by observation and submission; graph rejection prevents effects;
late effect refusal retains the new graph; successful reclosure remains installed;
and all sibling requests expire regardless of the winning entry's effect outcome.
`Examples/RecursivePublication.lean` runs the same eight actual selective closures
with distinct entry contexts, current refinement, evidence transplant rejection
and effect-only retry. The shared contexts are explicit caller state, not stored
inside the Scheme handle.

This advances the original generalized-prototype **future work**. Complete declared
reads/watches, exact graph identity/version correspondence, immutable metadata,
trusted terminating callbacks and sequential installation remain premises. There
is no claim of concurrent CAS, arbitrary callback-effect rollback, or atomic graph
and external-effect publication. The finite model does not verify Scheme runtime
or compiler internals.


## Shared approval metadata and graph revisions

`recursive-publication.snapshot` now captures the graph and metadata together.
`publication(graph, metadata:)` initializes this pair; existing graph-only readers
and operations retain their API and preserve installed metadata. New read-only
`snapshot-graph` / `snapshot-metadata` projections, `stage-joint-with`,
`submit-joint!` and `observe-joint!` operate on one captured pair. Installation is
one private snapshot-pointer replacement, before later entry effects. Access stays
caller-serialized; the busy guard rejects reentrant writes.

`recursive-approvals.stage-with` prepares against that exact whole snapshot and
captures existing lens revision guards for installed and proposed approval POO
objects. These guards reject changed versions even when values change back, and
prevent supported metadata writes during preparation, closure and admission.
Untracked interior mutations and hidden callback dependencies remain unsupported.
`submit!` installs the admitted pair before the entry observer; `observe!` retries
only refinement/evidence over a consistent current pair under the same metadata
write discipline. Observer refusal keeps the pair and the old entry context.

The existing recursive closure accepts `admit:` at its revision/reconfiguration
and staging boundaries. The callback receives a complete locally normalized and
admitted candidate, with canonical nodes sealed. It must return exactly `#t`.
Joint refusal occurs BEFORE predecessor retirement or dirty Reference revocation.
The attempt moves to its existing failed phase: leaked candidate graph access and
new Reference capabilities refuse, while reused clean predecessor capabilities
remain valid. This reuses selective closure and its dependency propagation, rather
than building an independent graph engine or undoing a committed graph afterward.

`examples/recursive-approvals.ss` uses per-entry ceilings, a stricter joint budget,
existing computed-shape refinement and checked Function recipes. Three entries
rotate through eight SCC/provider/computed rounds. Every round checks local success
with joint refusal, preserved old pair/references, rejected failed-candidate
capabilities, separate installed/proposed metadata ABA drift, explicit restaging,
late effect refusal and exact bind-evidence retry. Historical requests remain
pending across rounds. A ninth approval-only revision reconstructs no nodes and
retains canonical References, but still expires old whole-snapshot requests.
Supported approval writes from an admission callback refuse before mutation.
A final captured-version recheck also rejects a callback that changed a proposed
recipe watch before retirement; the external write persists, while the old graph
remains usable and fresh staging can retry. Callback effects are not rolled back.

Lean `Functional.RecursiveApprovals` proves eight composition laws: construction
refusal, joint refusal, exact successful pair, whole-state preservation, one-step
pair publication, metadata guard refusal, cross-round sibling invalidation and
late effect refusal retaining both installed projections. Its executable example
uses the same nine actual finite graph/approval states and per-entry contexts.
This extends the original generalized-prototype **future work**, under complete
registered versions/dependencies, exact host identity correspondence, lawful guard
operations, immutable-in-use metadata, locally terminating callbacks and serialized
access. It does not establish concurrent CAS, arbitrary effect rollback, or atomic
graph-plus-external-effect publication, and does not verify runtime/compiler code.


## Interleaved joint requests and repeated approval invalidation

`recursive-approvals.submit-sequence!` accepts an ordered list of `(request . observer)`
procedures. It preflights and copies every row before the first publication, then
uses standard `foldl` to invoke the existing guarded `submit!` once per row. It
continues after exceptions and preserves every attempt in input order. There is no
automatic restaging, reapproval or transaction across the sequence.

Read-only attempt selectors expose the original request, that attempt's actual
post-attempt snapshot, all returned observer values, an explicit `attempt-failed?`
flag and the original exception payload. The flag distinguishes a raised `#f` from
normal `#f` or zero return values. A normally returned metadata/effect refusal stays
in the returned values; it is not relabelled as an exception or accepted effect.
An observer exception after successful graph installation records the installed
pair, and later rows still attempt against that pair. Historical snapshot references
are observations, not renewed approvals or frozen copies of mutable metadata.

`examples/recursive-competition.ss` reuses current/future policy objects and the
existing joint-approval/service observers. Eight actual SCC/provider/computed
rounds retain a losing future proposal for explicit preparation in the next round.
Within each round, two requests share a proposed policy; proposed-policy ABA first
invalidates both. Freshly staged current/future requests then expire AGAIN after
installed-policy ABA. Explicitly prepared fresh requests compete only after these
two windows. Local success/joint refusal leaves the predecessor usable; a winner
installs despite later effect refusal, and the future challenger plus a replayed
winner refuse as stale. Historical requests remain interleaved on both sides.
Fresh `refine` / exact `bind-evidence` observation retries against the installed
pair, preserving the other entries' contexts and rejecting dirty old References.

Controls also retain an installed head after observer exceptions, continue to the
next stale request, reject a malformed queue before any publication, prevent an
observer rewriting the original queue from replacing later copied requests, and
distinguish false exceptions from normal false/zero values.

Lean `Functional.RecursiveCompetition` proves eight sequence laws: one receipt per
attempt, graph-refusal continuation, late-effect-refusal continuation with the
installed graph, exact preservation under an obsolete batch, single-step and
finite-sequence revision monotonicity, permanent historical request rejection and
invalidation of all same-or-earlier-round challengers after a winner. Each formal
submission carries its own observed stamp and entry effect. The executable example
uses the same eight actual graph revisions and competing future intentions, reusing
`Examples/Support/RecursiveApprovals.lean` for the existing checked service fixture.
That fixture is shared with the preceding joint-revision example; executable checks
remain in top-level `Examples/`.

These extend generalized-prototype **future work**. Native snapshot/guard identity
correspondence, complete registered reads and versions, immutable-in-use metadata,
caller-serialized attempts and pure locally terminating formal effects remain
premises. Host exception and queue-alias controls are separate Scheme evidence.
No concurrent CAS, arbitrary callback rollback, runtime/compiler verification or
whole-sequence atomicity is claimed.
