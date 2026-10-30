# Using the property-testing modules

The generic modules live under `testing/property`, within the ordinary POO
package build. Run `gerbil build` from the package root. They import only the
Gerbil standard library; typed derivation stays in `testing/type`.

Import the modules you use directly:

```scheme
(export arithmetic-test)
(import :std/test
        (prefix-in :clan/poo/testing/property/generator generator.)
        (prefix-in :clan/poo/testing/property property.))

;; Draw and shrink signed integers with one explicit random source.
(def integers
  (generator.make-generator
    (lambda (random size) (- (random (+ (* 2 size) 1)) size))
    generator.integer-shrinks))
;; Domain admission and shrink measure are supplied by this application.
(def integer-domain
  (property.make-specification exact-integer? abs))

;; Standard Gerbil TestSuite discovery owns execution.
(def arithmetic-test
  (test-suite "integer arithmetic"
    (test-case "addition identity"
      (check (property.report-status
        (property.check-property integers (lambda (x) (= (+ x 0) x))
          integer-domain seed: 42 cases: 100 size: 50))
        => 'passed))))
```

The example is exported as a normal `*-test` suite for `gerbil test` discovery.
See `examples/property-kernel.ss` for dependent packets, non-injective maps,
lazy bounded shrinking, source invalidation and a model with logical handles.
`testing/property/model.ss` owns model execution and repair; it does not instantiate
a POO object or prescribe an application representation.

POO users import `:clan/poo/testing/type` for descriptor-driven generators and
reports, `:clan/poo/testing/function` for signature derivation, and
`:clan/poo/testing/recursive-generation` for bounded recursive derivation.
Those modules own Type validation, wrapping and revision observations. They
supply these operations to the generic library through explicit callbacks.
There is no `api.ss` forwarding module or alternative dynamic import mechanism.

A generator's shrink callbacks must preserve its intermediate domain. The final
specification additionally checks domain admission, a natural-valued measure and
strict Boolean properties. Reports distinguish failure, errors, stale sources
and exhausted generation. Shrink fuel counts forced proposals, including rejected
ones; zero fuel does not invoke a shrink callback. A minimum refers only to an
observed exhausted immediate neighborhood, not a globally smallest value.

Seed replay regenerates under the recorded configuration; concrete replay checks
the retained witness without drawing or shrinking. Mutable callback dependencies
must be declared through accurate source observers. The isolated regression builds
the actual generic package and executes twelve cases without any POO modules in
its package directory, under the existing heap and timeout limits.

Model normalization is an explicit boundary: `check-trace` first prepares the
entire command list and executes exactly those normalized objects. Its mismatch
report carries the prepared command. A late domain/precondition refusal or
normalization exception opens no fixture. `valid-trace?` projects the same
preparation; do not use it as a substitute for `check-trace`'s own preflight.
The POO facade supplies already-wrapped commands with identity normalization.

Interrupted shrink reports retain the last confirmed witness and charged work.
A returned proposal counts even when admission, cost, property or source checks
fail; EOF and an iterator exception produce no proposal. The error's cause is
retained, `minimal?` is false, and concrete replay requires a `failed` report.
A diagnostic reduced value on an `error` or `stale` report is not certified evidence.

## Composable generator proof boundary

`LeanPoo.Functional.PropertyTesting` now also has the functionally separated
`LeanPoo/Functional/PropertyGenerators.lean` module. `weightedChoice_member` and
`weightedChoice_exists` cover positive-weight membership and all valid finite
offsets; they do not establish a host random distribution. `scheduledSamples_size`
and `scheduledSamples_length` retain actual size/trial ownership. The
`resolveDelayed_budget` law bounds callback requests, conditional on each pure
step returning. `shrinkProposals_budget` and `shrinkProposals_preserves` charge
pruned proposals while retaining the last valid false witness.

The top-level `Examples/PropertyGenerators.lean` checks weighted boundaries,
size schedules, zero fuel and pruned-child accounting. Existing mapped-preimage,
dependent-selection and stale-observation laws remain the provenance premises.
These are finite source laws; runtime PRNGs, callbacks and backend representations
still require their own executable admission. Scheme imports no Lean checkout.

Bind regeneration now reuses invocation-owned SRFI-27 initial-state checkpoints.
Every regenerated child still receives a fresh source and executes its selector
and draw; no generated value, sample tree or source observer is memoized. Nested
binds share only seed preparation. Public source lists remain detached, while
empty/identical internal owner joins can share immutable lists.

`PropertyGenerators.lean` proves seed-cache content/insertion invariants and
regeneration equivalence, including variable-length consumed states and first
failure, under an explicit state-restore law. `checkpointExpansions_le` is an
operation-count bound. Scheme regressions exercise the installed runtime's
checkpoint isolation; these laws do not establish PRNG quality, callback
termination, heap allocation, GC timing or an elapsed-time bound.

## Coverage, portable replay and finite function laws

`Functional.PropertyTesting` now models the next three finite PBT protocols.
`recordTrial_accounting`, `discarded_labels`, `auditTrials_attempts` and
`bounded_trials` establish generation accounting. `coverageAdmitted` reads counts
from the ledger's actual label list; `all_discard_refused` and `coverage_threshold`
prevent fabricated success from absent effective trials or unmet requirements.
Per-trial labels are normalized by the Scheme boundary before this finite model.
Shrinking records no generation event and cannot inflate this ledger.

`replay_identity_refused` and `replay_refused_before_fixture` require identity
admission before decoding or fixture binding. `replay_roundtrip` is conditional
on the application's codec law. It does not certify a host reader, serializer,
callback or stored-code evaluator; the Scheme protocol persists finite data only.

`unknown_function_row` refuses a missing finite argument row without a fallback.
`mapped_function_lookup` shows that result-only mapping preserves row selection
and transforms its selected result. Output may itself be a multiple-value tuple.
`Examples/PropertyGenerators.lean` supplies positive and negative controls.
Keyword interpretation is represented by explicit row data, not an unproved
claim of equivalence between unrestricted call languages or effectful procedures.

The generic Gerbil implementation remains independent of Lean and POO. POO owns
Function validation and descriptor/source revisions; these finite laws guide the
protocol rather than serving as runtime certificates for arbitrary callbacks.
This advances the paper's future work; it is not a claim that its Racket code
already implements these testing protocols.

## Standard test admission

`CheckStatus`, `checkedStatus` and `admitCheck` model translation from a finite
property report to a standard successful/error check. `admitCheck_ok` requires a
passed report and current sources; `checkedStatus_preserves_nonpass` preserves
coverage refusal, exhaustion, unsupported generation and callback errors.
`admitCheck_preserves` retains named argument data and original cause identity.
`productDomain_sound` and `productDomain_length` model fixed multi-argument domain
admission, including refusal of missing/extra positions. The new controls live in
`Examples/PropertyGenerators.lean`.

The Gerbil implementation delegates check registration/location/failure handling
to `:std/test`; it adds no runner. These laws do not prove the installed CLI's OS
exit code or turn callback exceptions into property falsifications. Generator
branches may depend on earlier argument values; per-value type inference remains
outside the fixed-specification interface.

## Reusable data family laws

The independent Gerbil algebra now supplies bounded integers, Unicode scalar
characters, octets, lists, strings, symbols and byte vectors. POO String, Symbol,
Bytes and BytesN reuse it; there is no Char descriptor invented for this feature.
`intervalValue_bounds` and `intervalValue_shrink` prove explicit interval admission
and decreasing offsets. `scalarCode_valid` and `scalarCode_strict` prove surrogate
exclusion and monotone scalar decoding. `dataLength_bounds` and `dataLength_fixed`
prove suffix bounds and size-zero fixed widths. `dataCarrier_domain` states the
representation obligation explicitly, rather than certifying runtime packers.

Scheme regressions exercise mixed Unicode/byte replay with the existing codec
identity/currentness and byte-budget refusal. These laws do not prove PRNG
uniformity, symbol interning, callback termination, arbitrary mutation purity,
or Gerbil's write/read implementation. This advances the paper's future work.

## Bounded generator inspection

P6 uses the existing Gerbil property module and typed sampler bridge. It observes
one owned random source and the existing lazy sample tree without running any
property or contributing coverage. Flat path events distinguish admitted roots,
decreasing children, domain refusals, nondecrease and pruned proposals. Count,
depth and one global proposal quota bound observations. Shared `next-proposal`
charges returned tombstones and stale-after-return values; EOF/throws are free.
Cutoffs leave neighborhoods unforced, so truncation is conservative, not minimality.

`inspectionAdmission_sound` proves domain membership and descent without a
falsity premise. `inspectionWalk_budget`, `inspectionWalk_zero`,
`inspectionWalk_depth_zero`, `inspectionWalk_depth`, and `inspectionEvents_budget`
prove finite worklist bounds and expansion independence. The depth annotation
abstracts the host path length minus its root index. Refused/tombstone proposals
have empty expansions. These are finite protocol laws, not a verification of
callback termination, PRNG distribution, or Gerbil iterators. Host interruption,
source guards, independent compilation and dependent packet replay are regressions.
This advances the paper's future work without a new execution framework.

## Default POO property checks and debug actions

The Scheme developer workflow now uses the existing `support/testing` standard
checks, PropertyConfiguration Record, property Reader/FUN action and DDT renderer.
There is no extra test runner or import-time generation. Record field validation
and finite runner validation keep distinct ownership. The configuration itself
is now a revision source, so a successful callback cannot admit an edited run.

`configuredCheck_ok` requires a passed/current report and equal configuration
revisions. `configuredCheck_preserves` retains original cause and named arguments
on refusal. Existing `productDomain_sound`/check admission laws cover fixed named
Type products. `configurationLimit_explicit`, `configurationLimit_fixed`, and
`configurationLimit_procedure` state finite-bound selection without inventing an
implicit bound for procedural sizes. `debugDelivery_report` and
`debugDelivery_disabled` preserve the original report and bypass the renderer
when disabled. The renderer-return premise does not certify host I/O; DDT's
formatter/I/O behavior and Gerbil CLI exit propagation are outside these proofs.

## Retained collection deletion

P8 replaces length-driven payload regeneration and typed empty/tail-only removal
with one retained sample-sequence policy. Aligned blocks halve to singleton
positions; only List/nullable carriers permit deletion. Pack callbacks remap
retained values while every originally visited source remains observed.
`deleteBlock_length` and `deleteBlock_bounds` prove exact length decrease/minimum
bounds; `deleteBlock_sublist` proves retained order and membership;
`deleteBlock_map` preserves mapped preimages; `retainedSources_keep_deleted`
retains historical observer identities. Callback purity/termination and the
host's allocation/runtime behavior remain explicit premises. No global minimum
is promised. Typed value-only batch preparation retains its existing search cap.

## Source-consistent portable replay stages

P9 uses `replayStage` in `Functional/PropertyGenerators` to model the existing
codec/domain observer brackets. `none` denotes a stale refusal; `some cause`
retains the exact application exception. `replayStage_preflight` refuses without
evaluating the callback; `replayStage_cause` preserves exceptions despite a later
revision; `replayStage_stale` rejects a normally returned stale value;
`replayStage_current` preserves an admitted value; and
`replayStage_refused_before_delivery` skips the next stage after any preparation
failure. Scheme applies those boundaries separately to encoding, decoding and
property execution, reusing the existing runner and typed sampler snapshots.

The downstream Record example restores nested Function fields through ordinary
construction and refuses revisions before property effects. Regression controls
also cover zero output prefix on preparation refusal, callback cause identity and
cleanup. These finite laws assume accurate, terminating observers/callbacks.
They do not prove arbitrary codec round trips, host port transactionality, thread
atomicity, parser allocation bounds or process/GC behavior. A host write failure
can leave partial bytes; durable file installation belongs to its application.

## Shared concrete-witness admission

P10 factors precondition/domain/property execution into the existing property
module's `check-counterexample`. In-memory and portable replay share it. Every
callback is guarded separately, so a source revision during precondition checking
cannot invoke a recognizer or open a property fixture. Portable import accepts an
explicit `policy:`; its precondition is enforced without generating a trial or
classifying coverage. Required generation coverage cannot reject a concrete
Boolean result. Application identity must include the policy interpretation.

`admitWitness` and `checkWitness` in `Functional/PropertyGenerators` compose guarded
Boolean judgments using the existing `replayStage` result. Finite laws prove
precondition/domain refusal skips later callbacks, stale judgments and application
causes remain distinct, and admitted replay returns the property's exact Boolean.
These assume truthful terminating observers/callbacks; they do not certify arbitrary
host predicates, codec equivalence, resource cleanup implementations or I/O atomicity.

## Source-current generator callback composition

P11 uses one hygienic `with-sources` form in the existing generic generator
module. It checks the declared flat observer list before and after normal callback
return, preserving original exceptions. Producer draw, mapping, dependent selection,
dependent child drawing, sized/delayed construction and retained sequence packing
use this same boundary. A selector revision cannot invoke its selected generator;
a child draw that revises an inherited parent source cannot deliver its result.
No per-node guard closure, new runner or source registry is introduced.

`guardedGeneration` models a callback's returned value and resulting source/random
state. Its five laws establish preflight refusal, post-callback revision refusal,
cause preservation, exact admitted value/state and suppression of dependent stages
after refusal. Existing source-union laws retain historical branch ownership.
Accurate pure observers and terminating callbacks remain premises. Effects already
performed inside a failing callback are not rolled back, and these laws do not
establish concurrent linearizability, PRNG distribution or host timing guarantees.

The standalone regression matrix exercises seven callback positions. The downstream
Record/FUN example refuses construction after a selector revision, explicitly
prepares a fresh sampler, performs actual shrinking, then verifies concrete replay
performs no draws and seed replay repeats the complete construction schedule.

## Finite-key hash and typed Map generation

P12 adds finite partial maps to the existing tree algebra. `selectedHashKeys`
models filtering the declared key domain and capping retained entries by size.
The sublist, size/domain bounds and Nodup laws establish that fixed keys introduce
no collision. `hashEntries_lookup` distinguishes a present false-like value from
absence; `hashEntries_delete` commutes structural deletion with retained entries;
`hashEntries_map` preserves keys under value transformation/wrapping. Existing
block-deletion, guarded-stage and source-union laws continue to apply.

The Scheme kernel uses Gerbil's ordinary HashTable equality for one-time finite
domain admission, and `list->hash-table` for fresh materialization. Only retained
value nodes are drawn; structural deletion does not regenerate them. The typed
`map-generator` checks representation-preserving key validation, exact value
sampler descriptor identity and preparation source epochs. Its existing Map
validator owns nested Function wrapping. The existing currentness hook is forwarded
through application-derived Record samplers in the downstream example.

Hash packing/lookup correspondence assumes lawful host equality/hash behavior,
stable key payloads and accurate source observers. Value callbacks and custom
validators must satisfy their declared contracts and terminate. No arbitrary key
inference, key mutation/normalization proof, stable hash traversal order, constant
hash lookup time, GC bound or compiler verification is claimed. Accepted domain
preparation scans at most its explicit key limit; nonzero roots test every key
and draw at most min(size, domain length) values. Each fresh packed/validated node
still has work proportional to its retained entries plus callback costs.

Finite declared alternatives use `generator-elements`, for example
`(generator-elements '(read write admin))`. Its lazy index tree simplifies toward
earlier declarations without redrawing. Use an explicit natural rank in a generic
specification. POO `Enum` derivation supplies its existing first-occurrence index
as that rank, including nested collections and replay. Empty Enum is uninhabited;
an empty generic alternatives list is a constructor error.

Generic model users supply `(shrink-trace model commands shrink-command)` from
`:clan/poo/testing/property/model` as their ordinary generator's shrink callback.
It shares collection block/coordinate proposals, then repairs dependent commands.
POO `trace-generator` uses the same policy automatically. No draws or actual
fixture transitions run during candidate preparation; model callbacks remain
explicit and finite. The runner still checks each repaired proposal's domain,
strictly smaller measure and falsification before accepting it.

Policy preconditions and each fixed product field are separate source-checked
stages. A precondition that revises a declared dependency stops before property
entry, including during shrinking. A product field that invalidates any captured
domain stops before later fields. Reports retain the previous witness and charged
proposal count; fresh execution is required after revision. Pure stable observers
and explicitly declared dependencies remain caller obligations.

Portable export rechecks codec and report sources after witness reconfirmation,
before encoding. Import preflights codec and specification sources before reading:
a stale prepared codec leaves input untouched. Prepare a new codec after its
revision changes; old codec instances remain refused. Normal Record constructors
restore Function wrapping during decode. Once actual port I/O starts, errors may
leave consumed input or emitted output; source checks do not provide rollback.

Lazy child iterators may be paused, but each resumed pull still checks its owned
sources before producer effects and after normal return, including EOF. A retained
`bind` descendant carries the original branch's source leaves as well as its new
branch. Lifting it into a new typed sampler cannot refresh those epochs. Generate
a new root when sources change. The implementation reuses standard Iterator/for
and the existing source boundary; source-free traversal keeps its direct loop.

P18 separates retained independent products from dependent bind regeneration.
`retainedProductStep` proves that replacing one coordinate preserves every other
preimage, width and external draw state; mapping commutes with replacement,
distinct replacements commute, and a smaller child decreases the sum measure.
The Gerbil implementation reuses its existing `sample-sequence` and root capture,
with seed/draw controls and typed Record/Function/FUN replay examples. These are
finite structural laws under faithful host representation, not GC/allocation or
arbitrary callback theorems.

P19 models supplied call-input demand with `demandInput` and `demandInputs`.
Successful descriptor preparation is reused; omitted/shadowed inputs are not
forced, and the first selected failure retains its exact cause and earlier cache
entries. Source admission stays with the existing guards. The Gerbil layer reuses
`defonce`, typed products and first-match signatures; it does not cache generated
values or substitute unsupported Types. See the RFC for sequential promise and
finite-Type proof premises.

P20 places revision-bound differential step laws in `PropertyTraces.lean`, under
the existing PropertyTesting namespace. `guardedTraceStep` preserves reference,
actual and comparison order, refuses revised declarations before downstream
stages, and retains exact exceptions and stable match/mismatch judgments. Scheme
regressions separately verify fixture cleanup and the real indexed-collection
FUN/retry workflow. These are finite epoch/observation laws, not host heap,
continuation, rollback or concurrency certification.

P21 moves finite shared product observation laws into `PropertyProducts.lean`.
`guardedProduct` composes the existing field evaluator with an owner preflight
and guarded representation packing, including empty products. Eight laws retain
order, natural sums, exact causes and downstream refusal. Scheme typed products
now consume the generic specification boundary rather than a duplicate cost fold;
captured directories and Record/FUN/replay controls provide the host correspondence.

P22 adds fixed-field source ownership to the same product module. `productSources`
flattens and deduplicates declared identities; six laws retain the complete field
conjunction, reject a stale later leaf before any draw/pack, and preserve nested,
shared and empty-domain judgments. The stable evaluator and its order/sum laws
remain unchanged. Source observers are pure Boolean functions in these laws;
runtime exception identity, copying and the unchanged seed/tree schedule have
separate Scheme regression coverage, not a heap or PRNG proof.

P23 adds finite rejection-sampling laws in `PropertyFilters.lean`. The model hands
the complete rejected-source history to each draw, checks the returned leaf union
before filtering and carries rejected owners into the next token. Ten laws cover
refusal, exact causes, zero fuel, retry/acceptance and a local generator-entry
bound. `filterHistory_pipeline` reuses the guarded stage evaluator to show that
revising a retired owner suppresses later nested callbacks. Nested generators have
their own budgets; the bound is not a total callback or host timing bound. Source
and scope fidelity and callback termination remain explicit host premises.

P24 adds `PropertyScopes.lean`: a transient replay directory authorizes checked
stages while the run's explicit ledger alone becomes new ownership. Nine laws
cover joint/nested checks, refusal, exact causes and stable/empty publication.
The model reuses guarded products and stages; it does not certify Gerbil control
transfer or parameter implementation. Runtime controls verify earlier-trial,
inspection and replay interruption, restored scope, no added sample source leaf
and unchanged observer work over twelve replays. User-captured continuations and
payload aliases retain their standard host lifetime obligations.

Size control: P25 retains known input sources without changing size algebra,
random state or retained trees. See `Examples/PropertySizes.lean` and the companion
Record/FUN example; dynamic sized selection still owns only selected branches.

P26 closes mandatory collection sources at the existing size selector. Positive
minimums preflight element leaves; optional empty selection does not claim them.
`PropertySizes.lean` models bounded lengths and authority while Record/FUN
regressions check retained shrinking, wrapped Functions and explicit revision retry.

P27 closes the shrink consumer admission boundary for returned filtered proposals,
including the last budget token. Existing audit accounting distinguishes charged
source refusal from unreturned iterator errors; settled real values alone reach
shrinking admission. `PropertyFilters.lean` gives the finite event/source laws.

P28 stages exact natural trace limits before initialization, then delegates to
the existing bounded draw engine. `PropertyTraces.lean` proves both cap bounds,
valid prefixes, initialization/early-stop causes and unchanged-size delegation.
Generic and Record/FUN examples check the host contract boundary and replay.

P29 validates finite outer spines and parameter results before candidate delivery.
`PropertySequences.lean` reuses guarded callbacks, Except composition and retirement
to establish source/shape refusal, exact causes and ordered proper results.
General lazy shrink Iterators and payload graphs keep their existing scope.


P30 extends the existing `PropertyScopes.lean` with `guardedThen`, composing
`guardedGeneration` for dependent model/fixture actions. Seven laws cover stale
preflight, first-stage revision, original exceptions, exact continuation,
last-stage revision, fresh result/state preservation and suppression of later
stages. `Examples/PropertyScopes.lean` exercises false and tuple values. Faithful
host stage/state encoding, pure observers and serial terminating callbacks remain
premises; host cleanup is tested in Gerbil rather than proved by these laws.


PBT RFC P32 adds eight nested admission/publication laws to `PropertyScopes.lean`.
Primitive actions require ancestor and local authority; terminal diagnostic
reports are checked under the parent after child scope unwinding. `nestedActions`
reuses `guardedThen`, and report publication reuses `guardedGeneration`. Accurate
pure observers, serial callbacks and faithful host scope encoding remain premises;
host continuation/cleanup and transactional port behavior are not verified.


PBT RFC P33 adds eight guardedAll laws in PropertyProducts. False field admission
is an observable result that stops the tail; true continues with the actual
state, stale sources refuse and original callback exceptions remain exact. Fresh
pure outcomes agree with List.all. Examples/PropertyProducts.lean includes a
false-head/throwing-tail control and a revised false result. These finite laws
assume faithful supplied-field order and host scope encoding; they do not verify
Gerbil contracts, arbitrary Type predicates, termination or runtime performance.


P34 protects typed sampler factory preparation and aggregate component measures
through the existing shared source boundary. Map key validation also inherits its
active ancestor. A revised first value cannot trigger another Map/trace weight or
later product binding. `map-service-tests` in the collection-properties example
combines two fixed-key service Records, nested Function wrapping, shrink refusal,
FUN delivery, fresh retry and both replay modes. Six regression cases and six
`guardedMeasure` laws cover exact totals, early refusal and original causes;
logical weights do not prove runtime costs. See P34 in the PBT RFC for premises.


P35 closes terminal error-classification admission through the shared checked
source action. A classifier that revises its owner cannot publish a normal refusal
or start obsolete nested effects; secondary exceptions retain the original cause.
Six generic cases (103 independent cases total), the Record/Function recipe-retry
FUN example and six `classifyFailure` laws cover classification, inspection,
confirmed shrink progress and replay. See P35 in the PBT RFC for precise premises;
this does not extend the domains, budgets or termination guarantees.


P36 makes the portable codec's own check an inherited checked-action scope.
Nested generation/domain/handoff work cannot continue after codec or application
source retirement. Six generic regressions (109 isolated cases total), the typed
service corpus Reader/FUN example, and two whole-execution scope laws cover refusal,
original causes, cleanup, non-retention, fresh retry and replay. The existing codec
and port boundaries remain: no arbitrary callback interruption or I/O rollback.
See P36 in the PBT RFC for proof premises and costs.


P37 captures recursive graph revisions at first discovery, including already
known siblings and returned sampler dependencies. Shared source admission now
serves discovery and runtime; late re-snapshotting and repeated sampler-spine
construction are removed. Seven regressions, the shared Record/Function FUN
preparation/retry example and six finite ledger laws cover refusal, identity,
shrinking and replay. Undiscovered dependencies, concurrent global snapshots and
callback termination remain explicit boundaries. See P37 in the PBT RFC for costs.


P38 binds constructor-produced samplers to their Type declaration and makes sampler
+ actual descriptor mandatory revision owners. Relabeling an inherited bounded
parser is refused; use a fresh constructor and explicit projection. Trace model
and List metadata are captured at construction through the existing source guard.
Eight new cases, a Record/Function schema-migration FUN example and six finite
binding/source laws cover preparation, diagnostics, compositions and portable replay.
No per-value wrapping or extra generator call is introduced; see P38 in the RFC.

P39 gives typed differential execution one inherited declaration scope. Nested
checked operations observe model and active fixture Type revisions immediately,
including standalone `check-trace` use. The existing scope is restored before
teardown: fixture-only retirement is allowed, while model revisions still refuse
nested cleanup work and factory return. `restoreDeclarations` preserves actual
state and original declaration identities; five laws and top-level controls cover
restoration, idempotence and stale/current admission. Existing nested-action laws
supply suppression of unstarted work. These are finite serial observer laws under
faithful host scope and terminating callbacks, not rollback or evaluator proofs.
See P39 in the Scheme RFC and the generated-traces service retry example.

P40 unifies first-observation preparation for typed trace generation, admission,
repair and differential checking. Earlier Type stamps are captured before each
later computed field, retained across ordinary Record normalization, and preserved
by the sampler's existing currentness hook. Gerbil dynamic scope restores fixture
ownership while retaining model authority. `observeDeclaration` reuses guarded
execution and first-revision capture: five laws cover preflight, later revision,
exact callback causes, stable capture and resulting ledger currentness. Top-level
controls exhibit a mixed-epoch rejection and stable/aliased declarations. Accurate
source observers, serial terminating callbacks and faithful host scope are premises;
these laws do not prove arbitrary field computations or concurrent snapshots.

P41 admits fixed-product topology before preparation, captures every known child
identity before factories, and retains the established bind/checkpoint draw.
An iterative Scheme candidate did not pass full-workflow GC cost acceptance and
is excluded from production. Standard Gerbil
contracts and the existing checked-action scope own refusal; Lists, finite Maps,
functions and typed products reuse the same sequence constructor. The independent
stdlib-only acceptance now requires 115 cases. PropertyProducts adds drawProduct
and an equivalent finite accumulator specification, with five laws for reference equivalence,
field order/length and exact continuation seeds. Existing guarded-product laws
suppress later factories after revision. Top-level controls cover width zero and
duplicate values. Finite lists, faithful source clocks/seed splitting, serial
terminating callbacks and host tail calls remain premises; no wall-clock or PRNG
quality theorem is claimed. The companion paired entry measures preparation,
drawing and full check/replay workflows with natural/post-GC and A/A controls.

P42 fixes standard test success forged through a diagnostic formatter. Admission
now requires an actual kernel execution, nominal passage and current sources
before/after rendering. Formatting runs under the existing inherited checked-action
scope; metadata cannot replace protected status/cause. Typed preparation refusals
supply a static refusal receipt and cannot manufacture execution. Original failure
causes outrank secondary formatting faults; passing renderer/observer exceptions
remain exact. Seven admitRendering laws cover missing/nonpassing reports, stale
preflight, retirement, stable payloads, precise exceptions and necessary authority.
They model admission and protected fields, not arbitrary UI fields or host TestResult
machinery. Accurate sources, faithful report metadata and serial terminating
callbacks remain premises. The independent suite now requires 121 cases; the
standard negative fixture requires eleven failures. A Record/Function FUN example
combines shrinking, both replays, forged/stale rendering and explicit retry.
