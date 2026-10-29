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
