# RFC: model-driven collection property tests

Current finite acceptance includes P0–P17. The companion Gerbil RFC owns the
current developer interface; [property-kernel.md](property-kernel.md) maps its
standard test/debug integration, bounded diagnostics and configuration guards to
Lean laws. Historical audit identities below remain historical receipts.

- Status: implemented; finite acceptance and evidence boundaries are recorded below.
- Date: 2026-10-27.
- Targets: Gerbil-POO PR #13 and Lean-POO PR #13.
- Implementation acceptance: reusable protocol, collection controls and downstream integration are implemented; CI is checked independently for each submitted revision.

## Module ownership and independent-library boundary

The generic library uses ordinary modules under `testing/property`, with direct
imports. The runner is `testing/property.ss`; generator, model, replay and test
support live in `testing/property/`. The root `defbuild-script` builds them with
all other package modules. There is no separate package or forwarding facade.

| Module | Responsibility | Dependencies |
| --- | --- | --- |
| `testing/property/generator.ss` | Invocation-local random sources, unit/map/bind/sequence, lazy value-and-shrink provenance | Gerbil standard library |
| `testing/property.ss` | Explicit domain specifications, finite checks, bounded child consumption, reports and both replay forms | Generic generator module and standard library |
| `testing/property/model.ss` | Pure model folds, dependency retirement, bounded trace draw, scoped first-difference comparison | Generic generator module and Gerbil standard library |
| `testing/type.ss` | Type-driven derivation, Record contracts, bounded membership, POO source observations, typed reports and Reader/FUN actions | POO and generic modules |
| `testing/function.ss` | FunctionArguments derivation from checked signatures | POO function/signature modules and testing/type |
| `testing/generation-graph.ss`, `testing/recursive-generation.ss` | Bounded descriptor graph compilation and safe recursive derivations | POO type/recursive constructions |

Top-level `property-testing.ss`, `function-testing.ss`, `generation-graph.ss` and
`recursive-generation.ss` are moved, with all importers/build inventories migrated.
There are no compatibility forwarding files. Existing `support/testing.ss` and
`t/table-testing.ss` keep their distinct support/test-only ownership.

The generic modules import no POO object, Type, Record, lens or revision APIs.
Their records are Gerbil structs; domain admission and cost are mandatory caller
callbacks. POO retains its Record declarations and supplies bounded typed
admission, normalization and source-current callbacks at the boundary. Generality
is parametric; it is not a fallback to an unconstrained POO `Any` descriptor.

The independent-library acceptance copies these five generic source modules and
`examples/property-kernel.ss` into a temporary standard Gerbil package, declares
`clan/poo/testing`, and compiles with `defbuild-script`. The compiled suite runs
through `gerbil test`. It requires all 55 case receipts, an error-free result and
correct process exit status under the existing heap and timeout limits. The
isolated installation has no object, MOP or typed testing modules. Sharing a
module path does not import parent modules. This demonstrates code dependency
independence; it is not an upstream publication.

## Checked actions and interrupted shrink receipts

The execution layer uses one private hygienic `with-current` form around domain
actions. It evaluates an action once and checks its declared sources before and
after it. Admission, strictly decreasing cost and Boolean falsity compose as
short-circuiting judgments. The search driver handles only proposal consumption
and confirmation; it no longer duplicates source checks around each callback or
passes positional progress vectors between nested loops. A single invocation-owned
Gerbil record holds the confirmed witness and counters. POO retains its existing
Record report projection and Reader/FUN report delivery.

Every returned non-EOF proposal is charged before admission, measurement, property
execution or the trailing source check. EOF and an iterator exception return no
proposal and add no attempt. A candidate is confirmed only after all judgments
and freshness checks succeed. Thus an interruption retains the previous confirmed
witness, charged attempts, accepted steps and the original exception. It reports
`error`, `stale` or the caller's explicit refusal classification, never a new
`failed` witness or a minimum. An error in a source observer while classifying an
earlier error cannot replace that original cause. Error/stale reports keep useful
progress but cannot authorize concrete counterexample replay.

This follows the existing FUN/IO style of composing owned actions and the Racket
libraries' separation of lazy shrink trees from property execution. It does not
copy Rackcheck's `pass?` exception-to-falsified policy: our RFC keeps host errors
separate from Boolean false. Gerbil's existing Iterator/in-coroutine protocol
remains the lazy representation. No new stream framework, scheduler, namespace or
POO dependency is added to the generic library. Filtering is not allowed to hide
proposal consumption or introduce unbounded search between budgeted attempts.

The independent example interrupts child creation, iteration, admission,
measurement, properties and observers after a confirmed reduction. It checks
cause identity, original/reduced values, counters, seeded replay and stale replay
refusal. The typed Record example delivers the same receipt once through FUN.
Lean's finite `auditShrinks` distinguishes failed returned proposals from iterator
exceptions. `auditShrinks_budget`, `interrupted_shrink_preserves` and
`callback_error_retains` reuse the established shrink laws to prove accounting,
retained validity/falsity and exclusion of the pending failed proposal. Runtime
callback termination, source-observer accuracy and PRNG behavior remain premises.

## Canonical trace admission and execution

Whole-prefix admission retains its exact normalized command list. The generic
model previously checked normalized commands but executed the original inputs;
POO's prevalidated List path concealed that discrepancy. `prepare-trace` now
reuses the existing model fold to return either the complete prepared list or
refusal. `valid-trace?` is its Boolean projection. `check-trace` executes and
reports those same prepared command objects, without another normalization pass.
An empty prepared list succeeds; refusal is separate from a command whose payload
is false. No prepared prefix is handed to a fixture after a late rejection.

The typed facade still owns its existing List/Record/Function validation boundary
and supplies the identity normalizer to generic execution. This preserves nested
Function wrappers without installing an additional wrapper chain in the kernel.
Dependency repair uses the same model fold; shrinking and both replay forms use
the ordinary property runner and fresh scoped fixtures.

`examples/property-kernel.ss` combines shared producers, normalized contracted
callbacks, dependency repair, a faulty consumer, shrinking and both replays.
Separate late-domain/normalization-failure controls require zero fixture opens.
The POO Record regression rejects an invalid callback argument before its body
and refuses a missing producer before opening a fixture. Callback setup/cleanup
remains balanced on both success and errors.

Lean's `prepareTrace_sound` proves successful preparation preserves decoded
order, input length and state-dependent validity. `prepareTrace_identity` covers
the typed facade's already-normalized path; `prepared_observations` states the
exact execution handoff. The concrete collection example decodes command codes
through the existing conflict, inverse, stale and retry lifecycle and refuses a
malformed final code. These are pure finite laws: truthful normalization, model
callback purity/termination, runtime wrapping and the fixture simulation premise
remain separate executable obligations.

## Quickcheck and Rackcheck source comparison

The source references are pinned independently of the local compiler:

- [Racket Quickcheck](https://github.com/ifigueroap/racket-quickcheck/tree/0b6902d8d79973ec959f99e56ccba038beca8fe9):
  `quickcheck/private/generator.rkt` combines return/bind/sequence and splits the
  random source; `quickcheck/generator.rkt` expands `bind-generators` into that
  algebra. Ordinary Racket generators do not require Typed Racket.
- [Rackcheck](https://github.com/Bogdanp/rackcheck/tree/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7):
  `rackcheck-lib/gen/core.rkt` maps and binds shrink trees, retaining a child random
  state for dependent regeneration; `gen/base.rkt` builds lazy list shrink trees.

We adopt composition of generated values AND their provenance. A non-injective
map retains its preimage tree without asking for an inverse. Bind first explores
parent shrinks, regenerating each dependent child with the same captured child
seed, then explores that child's own shrinks. Gerbil's standard `in-coroutine` /
Iterator protocol provides lazy children; no thread, custom stream framework or
process-global sample cache is introduced. Seed splitting follows the compositional
idea, not byte-for-byte random sequence compatibility with either Racket library.

A generic generator and its intermediate shrink nodes must honor its declared
semantic domain; a malformed selector/callback is an error, not a false property.
The final property specification explicitly admits values and supplies a natural
measure. POO-specific generation-refusal classification stays in testing/type.
The kernel never classifies an exception as a passed or falsified property.

Source freshness is rechecked after iterator EOF before certifying exhaustion.
Zero shrink fuel invokes no shrink callback. A child is pulled only inside the
budgeted consumer body; no tail lookahead occurs after the final allowed attempt.
`minimal?` requires observed EOF and certifies only the supplied immediate
neighborhood. POO-derived raw shrink callbacks keep their finite proper-list
contract at one boundary; their own preparation cost remains subject to the
existing graph/search budgets and process guards.

Reports retain observers for all generated trial roots and forced shrink branches,
including earlier successful trials and rejected candidates. A changed original
branch cannot become authorized merely because the final witness moved elsewhere.
Seed replay keeps those observers live throughout rerun, and the new report owns
only the rerun's observations rather than accumulating replay closure chains.
Concrete replay performs no draws, selectors or child forcing. Observer accuracy,
callback purity/termination and runtime PRNG correctness remain explicit premises.

## Decision

Extend the existing descriptor-driven property-testing protocol with finite,
state-dependent command traces. Reuse its generator objects, PRNG ownership,
strict shrinking, revision admission, reports and Reader/FUN integration.
Use `:std/test` as the downstream test runner. Do not introduce another runner,
DSL, package namespace, scheduler, module loader or serialization framework.

The first complete unit exercises declarative unique indexes and persistent table
deltas: conflicting installation, successful installation, inverse recovery,
stale collection metadata/deltas and explicit repair/retry. It provides a reusable
trace protocol plus an executable collection example, rather than one hard-coded
random test or a general runtime/FFI verification framework.

## Source basis and existing capabilities

The author's [I/O Validation and Beyond discussion](https://github.com/metareflection/poof/blob/9affa8fbbb4f12cbd98cb97f8b8b84474fc39429/poof.scrbl#L1361)
explicitly includes pseudo-random value generators and value compressors among
type-descriptor operations. His dictionary examples compose algorithms through
final-self extension points. Stateful trace generation and dependency-preserving
shrinking are proposed extensions of that direction, not algorithms claimed to
already exist in the Racket listings. The fixed-point use of the word generator
elsewhere in the paper is distinct from a pseudo-random test sampler.

| Existing owner | Reused responsibility |
| --- | --- |
| `testing/type.ss` | Typed generator/product preparation, Type/source admission, report projection and `property-action`; execution delegates to the generic modules |
| `testing/generation-graph.ss` / `testing/recursive-generation.ss` | Existing bounded recursive value generation; not replaced by a second recursion engine |
| `Type`, `List`, `Tuple`, `Union`, `Exactly`, `Enum` | Command and trace membership; no `Any` fallback |
| Existing table/index protocols | `.delta/opt`, `.apply-delta`, `invert-table-delta`, index observations and supported metadata invalidation |
| FUN / IO and `:std/test` | Composition, fixture resource lifetime and ordinary suite discovery/checks |
| `LeanPoo.Functional.PropertyTesting` | Shrink admission, descent, retained falsity, budgets and stale-evidence laws |

The audit used Gerbil commit `7b2ead60d52c3648a26e65ca149636f5ab6f39dc`
and Lean commit `7f2f71e1463b99151f23994d1b1fcc1acd5a7696`. Uncommitted
representation/cache work is outside the audit and must not be overwritten.
See the existing `generated-testing.md`, `recursive-generators.md` and
`table-indexes.md` in each repository's documentation directory.

## Scope and explicit boundaries

V1 uses finite, sequential command traces, pure reference-state transitions,
explicit logical handles and finite canonical observations. Commands are owned,
stable data values. Every trial, shrink probe and replay gets a fresh actual
fixture. Model hooks and observation callbacks must terminate and produce finite,
stable values; process watchdogs and heap limits remain necessary.

The initial oracle uses ordinary association lists and logical receipt records,
independent of the implementation's indexed table algorithms. It must not call
`.apply-delta`, index construction or inverse application to compute expectations.
An oracle is fallible: Lean proves stated source-model laws, not the complete
Scheme implementation, compiler, collector or physical memory behavior.

Concurrent scheduling, arbitrary FFI pointer graphs, universal callback synthesis,
portable closure serialization and automatic contract/law discovery are outside
this unit. The first collection adapter qualifies the pure protocol on two
existing backends. Other ownership styles require their own execution/ownership
checks; pure results alone cannot certify mutable or linear publication.

## Proposed public surface

These are proposed signatures, not claims about the currently released API.
The typed entrypoints are in `clan/poo/testing/type`; generic execution is
owned by the directly imported `clan/poo/testing/property` modules above.

```scheme
(trace-generator command-type model steps: 64 dependencies: [])
(check-trace model commands with-system same?: equal?)
(trace-property model with-system same?: equal?)
(replay-counterexample report)

(property-action descriptor property consume
  sampler: #f dependencies: [])
```

`trace-generator` returns an ordinary `make-generator` object. Its descriptor is
`(List command-type)` and its `.accept?` additionally validates state-dependent
prefixes. Callers use that exact descriptor identity with `check-property`.
`trace-property` only turns `check-trace`'s explicit comparison result into the
Boolean required by the existing runner. `replay-property` retains seeded replay;
`replay-counterexample` executes the stored concrete witness without drawing or
shrinking it. `property-action` gains the same supplied-sampler/dependency inputs
as `check-property`, retaining the existing Reader/FUN chain.

The existing `Record` contract defines `TraceModel`; `TraceGenerator` inherits
that contract and adds generation/shrink hooks. Construct models with
`make-instance TraceGenerator`, retaining normal POO field initialization and
validation. No separate model interpreter or package namespace is introduced.

`Command`, `State`, `Result` and `Observation` are explicit Type descriptors.
The transition boundary validates dependent state/results and the comparison
boundary validates observations. Callable fields recognize procedures; they do
not infer host arity or termination, or preempt the shrinker's candidate gate.

The model exposes these extension points:

| Field | Contract |
| --- | --- |
| `initial` | `() -> reference-state`; returns a fresh pure state |
| `enabled?` | `(state command) -> Boolean`; whether this prescribed operation is admissible now |
| `advance` | `(state command) -> (values next-state expected-result)`; pure, deterministic transition |
| `observe` | `(state) -> stable finite canonical observation` |
| `draw` | `(state random size) -> Option command`; `some` carries a command, `#f` ends the trace |
| `shrink` | `(command) -> finite proper list of parameter candidates` |
| `measure` | `(command) -> natural number`; parameter complexity |

A false command, when allowed by its Type, is `(some #f)`, not end-of-trace.
Hook exceptions are errors, not disabled commands. Non-Boolean preconditions or
comparisons are errors rather than truthy successes. Invalid command descriptors
or callback configuration refuse before actual fixture effects.

`with-system` is a scoped fixture function, `(use -> result)`. It creates a fresh
actual system, calls `use` once and owns cleanup through standard call-with/IO
mechanisms. The supplied system is an ordinary object exposing:

| Field | Contract |
| --- | --- |
| `State` | Actual state descriptor, including any deliberately retired snapshots |
| `initial` | Initial actual state, validated through `State` |
| `step` | `(actual-state command) -> (values next-actual-state actual-result)` |
| `observe` | `(actual-state) -> owned/stable canonical observation` |

Construct the fixture with `make-instance (TraceSystem ActualState)`. The scoped
callback is used exactly once. Its result cannot be replaced or reused after the
scope ends.

Pure prefix admission and dependency retirement share one typed state fold;
selection chooses whether to reject or omit a disabled command. Generation and
differential checking use bounded state folds; checking exits at the first
mismatch. `property-action` composes the run and consumer through the existing
Reader/FUN bind rather than introducing an effects framework.

Logical handles resolve only in the fixture that created them. No pointer,
mutable PRNG, table owner or cached receipt may escape one trial and become the
initial state of another trial or shrink probe. Fixtures can own files or other
resources without making the PBT runner a resource manager.

## Generation and domain admission

1. Admit `command-type`, model hooks, positive descriptor configuration and a
   finite nonnegative step cap. Create one ordinary trace sampler.
2. For each draw, call `initial`; consume the existing run-local random source.
3. Until `min(size, steps)` commands have been drawn, ask `draw` for a command
   enabled in the CURRENT reference state. The adapter chooses from enabled
   alternatives directly, rather than generating arbitrary syntax until it passes.
4. Check the command Type and Boolean `enabled?`, then use `advance` to construct
   the next reference state. A malformed/disabled draw is a generator error;
   it is never silently dropped or retried without a budget.
5. Return an owned finite trace spine. A normal `#f` from `draw` ends a valid
   prefix; it does not prove that the whole domain is exhausted.
6. Sampler admission replays the whole reference trace. A deleted producer or
   changed prerequisite cannot be hidden by accepting each command independently.

A valid empty trace checks initial-state equivalence; it does not demonstrate
command coverage. The collection example must separately assert coverage of its
required lifecycle prefix, with seeded random state-dependent suffixes.

## Stepwise differential execution

Preflight the complete command trace against the pure model before opening the
actual fixture. Invalid externally supplied traces are errors, not false
counterexamples or successful skipped tests.

Compare initial canonical observations. For each command, compute the expected
transition/result, run the actual operation once, compare the reply and then
compare the next canonical observation. Stop at the first mismatch. Do not
continue executing potentially dependent commands after divergence.

`check-trace` returns an ordinary diagnostic object containing `matched?`, phase
(`initial`, `result`, `state`, `complete`), command index, optional command and
expected/actual observations. It retains no actual fixture or live table owner.
`same?` must return Boolean; applications with representation-specific equality
supply it explicitly. Backend allocation identity or raw memory layout is not
the default oracle.

Expected protocol refusal is an ordinary modeled result. Only the collection
adapter classifies declared failures such as `table-index-conflict?`,
`table-conflict?` and the specific documented stale-source conditions. It retains
original diagnostic fields needed by the oracle. Unexpected exceptions propagate
unchanged to the existing `error` report; catching everything as conflict, false
or success is prohibited. Failed operations must leave the observed old state
and usable ownership unchanged before any retry is admitted.

## Dependency-preserving sequence shrinking

Reuse the existing runner's admission/descent/falsity/budget loop. Add only trace
candidate construction:

1. Propose deleting one command, and reuse existing coordinate shrinking for
   parameter replacements supplied by `model.shrink`.
2. Replay each proposed sequence from a fresh reference state. Retain a command
   only when it is typed and enabled at its new prefix. Omit commands whose
   producers/prerequisites were removed, then continue replaying the suffix.
3. Never rename a logical handle to another surviving handle, invent a producer,
   regenerate a random suffix or silently turn an expected refusal into success.
   Prescribed reply labels are part of collection commands and their preconditions.
4. Replay/admit the resulting whole trace again before running the actual system.
5. Use `length(trace) + sum(command-measure)` as the natural measure. A parameter
   replacement must reduce the whole measure; deletion plus dependent retirement
   cannot increase it. The existing runner retains only valid, strictly smaller
   traces that still falsify the differential property.

This is semantic dependency retirement, not text deletion or an inferred global
minimal sequence. An independent command survives removal of unrelated producers.
Deleting a producer can retire several dependent consumers; later commands that
remain enabled are preserved in order. A retired mismatch that no longer fails is
rejected by the existing falsity check, retaining the previous valid witness.

The first implementation may replay each candidate in O(n) reference steps and
propose O(n) single deletions, plus finite parameter candidates. It must charge
these costs; the shrink attempt budget does not prove callback execution time,
byte allocation or globally minimal counterexamples. No hidden unbounded search
or replacement scheduler is introduced.

## Revisions, failures and replay

Specification sources and system-under-test state have different roles:

- Descriptor/model/factory recipes are stable specification dependencies. Their
  mutation makes the PBT result `stale` and refuses old witness/seed replay.
- Per-trial table metadata, pending deltas and collection revisions are fixture
  state. Intentional changes to them are tested operations, not specification
  mutation. Do not register every mutable fixture as a stable PBT dependency.

Retain the existing `passed`, `failed`, `error`, `stale`, `exhausted` and
`unsupported` distinctions. Only valid Boolean-false observations create shrinkable
`failed` witnesses. Zero cases are refused. Unsupported generation, stale
specifications, process limits and unexpected exceptions never mean pass.
An ordinary stale TABLE result may be expected by a command; it must not be
confused with a stale PBT specification.

Reports retain their original and reduced concrete traces, seed, trial, effective
limits and source snapshot through the current property-report mechanism.
Concrete replay checks current sources and trace admission before opening a fresh
fixture; it does not consult the PRNG. Seed replay remains runtime/PRNG dependent.
V1 reports are in-process Scheme values, not portable closure bundles. Data-only
commands may be printed/read with standard Scheme tooling for explicit reproduction;
no versioned JSON, full benchmark datasets or archives are committed. Replaying on
changed code is a new experiment and cannot inherit an old report's authority.

## First complete collection adapter

Use typed data commands over integer keys/values and explicit logical ticket IDs.
The reference state contains primary bindings, logical metadata generation,
current/stale family status and captured before/after delta expectations.
It computes uniqueness independently with association lists.

| Operation | Required differential checks |
| --- | --- |
| Stage | Capture the old expectation and generation without publishing a table update |
| Install | Old-value validation, unique-index result and atomic primary/index observation |
| Undo | Existing inverse delta restores the prior observation or reports the prescribed conflict |
| Put/remove | Update reference bindings and every observed index; unblock a refused install when appropriate |
| Expire metadata | Leave the old collection state available only as a stale observation/control |
| Read old | Require the documented old-family refusal; no fallback to unchecked primary data |
| Refresh | Reconstruct through existing public index/table constructors, preserving valid primary content |
| Install old-generation ticket | Require stale delta refusal after refresh |
| Restage/retry | Create a fresh ticket; success must follow the same ordinary install path |

A deterministic valid prefix guarantees unique-index conflict, repair/retry,
old-value conflict, inverse restoration, stale family and stale delta rejection.
State-dependent random suffixes vary keys, values, pending-ticket selection and
revision order. Both RationalDict and the existing trie backend must agree with
the independent oracle. No new table, hash, index or ownership algorithm is part
of the test harness.

Inject known faulty adapters: admit a stale ticket, mutate primary state before
index refusal, lose an inverse update, or return a wrong index owner. The runner
must fail, shrink to a valid witness and reproduce it. Successful tests alone are
insufficient acceptance of the PBT implementation.

## Abstraction and implementation review

The implementation uses the existing POO `Record` contract for sampler/model/
fixture data rather than hand-written field-presence loops. `TraceGenerator`
inherits `TraceModel`, so generation and checking declare one domain.

A shared typed reference fold supports two selection policies: strict admission
rejects disabled commands; repair retires them. Both invoke the same state/result
boundary and preserve retained command order. Bounded generation carries its
state through `for/fold`; differential checking folds paired reference/actual
states and uses one escape continuation for the first mismatch. The scoped
fixture owns resource cleanup, while `property-action` uses the existing
Reader/FUN bind to hand its report to the caller's consumer.

This keeps policy separate from traversal without adding a monad, interpreter or
namespace solely for testing. Host exceptions stay errors. Invalid shrink
proposals still reach the existing budget/domain gate, rather than being hidden
by a new callback wrapper. The fixture's actual-state contract may intentionally
include expired snapshots; command preconditions and stale-version observations
remain part of the domain model.

The executable examples are `examples/collection-testing.ss` and
`t/representations/collection-testing-test.ss`. They exercise both existing RationalDict and trie
backends, including adapters deliberately broken at stale admission, index
observation, inverse installation and atomic failure. Their reference oracle uses
logical handles and ordinary lists, independent of backend mutation algorithms.

## Complex executable examples

[`collection-properties.md`](collection-properties.md) explains three runnable
examples in `examples/collection-properties.ss`: interleaved unique-owner handoff,
two-round service upgrades with retained receipts, and same-epoch ABA versus
cross-epoch rejection. Each uses both backends and multiple seeded runs through
`property-action`, with random suffixes after its required domain prefix.

Known faulty adapters must produce smaller dependency-valid counterexamples and
reproduce them through both replay paths. Custom-prefix controls additionally
verify owned scalar commands and fresh producer selection from retained IDs,
rather than assuming that the trace step number is unused. The corresponding
`freshHandle_lower`, `freshHandle_gt` and `freshHandle_not_mem` laws extend the
existing Lean testing model. These are finite design controls, not universal
runtime correctness or serializability claims.

## Downstream Scheme integration

The library additions below are implemented on PR #13. Users need a revision
containing them; older releases must not be described as providing these exports. Declare the package through the
project's normal Gerbil dependency workflow, with no Lean checkout or special
load-path/environment variables.

The downstream project owns its command Type, pure model and scoped actual fixture.
The following proposed test file delegates generation, shrink budgets and replay
admission to Gerbil-POO, and execution/discovery to `:std/test`:

```scheme
(export collection-model-test)
(import :std/test :clan/poo/object :clan/poo/testing/type
        (only-in "support/collection-model.ss" Command model with-system))

;; One standard suite fails on mismatch, stale sources, exhaustion or callback error.
(def collection-model-test
  (test-suite "collection model"
    (test-case "stateful differential traces"
      (let* ((sampler (trace-generator Command model steps: 64))
             (descriptor (.get sampler descriptor))
             (property (trace-property model with-system))
             (report (check-property descriptor property sampler: sampler
                       dependencies: [model] seed: 41 cases: 100
                       size: 40 shrink-budget: 200)))
        (check-equal? (list (.get report status) (.get report counterexample)
                            (.get report cause))
                      '(passed #f #f))))))
```

If `with-system` captures mutable factory/adapter recipes, include those stable
recipe objects in `dependencies:` as well; do not include the fresh mutable
fixture itself. A downstream project can first adopt the supplied collection
example, then replace only its command Type, model and actual adapter.

Export suite names ending in `-test`, retain the project's standard build/test
entry (`gerbil build` / `gerbil test`), and use its existing process/heap guards.
No PBT-specific runner is required. The implementation example will expose the
same model/fixture to a normal suite and a Reader/FUN `property-action` consumer.

For an expected regression failure, call `check-trace` on the stored minimized
trace for step diagnostics and `replay-counterexample` to reproduce Boolean false
with current sources and a fresh fixture. `replay-property` reproduces the seeded
search. A library mismatch is a failed test; no test should accept `error` or
`stale` merely because it was expecting a counterexample.

## Lean proof and implementation placement

Extend the existing `LeanPoo.Functional.PropertyTesting` namespace, rather than
creating a parallel testing namespace. Keep executable Lean controls in top-level
`Examples/` and `Tests/`; keep Gerbil functions in `testing/type.ss` and the
collection adapter in a functionally named `examples/` file. Each `def` documents
its contract/failure boundary. Split by existing functional boundaries if needed;
no code file should grow beyond the agreed modularity limit.

Required finite source laws:

1. Enabled draw/advance preserves valid prefixes and the declared step bound.
2. Dependency retirement returns a valid ordered subsequence under pure,
   deterministic model transitions and command admission premises.
3. Accepted shrink steps retain validity and falsity and strictly decrease the
   natural measure, reusing the existing budget/preservation theorems.
4. Step simulation plus initial observation agreement implies finite-trace
   agreement, including the first prescribed refusal and unchanged-state cases.
5. Stale specification snapshots refuse replay; concrete witness replay does not
   require a PRNG stream equality assumption.

Faithful backend observations, equality, stable callbacks and actual adapter
refusal classification remain explicit assumptions. These proofs do not verify
Gerbil, C++, FFI memory safety, arbitrary callback termination or concurrent
linearizability. Performance acceptance is measured separately.

## Verification matrix

| Obligation | Implementation / executable evidence |
| --- | --- |
| Typed model and fixture data | `TraceModel`, inherited `TraceGenerator`, `TraceSystem`; examples declare one reusable fixture Record and create fresh instances |
| State-dependent draws and dependency repair | Shared typed `fold-trace`, bounded generator fold, existing shrink budget/domain gates; invalid-draw, false-command and independent-suffix controls |
| Fresh resource scope | Distinct fixture identity across trials, shrink probes and both replays; cleanup counters remain balanced after comparison exceptions |
| Canonical handoff | Exact normalized command identity, one normalization per check, contracted callbacks through repair/replay, and late rejection before fixture effects |
| First difference | Initial/result/state fault controls reject later steps and count only required observations |
| Adapter contracts | Malformed actual state, result and observation are Type errors, not counterexamples |
| Collection semantics | RationalDict and trie lifecycle plus stale-admission, index-owner, inverse and premature-publication fault injections |
| Finite Lean laws | `retire_valid`, `retire_sublist`, `retire_deletion`, `drawTrace_sound`, `trace_simulation`, `replayTrace_stale`, `replayTrace_failed` |
| Concrete collection proofs | Top-level `Examples/CollectionTesting.lean` reuses `applyIndexed` and `inverseChanges`; proves complete two-key enumeration and checks conflict/retry/inverse/old-value/stale outcomes, final primary/index restoration and detection of premature primary publication |
| Local full workflow | The complete 149-module workflow and linked paired collection benchmark pass under existing limits; The existing focused PBT cases plus the independent-library cases pass |
| Published baseline CI | Lean `7932410a339dadc7d3736e286cbc6750c689d220`: 17 successful checks; Gerbil `4be7c411120cce18436fc35875a62da8e420f16a`: 53 successful checks, including single-process acceptance |

The local full-workflow row records the earlier accepted workflow. In the
interrupted-shrink follow-up, macOS `just check 2 1 4` stopped at the existing
90-second `build-shared` executable-construction gate. That is an unpassed local
build gate, not a falsified property or a paired-performance receipt. The existing
standard build configuration and limits are retained. Standalone kernel tests,
Record/FUN regressions, complete compiled-suite execution and exact-head CI are
reported separately; none substitutes for a missing full-entry receipt.

The published baseline CI was checked before this follow-up. Every later revision
must pass the same CI; that baseline is not evidence for unsubmitted edits. Full
Lean submission checks and exact-head remote CI remain separate from target proof
checks. No source law proves a host adapter simulation premise automatically.

The three delayed Gerbil baseline jobs were waiting in GitHub artifact download,
not running a failing compiler/test. They completed without reruns or changed
limits. Local `pkg-config-libs "openssl"` uses the selected system `pkg-config`;
the Nix tool without OpenSSL metadata is distinct from Homebrew's configured tool.
No library paths are hard-coded to hide that environment distinction.

## Acceptance checklist

- [x] Reusable trace generation/admission, with typed invalid-draw and bound controls.
- [x] Fresh-fixture initial/step/result/state comparison and first-divergence reports.
- [x] Dependency-retiring structural and parameter shrinking; independent suffix retention.
- [x] Original-cause errors, expected refusal and specification-vs-fixture stale controls.
- [x] Seed and concrete-witness replay; old-source refusal before fixture effects.
- [x] Complete indexed collection lifecycle on two backends, including failure/retry.
- [x] Fault injection demonstrates false witnesses, valid shrinking and exact reproduction.
- [x] Standard downstream test example and FUN/IO composition, using the implemented public API.
- [x] Finite Lean laws and executable examples, with assumptions stated beside claims.
- [x] Focused regressions, the COMPLETE Scheme inventory and COMPLETE Lean checks pass.
- [x] Published baseline commits in both PRs have separately verified full CI results; later revisions retain the same required gate.
- [x] Resource limits, existing checks and progress remain; no SubAgent or committed raw datasets.

The finite V1 protocol is complete within the stated scope. Keep universal
correctness claims separate from generated evidence, and verify each submitted
revision through the unchanged full gates. The matrix identifies reproducible
checks; it does not turn this document into a replacement for their results.

## P13: declared finite enumeration simplification

Finite Enum values previously had no shrink candidates and zero measure. A
nested collection could reduce its shape but could not simplify an Enum field.
`generator-elements choices` now maps the existing integer shrink tree through a
captured vector of declared values. It requires a nonempty proper list, draws one
index regardless of size, and never redraws while shrinking. Equal payloads retain
their distinct position preimages. Mutable payloads remain caller-owned; only the
list spine is detached. Existing observer ownership and exact error causes apply.

The POO scalar bridge reuses Enum's existing `.uint<-` and `.<-uint` metadata.
The first equal declaration position is the natural measure. Value-only shrinking
maps smaller indices through the same descriptor; generic tree shrinking retains
its original index preimages. A duplicate proposal with equal canonical rank is
charged and refused by the existing strict-descent gate. Empty Enum remains an
uninhabited leaf and does not invalidate an otherwise inhabited Union. Declaration
order is an explicit simplification policy, not an inferred semantic ordering.

Regression acceptance covers false payloads, equal duplicates, detached spines,
no redraws, stale retained descendants, original callback causes, minimum failing
ranks, concrete/seed replay and a nested List/Tuple/Enum FUN workflow. Changes to
the role descriptor reject old reports. Independent generic acceptance now runs
48 cases. No equality implementation, RNG, shrink runner or namespace is added.

Lean proves selected values belong to the finite domain, out-of-range selection
refuses, first-occurrence rank is no larger than the selected index, and earlier
positions strictly lower canonical rank even with duplicates. Host equality/hash
agreement, stable payloads, truthful observers and terminating callbacks remain
premises. Index generation does not prove PRNG distribution or wall-clock costs.
Preparation copies N positions; each draw selects one index; shrink work and
source checks retain the existing lazy tree and budget costs.

[Rackcheck's finite-choice generator](https://docs.racket-lang.org/rackcheck/index.html)
also supplies shrinking. Its removal-of-previous-choices policy differs from our
explicit declaration-order policy; byte-for-byte tree parity is not claimed.

## P14: dependency-repaired block trace shrinking

Audit finding: the typed trace sampler enumerated only single-command deletions
and separately rebuilt parameter coordinates. A failure requiring zero or two
independent noise commands can disappear after every single deletion, so that
neighborhood can stop before a smaller valid witness is reachable. This is a
concrete missing structural neighborhood, not a promise of global minimality.

`testing/property/model` now exports `shrink-trace model commands shrink`. It
composes the existing `data-list-shrinks` policy with `repair-trace`: aligned blocks
halve to single positions, then parameter-coordinate proposals follow; each raw
candidate is normalized and dependency-repaired once. The typed `trace-generator`
uses this function with its existing prepared model and raw parameter callback.
There is no separate block algorithm, identity search, handle renaming or fixture
execution. Generic downstream code uses the same function. Callback errors retain
their original cause, and empty proposals remain successful candidate sequences.

The existing runner still owns membership, strict cost descent, retained failure,
source checks, zero-fuel behavior and replay. Repair can retire more dependents;
strict descent is guaranteed for nonempty structural deletions with natural
parameter weights. Parameter replacements still require the runner's cost check.
The normalizer must be stable and preserve the intended command interpretation;
Lean's retirement laws model already-normalized commands, not arbitrary decoder
effects. Parameter callbacks and normalizers remain terminating premises.

Acceptance includes a single-deletion control that cannot cross a parity barrier,
the block policy reducing to the required producer/consumer pair, dependency
retirement, parameter normalization errors, balanced scoped fixtures, zero-budget
no-shrink behavior, FUN execution, seed/concrete replay and old-source refusal.
The generic isolated suite now executes 50 cases. Existing real collection model
fault injections and their dependency/replay regressions remain in the full check.

Lean composes existing block and retirement laws to prove valid dependency order,
retained-sublist identity, at least the deleted block's length decrease, and strict
complete trace-weight decrease. The concrete parity model matches the executable
control. No arbitrary callback, runtime scheduler or host-GC theorem is claimed.

The value-only callback boundary still materializes a finite proper candidate
list. For length N, structural proposals are counted by `list-deletion-count N 0`;
repairs traverse retained prefixes, and parameter proposal costs are additional.
We do not claim lazy preparation, linear wall-clock complexity, all possible
subsequences, or a globally minimal witness. The supplied neighborhood becomes
stronger without changing fuel accounting or inventing another shrink runner.

## P15: source-consistent policy and product admission

Audit finding: shrink admission wrapped the policy precondition and property as
one action. A precondition that returned true after revising a declared source
could therefore enter the property before the outer stale check. Fixed products
similarly checked sources around the aggregate predicate/measure, allowing later
field effects after an earlier field invalidated their captured specification.
Negative controls reproduced all three forbidden downstream calls before repair.
These are sequential source-admission defects, not unrestricted effect inference.

The existing hygienic `with-current` form now brackets shrink eligibility before
property entry, reusing the run's own nonlocal stale exit. Stable exclusion remains
non-falsification and adds no generation coverage. Products reuse that same form
around each field predicate and weight, checking every captured domain source
between callbacks. Gerbil's standard `map-in-order` supplies ordered measurement;
there is no new callback framework, namespace or source cache. Generator, root,
shrink and concrete replay retain their existing owners and reports.

A refusal never installs the in-flight proposal. Its already returned attempt
remains charged, the previous confirmed witness survives, no minimum is certified,
and callback exception identity is retained even if the source also changed.
Fresh execution may capture revised sources; seed replay of stale reports may not.
Already executed callback effects are not rolled back. Observers must be accurate,
pure and terminating; each application must declare its mutable dependencies.

Regressions cover true/false stale eligibility, cross-field recognition and
measurement invalidation, skipped later callbacks, original policy exceptions,
retained witness/attempt accounting, stable exclusions and unchanged coverage.
The FUN/Record example revises shared policy rules during shrinking, rejects the
old report, then prepares a new execution that shrinks and replays successfully.
The isolated generic suite now runs 55 cases without POO modules.

Lean composes the existing guarded state callback model into ordered product
stages and a shrink-policy judgment. Seven laws cover immediate and arbitrary
prefix refusal, original causes, stale Boolean policy returns, stable exclusion
and admitted evaluation. Concrete controls use effect markers for forbidden
later fields/properties. These finite laws require a faithful host interpretation;
they do not prove arbitrary source observers or concurrent atomicity.

With N product fields, successful full recognition/measurement adds two aggregate
source checks per visited callback, each checking up to N domains. This may cost
O(N²) observer calls; arbitrary observers offer no invalidation notification that
would justify caching a once-true result. Host callback and observer costs remain
explicit, and all existing runtime limits and proposal budgets remain unchanged.
No speedup or global effect safety is claimed.

[Rackcheck](https://docs.racket-lang.org/rackcheck/index.html) supplies the lazy
generator/property composition comparison. Revision observers are this protocol's
additional responsibility; this change does not claim Rackcheck implements them.

## P16: source-consistent portable handoff stages

Audit finding: export reconfirmation and encoding shared one codec boundary. A
property could invalidate codec metadata while leaving its witness domain stable,
then still invoke that stale codec's encoder. Import likewise consumed an envelope
before its first provenance preflight, even when the codec or specification was
already stale. Negative controls reproduced one forbidden encoder invocation and
an unexpectedly consumed input datum before the fix.

The existing `with-codec` now owns distinct confirmation, encoding and delivery
stages. A normally returning confirmation checks both application and codec
provenance before encoding starts. Encoder refusal still precedes every output
prefix. Import preflights both sources before its first read, then checks the
bounded envelope read, trailing-data check, decode and concrete-witness admission
at their existing boundaries. Invalid policy configuration remains first; stale
preflight now precedes input parsing and identity admission. For current sources,
identity and trailing-data errors still precede decoder/property callbacks.

No codec registry, port wrapper, serializer or runner is introduced. Standard
Gerbil ports and the existing explicit data codec retain format identity, payload
budgets and Function reconstruction. An already stale read leaves input untouched;
once I/O has started, consumed/emitted bytes are not rolled back. A port or
callback exception keeps its own cause even if sources also changed. Atomic
publication, arbitrary reader allocation and concurrent source changes between
checks remain outside these finite sequential guarantees.

Acceptance covers confirmation invalidation, zero encoder/output effects, stale
input preflight, original confirmation exceptions, and fresh codec preparation.
The typed FUN example shrinks a Record with a Function field, retires codec
metadata during export reconfirmation, retries using a new codec, rejects the old
codec without consuming input, and reconstructs the checked Function through the
ordinary Record constructor. Generic coverage/decoder/encoder/corpus tests remain
unchanged in scope; the isolated generic kernel inventory stays at 55 cases.

Lean composes existing guarded callbacks into confirmation/encoding/delivery.
Seven laws prove preflight refusal, confirmation source/cause refusal, encoder
source/cause refusal, exact stable payload handoff and original port causes.
Controls distinguish skipped later actions from post-delivery refusal. Faithful
witness confirmation, observer accuracy and callback termination remain premises;
no host I/O rollback or compiler correctness is asserted.

Export adds one constant codec/context boundary between reconfirmation and encoding;
import adds guarded read/trailing-data stages. Existing data-copy node/depth budgets
are unchanged. Observer, serialization and host port costs are not claimed zero,
and no wall-clock speedup is asserted. This preserves the generator/property
separation learned from [Rackcheck](https://docs.racket-lang.org/rackcheck/index.html)
while enforcing this library's additional revision protocol.

## P17: source-owned resumable shrink traversal

Audit finding: standard value shrink factories checked their source leaves only
when a coroutine first started. A paused iterator could resume producer effects
after its source changed. Combinators could detect stale results after that extra
pull, while dependent bind reconstruction could omit the originally selected
child's source leaves on a separately retained smaller node. Negative controls
reproduced an unchecked next value, an extra producer effect and a descendant
that incorrectly reported its old origin as current.

One private `for-sources` form now composes the existing `with-sources` boundary
with Gerbil's ordinary Iterator protocol. It guards factory evaluation and every
`next!`, including EOF. Value generation, mapping, bind, filtering, sequence
coordinates and finite-function tables use the same form. No new public DSL,
iterator implementation, coroutine framework, scheduler or source registry is
added. If both owned and inherited source lists are empty, the form lowers to the
standard `for` loop directly; a currently true observer never qualifies for that
fast path merely because of its current truth value.

Bind nodes merge original/parent/selected-child leaves before admission and pass
that flat ownership to parent regeneration and child shrinking. Mapped descendants
retain the enclosing observed leaves. Retained subtrees cannot drop old authority
by selecting a fresh branch, including when lifted through the ordinary typed
`from-generator` bridge into a separate FUN run. Fresh invocation may capture a
new epoch; old retained nodes and old replay remain refused. Unvisited alternative
branches are not scanned or added. Advanced handwritten sample producers still
must declare accurate source leaves on their own nodes.

Regressions cover paused primitive and map/filter/bind/sequence/function traversal,
original iterator causes after source mutation, historical bind ownership and
fresh invocation. The Record/Function/FUN example retains a smaller dependent
subtree, rejects it after the original branch changes, then regenerates, shrinks
and replays under the new epoch. Existing seed checkpoints, parent-before-child
order, zero-fuel behavior, EOF checks, proposal accounting and corpus tests remain
in the full workflow. Independent generic acceptance stays at 55 kernel cases;
additional public workflow and typed cases run under the standard suite.

Lean reuses source unions and guarded callback transitions. Eight laws establish
rebuilt membership/currentness/stale refusal and per-pull preflight, EOF refusal,
exact exception/value preservation and the source-empty fast path. Accurate pure
observers, faithful host callback interpretation and termination remain premises.
This is sequential resume admission, not concurrent linearizability, coroutine
runtime verification or arbitrary closure dependency inference.

Guarded pulls add before/after source walks and reuse the existing inherited
context-sharing fast path. Source identity deduplication retains all distinct
captured epochs, never deduplicating by Boolean truth. Origin lists may grow with
visited reconstruction ancestry; this is not an O(1) source-check or host-heap
bound. Source-free data keep the standard loop; no wall-clock improvement is
claimed. Proposal budgets count returned composed proposals; an interrupted pull
that returns no proposal cannot certify a minimum. Existing heap/deadline guards
still bound arbitrary callback work.

[Rackcheck bind](https://docs.racket-lang.org/rackcheck/index.html) provides the
parent-first lazy tree comparison. Original child seeds and regeneration order
are unchanged; source ownership is our additional explicit protocol.
