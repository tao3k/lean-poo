# RFC: model-driven collection property tests

- Status: implemented; finite acceptance and evidence boundaries are recorded below.
- Date: 2026-10-27.
- Targets: Gerbil-POO PR #13 and Lean-POO PR #13.
- Implementation acceptance: reusable protocol, collection controls and downstream integration are implemented; CI is checked independently for each submitted revision.

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
| `property-testing.ss` | `make-generator`, products, `check-property`, strict/budgeted shrinking, `replay-property`, `property-action` |
| `generation-graph.ss` / `recursive-generation.ss` | Existing bounded recursive value generation; not replaced by a second recursion engine |
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
All additions stay in the existing `clan/poo/property-testing` module.

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
`t/collection-testing-test.ss`. They exercise both existing RationalDict and trie
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
(import :std/test :clan/poo/object :clan/poo/property-testing
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
`Examples/` and `Tests/`; keep Gerbil functions in `property-testing.ss` and the
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
| First difference | Initial/result/state fault controls reject later steps and count only required observations |
| Adapter contracts | Malformed actual state, result and observation are Type errors, not counterexamples |
| Collection semantics | RationalDict and trie lifecycle plus stale-admission, index-owner, inverse and premature-publication fault injections |
| Finite Lean laws | `retire_valid`, `retire_sublist`, `retire_deletion`, `drawTrace_sound`, `trace_simulation`, `replayTrace_stale`, `replayTrace_failed` |
| Concrete collection proofs | Top-level `Examples/CollectionTesting.lean` reuses `applyIndexed` and `inverseChanges`; proves complete two-key enumeration and checks conflict/retry/inverse/old-value/stale outcomes, final primary/index restoration and detection of premature primary publication |
| Local full workflow | The complete 149-module workflow and linked paired collection benchmark pass under existing limits; 18 focused PBT cases pass |
| Published baseline CI | Lean `6bda6ff61fcde59f74cbf3f90723ae25c1f10328`: 17 successful checks; Gerbil `77dd5e6ae33047e0a2755f0be705bd6bf8ec3b99`: 53 successful checks, including single-process acceptance |

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
