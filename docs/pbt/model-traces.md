# Stateful models and dependency traces

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Canonical trace admission and execution](#canonical-trace-admission-and-execution)
- [Stepwise differential execution](#stepwise-differential-execution)
- [P14: dependency-repaired block trace shrinking](#p14-dependency-repaired-block-trace-shrinking)
- [P20: scoped differential observations under fixed declarations](#p20-scoped-differential-observations-under-fixed-declarations)
- [P30: source-consistent generic model actions](#p30-source-consistent-generic-model-actions)
- [P54: demand-driven dependency-repaired trace trees](#p54-demand-driven-dependency-repaired-trace-trees)
- [P59: trace request admission before declarations and fixture scope](#p59-trace-request-admission-before-declarations-and-fixture-scope)
- [P60: owned trace ingress and first-observed explicit dependencies](#p60-owned-trace-ingress-and-first-observed-explicit-dependencies)
- [P70: shared dependent declarations and closed source observers](#p70-shared-dependent-declarations-and-closed-source-observers)

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

## P20: scoped differential observations under fixed declarations

Direct typed `check-trace` previously could return a match after its fixture
changed the model declaration midway through execution. The typed boundary now
captures model/schema/Type owners, then adds fixture/schema/State owners without
refreshing old stamps. Existing preparation, step, observation, validation,
comparison and factory-return stages share one checked action. The generic model
fold and caller-owned cleanup remain unchanged; actual State can still evolve.

`PropertyTraces.lean` reuses guardedGeneration in the existing PropertyTesting
namespace, with eight finite laws covering preflight, revision refusal at each
stage, exact callback causes and stable match/mismatch preservation. The new
module avoids extending the already large generator algebra file. Scope cleanup
is covered by Scheme regressions, not a theorem about the host continuation
runtime. The real indexed-collection example composes state-dependent traces,
FUN, stale rejection, explicit preparation retry and seed replay.

Epoch accuracy, sequential observation, termination and a faithful fixture/model
relation are premises. Hidden heap changes, concurrent linearizability, backend
rollback and wall-time/GC guarantees are not established. Each callback checks a
finite ledger; wrappers are prepared once per trace. All existing checks and
resource limits remain required.
Fixture declaration ownership ends with active use, allowing normal resource
retirement during teardown; model declarations stay checked through factory
return. Executable teardown controls preserve this scope distinction.

## P30: source-consistent generic model actions

The audit reproduced a missed action boundary, rather than expanding the model's
research scope: an ordinary source-owned generator called `draw-trace`, whose
initializer revised its declared owner. The outer generator eventually refused
stale, but three draws and three advances had already run. The same generic
model pipeline could continue through normalization, observations and actual
steps after a registered source or a run-local specification became obsolete.
The fixed control refuses with zero draws and advances after that initializer.

`testing/property/model.ss` now uses the existing `with-sources` form at caller
actions: model initialization/admission/normalization/preconditions/transitions,
draw callbacks, expected and actual observations, actual steps, equality, and
fixture entry/normal return. The generator module exports that existing hygienic
form for ordinary module reuse. No extra callback objects, source directory,
model evaluator, scheduler or POO-dependent kernel is introduced. Explicit
`let*` sequences expected observation before actual observation, so refusal can
suppress the latter during argument evaluation. Exceptions keep their original
cause and multi-value transitions are unchanged. Standard `try`/`finally` still
owns cleanup; refusing a source does not roll back earlier effects. General lazy
Iterator consumption, finite trace caps and shrink delivery accounting stay.

Five independent cases exercise all six drawing stages, shared admission and
retirement, reference/actual/equality/setup/teardown revisions, original causes,
false data and multi-values, and transient specification refusal with balanced
cleanup and a fresh retry. The independent standard-library package now runs 92
cases. `examples/generated-traces.ss` adds one Record/FUN scenario across initial,
draw, precondition and advance revisions: no property is entered after refusal,
repeat runs retain the same stage boundary, and a fresh preparation successfully
checks commands whose nested Function fields still reject invalid arguments.
A new run may capture a new snapshot; this does not renew an old report's replay
authority or require permanent invalidation of a sampler object.

Seven additional laws in `PropertyScopes.lean` compose the existing
`guardedGeneration` for two dependent actions: stale preflight, first-action
revision, original cause, exact continuation, final revision refusal, unchanged
fresh results/state, and suppression of all later continuations. Repeated finite
composition gives the action-chain interpretation. Accurate pure observers,
faithful stage/state encoding, serial terminating actions and pure model
transitions remain premises. The laws do not verify Gerbil contracts, host
unwinding, hidden mutations, arbitrary callback termination, concurrency, GC or
wall-clock performance. Executable cleanup controls are separate evidence.

The design retains Rackcheck's [stream-based shrink-tree composition](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt)
and callback-oriented mapping rather than replacing it with an eager runner.
Registered revision checks are this project's extension, not a claimed missing
Rackcheck feature. Every newly protected action walks its active observer ledger;
no timing or zero-cost improvement is claimed. Existing resource limits and the
complete local/remote checks remain the acceptance gate for this revision.

## P54: demand-driven dependency-repaired trace trees

The audit reproduced unused framework work on the normal typed trace path: an
eight-command trace with shrink-budget one called all eight parameter shrinkers
and repaired the entire finite structural batch before returning its first
proposal. The accepted witness was already the empty trace. An exception in an
unused parameter callback could therefore prevent that budgeted witness entirely.
The value-only finite-list API itself is an explicit contract, not this gap; the
normal generated trace was incorrectly routed exclusively through that eager path.

The existing generic model module now exports trace-generator, a thin composition
of draw-trace and the ordinary generator constructor. The established core owns
iteration, source leaves, proposal charging and restart from confirmed values.
Its standard current?/sources options pass unchanged through a plain Scheme rest
forwarder with Gerbil using contracts; no second option parser or domain namespace
is introduced. No constructor invokes model initialization or generation callbacks.

One private trace-neighborhood uses sample-sequence's existing aligned deletions
and coordinate policy. A command exposes a finite, validated and owned parameter
spine, but allocates sample nodes only as its standard iterator is pulled. Each
requested sequence proposal is dependency-repaired once before yielding. Unused
neighborhoods invoke neither parameter callbacks nor repair; initial construction
still prepares a linear number of command nodes. After confirmation, the ordinary
value-generator tree rebuilds the next neighborhood from the REPAIRED commands,
not from raw nodes whose orphan dependents were removed. The raw sample-sequence
is only one neighborhood layer; it is not retained as the accepted trace's origin.

Typed trace-generator reuses that owned generic tree through make-generator's
existing generation field, while preserving its public draw/shrink/measure views,
Record contracts and declaration guard. An explicit derived draw/shrink method
continues to own a new callback protocol through the established ownership check;
the earlier default tree cannot silently override it. shrink-trace remains the
finite, all-or-nothing value-neighborhood operation. Its existing malformed-list
and pre-repair refusal controls are retained unchanged. These two contracts share
existing sequence algorithms; there is no legacy strategy selector or new runner.

Returned proposals keep the existing charge-before-admission rule. A failure during
repair or a parameter factory has not returned a proposal, so it adds no attempt;
previous returned structural proposals remain charged and confirmed progress is
retained. Exact false/object exceptions remain distinct from falsity and stale
sources. Paused iterators reject retirement before additional repair or producers.
A fresh factory may capture a new epoch; old reports/trees stay refused. Budget
cutoff does not probe EOF and cannot claim local minimality. A reached parameter
callback still owes a finite proper list; its own allocation/termination is not
bounded solely by the proposal counter. Existing process guards remain necessary.

Ten independent controls cover zero/one budgets, identical seeded draws and finite
neighborhood order, restart after orphan retirement, malformed demanded lists,
exact causes, repair interruption, paused/fresh ownership, constructor contracts,
and complete shrinking/replay against a first-difference fixture. Paired value/tree
controls run both orders at sizes 1, 8 and 128 with the same seed/model/property and
construction boundary: one requested proposal makes zero parameter calls in the
tree path, rather than one per original command. Initialization counts expose one
repair rather than the complete structural batch. These are work-count controls,
not wall-clock or GC speed claims. All 158 earlier independent cases remain and
the independent compiled receipt now requires exactly 168 cases.

Two typed controls cover zero/one budgets, nested command Function wrapping,
retired Type ownership and explicit callback overrides. The collection request
example composes the owned trace with a constant checked Function dispatcher,
Record packing, the existing product tree and FUN delivery. Real Trie indexed
deltas exercise inverse failures, old-value/index conflicts, source refresh and
stale tickets from the established lifecycle. A failing request shrinks without
orphan handles, retains wrappers, replays seed/concrete/portable witnesses, refuses
old ownership and explicitly prepares a corrected fresh passing request. The
reference oracle and actual indexed backend remain separate existing algorithms.

PropertyTraces.lean adds repairedTracePrefix using only take, map and the existing
retire. Nine finite laws prove eager-prefix agreement, repair-count budget, zero
demand, candidate validity and origin order, independence of unvisited parameter
suffixes, full-deletion selection and strict structural measure decrease. Examples
exercise orphan retirement and restarting from repaired commands. Existing guarded
action and interrupted-shrink laws continue to own source and exception semantics.
Faithful standard iteration, accurate sources, pure/terminating model transitions,
normalization and fixture simulation remain premises. This advances the paper's
future work; it is not compiler/runtime verification or a universal callback-cost
bound. No upstream source, scheduler, namespace or resource limit is changed.

## P59: trace request admission before declarations and fixture scope

The complete trace front door had two reproduced admission defects. A generic
`check-trace` request with a nonprocedure equality callback initialized its model
twice and opened/closed a fixture before failing. A typed `trace-generator` with
negative steps forced computed Command metadata before rejecting configuration.
These are static request errors; they should not acquire an application resource
or evaluate declarations. This is distinct from a valid callback throwing during
execution, which must retain its original cause and ordinary scope cleanup.

The existing generic model entry now uses Gerbil contracts for the model, proper
command spine and equality callback, alongside its existing fixture/preparation
contracts. The typed trace generator admits exact bounded
steps and a proper dependency spine before entering `with-trace-model`. The same
0–65536 step bound is preserved, with no clamping. Typed `check-trace` replaces
manual callable checks with the same standard parameter mechanism; `trace-property`
checks its fixture/equality binding immediately instead of deferring a static
error until after a property generator has drawn. `valid-trace?` still returns
false for an invalid trace, and domain mismatch, Boolean mismatch, stale sources
and callback exceptions retain their existing owners. No guard framework, new
namespace, wrapper chain or fixture scheduler is introduced.

The compiled regression also exposed a representation distinction at a known
improper command literal: the optimized call selected the unchecked entry while
the interpreted request refused. Gerbil's official MOP places `:pair` under
`:list`; that carrier fact is insufficient for PBT's proper finite-spine law.
The existing parameter/using contracts therefore use the existing standard `proper-list?`
predicate contract across finite sequence, specification, product, trace and
dependency boundaries. This retains an explicit properness judgment without a
new list implementation or wrapper. POO model/descriptor validation stays in
`with-trace-model`, preserving its TypeError rather than duplicating it with a
carrier contract; static callback/spine/budget failures use ContractViolation.
A compiled literal regression covers repair,
raw sequence shrinking and specification preparation before callbacks. The
existing finite-sequence Lean laws apply under truthful host shape recognition;
this is executable optimizer-path acceptance, not compiler verification.

Five generic regression cases cover all configuration dimensions before any model,
normalizer, preparation or fixture action; no cleanup for an unacquired fixture;
exact false/object callback causes with balanced acquired scope; and fresh empty
traces/false commands. The independent compiled stdlib-only acceptance grows from
191 to 196 cases. Three typed cases cover malformed limits/dependency spines before
computed metadata, binding/check configuration without declaration reads, and a
Record/Function service carried through dependency-aware generation, FUN delivery,
shrinking, seeded/concrete replay, old-source refusal and fresh corrected retry.
The oracle's reply is independent of the checked implementation Function. Invalid
binding performs zero draws or fixture actions; valid mismatches still open and
clean each acquired fixture once.

`PropertyTraces.traceStepLimit` records the existing finite integer interval.
Eleven Lean laws reuse `admitWitness` and `guardedGeneration` for static refusal,
valid forwarding, both limit boundaries, stale preparation, revision during normal
return, exact callback causes and exact result/state preservation. Top-level
examples distinguish successful false mismatch from thrown false and reject both
out-of-range endpoints. Host procedure recognition/arity, fixnum representation,
truthful source observers, terminating callbacks and actual fixture cleanup remain
executable premises. These laws do not prove callback purity, host contracts or
resource rollback. This is finite RFC future-work protocol completion, not an
extension into the original paper's compiler/runtime validation. Existing full
checks, negative controls and resource limits remain unchanged.


## P60: owned trace ingress and first-observed explicit dependencies

The audit reproduced a shared ingress ownership defect across typed validation,
repair, execution and generation. A computed Command declaration could replace
`(1 2)` with `(99 2)` before the model saw the commands. A computed declaration
could also replace an explicit dependency owner in the caller's list; retiring
the originally supplied owner then left the old sampler current. P59's properness
checks admitted a shape, but did not yet capture that admitted request before
computed declarations. The frozen baseline uses direct lazy declarations and
checks that caller rows/owners are unchanged immediately before API entry; effects
while constructing an already initialized Record are outside this boundary. Record
normalization may observe a getter more than once, without changing the captured
request or its first owner epochs. This is an actual protocol gap, not unrestricted payload
isolation or a new mutable-heap verification requirement.

The existing typed entries now capture the outer command/dependency spine before
`with-trace-model`. Validation retains malformed ingress as false; repair retains
its ordinary contract refusal after the POO model/Type boundary. Checking captures
its already admitted proper row before Record normalization. Empty proper rows
remain valid and false command payloads are not refusal sentinels. Computed metadata
cannot repair an originally malformed request into an admitted one, or redirect an
admitted row by replacement, truncation or a newly introduced caller-side cycle.

`with-trace-model` accepts optional initial owners and uses the SAME first-
observation ledger and transient source check. Generation supplies the copied
explicit dependency row there before any model field is read. Source retirement
during metadata refuses before the next getter; original callback exceptions still
escape unchanged. The normal no-extra-owner form is a syntax expansion, not a new
runtime guard layer. The final sampler retains the original declared identities,
so unrelated substitute revisions do not invalidate it and original-owner revisions
do. Retry is explicit new preparation; an old report never refreshes its stamps.

Six typed regression cases cover all ingress operations, edited/cyclic caller
aliases, initially malformed inputs repaired by metadata, owner replacement and
truncation, source retirement between getters, exact false/object causes and scope
unwinding. The complex Record/Function example stages private command rows and
uses the ordinary trace sampler and FUN property action. Metadata truncates only
the application's staging alias; the protocol executes its captured row, revealing
the faulty consumer instead of passing an incomplete trace. Dependency-aware
shrinking reaches open/use, nested Function contracts survive, concrete/seeded
replays agree, substitute-owner edits remain harmless, original-owner retirement
rejects replay before fixture opening, and fresh corrected preparation passes.
The property protects its generated witness by staging a shallow copy; PBT does
not claim that arbitrary property callbacks may mutate their own witnesses safely.
The independent generic library remains at 196 cases with no POO dependency.

`PropertyTraces.guardedTraceRequest` reuses `guardedGeneration`. Eight laws establish
stale preflight, exact metadata/execution causes, retirement refusal, original-
request handoff, ingress extensionality and exact successful result/state. Top-level
examples distinguish None from empty/false data, preserve duplicate owner IDs,
refuse retired authority and retain false exceptions. Faithful host shallow copying,
pure model/source observers and terminating callbacks remain premises. Payloads
are shared; there is no deep snapshot, concurrent linearizability, rollback or
compiler/runtime proof. Capture costs one outer-spine copy per admitted typed
request; metadata and epoch registration remain with their existing owners. No
wall-clock speedup is inferred. Existing complete acceptance and resource limits
remain unchanged. This continues the RFC's finite future-work protocol.

## P70: shared dependent declarations and closed source observers

The report-producing `testing/property` declaration now accepts the existing
binding syntax of `testing/property/test`:

```scheme
(property.define-property packet
  ((count count-generator count-domain)
   (payload (payload-generator count) payload-domain))
  (= count (length payload)))
```

Specifications are fixed declarations, prepared once in order before generation;
they cannot refer to values not yet drawn. Generator expressions may depend on
previous bindings. Hygienic expansion uses the existing `bind-generators`, product
specification and request admission. Parent shrinking rebuilds dependent suffixes
with captured seeds; independent coordinate shrinking keeps its original policy.
Seed and concrete replay consume the same retained report. The standard test
macro delegates to this declaration and adds only `do-check!`, authoritative
`require-passed` and named diagnostics. There is no additional interpreter, loop,
PRNG owner, replay recipe, namespace or runtime wrapper chain. The original
single-value report declaration remains its distinct, supported form.

Closed typed source observers now own a fresh stamp spine and stamp pairs BEFORE
reading optional hook metadata. They preserve supplied epochs, owner identities,
order and contradictory duplicates; they do not resnapshot or renew authority.
The private epoch fold is shared with the intentionally growing discovery ledger.
Absent `.current?` means no additional callback; a present value must be a
procedure. A procedure returning false still means stale, and exceptions retain
identity (including a raised false). Invocation checks epochs before calling the
hook. Standard procedure/list contracts, `map`, `every` and the existing dynamic
source scope implement this boundary. Mutable generated payloads remain shared.

Regressions compare named dependent declarations to explicit bind composition,
including counterexamples, attempt counts and seeded/concrete replay; cover
option admission before declarations and standard test delivery; and reject
snapshot alias renewal, malformed present hooks, conflicting stamps, changed
metadata and callback causes. A Record/Function service example composes through
FUN, shrinks dependent services, preserves Function wrapping, rejects old reports
and explicitly rebinds fresh authority for retry. The independent generic package
exercises the same declaration without importing POO.

Eight finite Lean laws cover shared preparation/delivery, dependent candidate
order, captured pre-metadata epochs, binding errors, absent hooks, false replies
and exact observer results. Existing dependent-domain and retained-source laws
continue to apply. Fresh host stamp copies, hygienic expansion, accurate declared
epochs, pure observers and terminating sequential callbacks are premises. These
are finite protocol proofs, not Scheme compiler/runtime verification, arbitrary
mutation isolation, concurrent publication or latency claims. This advances the
paper's future work. All checks and existing resource limits remain unchanged.

