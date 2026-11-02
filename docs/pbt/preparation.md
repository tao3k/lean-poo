# Preparation and declaration admission

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [P34: inherited typed preparation and aggregate measurement](#p34-inherited-typed-preparation-and-aggregate-measurement)
- [P51: closed bridge and specification preparation](#p51-closed-bridge-and-specification-preparation)
- [P52: Reader configuration and initial request admission](#p52-reader-configuration-and-initial-request-admission)
- [P53: ordered named-property declaration preparation](#p53-ordered-named-property-declaration-preparation)
- [P56: fixture lifetime admission before typed preparation](#p56-fixture-lifetime-admission-before-typed-preparation)
- [P65: shared primary-cause ownership during typed preparation failure](#p65-shared-primary-cause-ownership-during-typed-preparation-failure)
- [P68: shared static run admission before declaration preparation](#p68-shared-static-run-admission-before-declaration-preparation)
- [P69: owned factory result admission before subsequent binding](#p69-owned-factory-result-admission-before-subsequent-binding)
- [P71: shared observer binding before Map declarations](#p71-shared-observer-binding-before-map-declarations)
- [P75: joint admission of constant size and declared limit](#p75-joint-admission-of-constant-size-and-declared-limit)

## P34: inherited typed preparation and aggregate measurement

A registered ancestor can become obsolete during a typed sampler factory, a Map
key validator or a scalar measure. Refusing only after the whole aggregate is too
late: a two-entry Map reproduced `stale` with **two** weight callbacks before this
change, and with **one** afterwards. Preparation could likewise bind another field
after its first factory had ended the active parent's authority.

The existing `generator-core` and `weight` boundaries now use the generic
`with-sources` action. Map key validation inherits that same active scope while
retaining its own captured guard and representation-identity check. This protects
Map folds, trace command measures and product preparation through shared helpers;
there is no second fold, context registry or per-container wrapping protocol.
Normal totals, natural-number rejection, key-identity rejection and original thrown
causes retain their meanings. No authority is invented for a raw callback invoked
outside an owned action; an arbitrary custom factory still owns its internal
callbacks until it returns.

`examples/collection-properties.ss` exports `map-service-tests`: a fixed-key batch
of two service Records with nested Function fields. The existing product trees
supply value shrinking; the Map descriptor owns validation and its cardinality-plus-
sum measure. An obsolete first measure refuses before a second callback or shrink
step. Explicit re-preparation captures the revised owner, shrinks both values,
delivers through FUN, preserves Function checks and supports concrete and seed
replay. The old report remains refused. The six `sampler-scope-test` cases also
cover trace costs, later factory suppression, Map key suppression, exact exception
identity, fresh/empty totals and malformed measures. Map iteration order is not an
observable assertion.

`PropertyProducts.lean` adds `guardedMeasure`, a specialization of the existing
`guardedProduct`, and six laws: stale preflight, first-revision suppression,
original cause, empty total, exact stable cardinality-plus-sum, and refusal before
continuation. Existing product laws cover bridge/key preparation. The premises
are finite terminating serial callbacks, natural weights, fixed structural weight,
truthful source observations and a faithful host scope encoding. This logical
shrink measure is **not** a time/allocation cost proof. Host unwinding and Function
wrapping remain executable regressions, not verified Scheme evaluation.

Rackcheck's pinned shrink-tree map/filter implementation remains the reference for
composable lazy value trees. This unit preserves those trees and their force
policy; it does not change quotas, Map representation, key uniqueness, hash order,
shrinker provenance or replay identity. Registered dynamic source boundaries are
an explicit extension, not a missing Rackcheck guarantee. No performance claim is
made from callback counts alone.


## P51: closed bridge and specification preparation

The audit reproduced a post-snapshot admission gap: a generation getter retired
the captured Type, yet generator-core invoked its returned factory and published
a stale bridge. Attaching a guard only to later value pulls did not protect the
preparation callbacks already executed. This closes a concrete typed preparation
path rather than expanding the inference domain.

A private `with-source-stamps` form now reuses the existing dynamic generation
check and source boundary for both discovery and preparation. It reads only the
stamp variable and never invokes metadata or source hooks from its checker.
`sampler-generation` checks generation metadata, owned-factory return, raw draw
binding and source-hook binding in order. Stable factory #f remains the legitimate
raw opt-out; a retired #f return cannot enter fallback. Present trees containing
false data remain distinct from opt-out. Exceptions, including false causes,
escape unchanged. Scope exit restores the caller and does not roll back effects.

`prepare-sampler` binds generation then domain from the same captured stamps for
checks and diagnostics; it does not take a permissive second snapshot. Domain
measure binding is checked before later hook metadata. A check's known requested
Type is registered before its sampler descriptor getter; identity mismatch still
refuses before later declarations. Invalid false requests remain Type errors,
not absent-authority sentinels. Product preparation uses the same binder discipline.
There is no new public interface, namespace, parser, cache or wrapper chain.

The construction scope also protects nested pulls using the existing core protocol.
An obsolete factory cannot enter a nested generic producer. Arbitrary direct host
side effects or callback termination are not controlled or rolled back. Completed
generators retain their ordinary explicit source guard, not the transient checker;
normal draws, shrinking and replay keep their existing generic owner.

`service-factory-action` in the existing collection example reuses the Record/
Function producer and accepts an owned tree recipe. The complex regression retires
a declared owner before a bounded probe and verifies no producer/Function binding
runs. A fresh recipe finds and shrinks the deliberately faulty service, retains
wrappers, replays seed/concrete/corpus witnesses, refuses later retirement without
extra factory/producer effects and explicitly prepares a corrected passing service.
Controls also cover getter/factory ordering, raw opt-out, false data, nested pulls,
exact causes, expected-Type admission and scope release. Existing tests remain.

`PropertyPreparation.lean` imports the established scope/generation laws under the
same Functional.PropertyTesting namespace. Eight finite laws cover stale preflight,
retiring factories, exact causes, owned result selection, legitimate fallback,
fallback retirement/error and suppression of later metadata. Top-level examples
distinguish absent trees, false values, false causes and fresh authority. The new
files avoid further growing PropertyScopes and are part of the normal library and
complete example checks. Accurate clocks, faithful host binding/metadata, standard
dynamic scope and terminating callbacks remain explicit premises. These are
source/model laws advancing the paper's future work, not compiler, concurrency,
arbitrary effect or physical performance proofs.

Checks/diagnostics share one declaration snapshot. Pure epoch checks run at
preparation stage boundaries over its finite owner set; no transient frame is
stored or added to hot execution. Operation counts do not imply a wall-clock
speedup. The independent generic package remains at 148 cases and imports no POO.
No upstream, scheduler, resource-limit or full-acceptance changes are introduced.

## P52: Reader configuration and initial request admission

The audit reproduced a library-owned admission gap: a Reader policy getter
retired its known Type, but the later seed getter and draw still ran and the
report passed. Direct caller argument evaluation remains outside admission;
this fix addresses configuration getters invoked by property-action itself.
Automatic generator construction had the analogous window before the initial
request dependency snapshot. These are preparation-order bugs, not expansions
of inference or of the callback effect model.

property-action now copies declared dependency identities when constructing the
Reader recipe, then captures their current epochs with the configuration, Type
and supplied sampler at each invocation, before any configuration getter. One
private configuration-options reader uses the existing dynamic .slot?/.ref
protocol and checked source boundary. It reads size once, preserves optional
bare-object defaults, size zero, explicit scheduled-size limits and invalid false
policies, and returns ordinary keyword arguments through standard apply. There
is no replacement configuration class, new public protocol, namespace or runner.
The existing Map sampler's dynamic presence test also uses .slot? rather than
literal-name .has? syntax; shape contracts still belong to the existing Record.

check-property freezes its dependency spine and captures known request owners
before selecting an automatic generator. That authority protects generator
construction, metadata discovery and bridge binding; a later snapshot cannot
refresh a retired owner or erase one by replacing the caller's list spine. The
existing generic core boundary also suppresses nested producer pulls after
retirement. Final captured authority still belongs to the existing sampler/report.
No transient preparation checker is retained during trials or consumer IO.

A configuration exception escapes unchanged, including a false cause, before a
report/consumer exists. Once check-property starts, its existing preparation
report semantics remain: stale/error/exhausted are distinct and incomplete runs
are non-replayable. No effects are rolled back. Explicit fresh invocation captures
new epochs; it is not an automatic retry and cannot authorize an old report.

The downstream collection-properties example composes existing service recipes,
Record/Function contracts and FUN: an obsolete configuration stops all producers
and delivery, a corrected invocation finds and shrinks a wrapped faulty service,
seed/concrete replay reproduce it, later configuration revision refuses the old
report, and an explicitly corrected recipe passes. Regression controls cover
known Type/sampler/dependency retirement, exact causes, single configuration reads,
optional defaults, dependency-spine mutation, nested automatic-generation probes,
non-replayable refusal and scope release before consumer effects.

PropertyPreparation.lean composes the existing guardedGeneration and prepareBridge
models as prepareConfiguredBridge. Seven laws prove stale preflight, configuration
retirement, exact causes, option/state forwarding, factory retirement, stable
publication and suppression of a later consumer. Top-level examples include false
options/causes, exact state threading, stale opt-out and explicit fresh authority.
Accurate declared identity/epoch tracking, pure observers, terminating callbacks
and faithful sequential host/dynamic-scope binding remain premises. The paper's
prototype-composition model and RFC-pinned Rackcheck gen:map/gen:bind motivate
composition through existing values and shrink trees; they do not specify POO
mutable-epoch checks. This is future-work source/model verification, not a proof
of compiler/runtime correctness, arbitrary effects or concurrent atomicity.

The generic generator algebra, budgets, resource limits and complete acceptance
suite are unchanged. Additional transient owner checks occur only during preparation; fewer
configuration reads are not a measured wall-clock performance claim.

Reader source discovery preserves stable declaration failures through the same
private report runner as direct checks. The existing Option carrier retains an
original false cause without rerunning the failing getter, wrapping a substitute
sampler or skipping the consumer's ordinary error report. If the getter also
retired known authority, its original exception escapes before configuration;
no later configuration getter runs. This distinguishes original exceptions from
normal stale returns without refreshing epochs. The established Schema migration
regression and exact-cause/one-delivery controls cover this report boundary.
The preparation model's monadic consumer is a success continuation; application
consumption of an error report remains a separate, existing IO operation.

## P53: ordered named-property declaration preparation

The audit found a concrete gap in the public named-property forms: a generator
expression retired its already known specification and then ran a nested producer.
The final report was stale, but the obsolete producer had already executed. The
same window covered later fixed specification expressions in multiargument
properties. These expressions are invoked inside a library-generated declaration,
not ordinary caller arguments evaluated before an explicit check-property call.

One shared call-with-specifications combinator now owns ordered fixed declaration
preparation in the existing generic property module. It admits a proper list of
constructor procedures, copies its spine, evaluates each constructor once with
standard map-in-order, and registers the returned specification immediately.
Already captured specifications authorize each later constructor and the final
construction callback. Newly returned stale or malformed domains refuse before
any next callback. The existing with-current / with-sources / dynamic generation
checks also interrupt nested producer pulls. The combinator returns its callback's
exact values, including multiple values and false; there is no new carrier class,
registry, PRNG, namespace, framework or per-value validation wrapper.

Both define-property forms use this owner. The one-argument report form explicitly
prepares its fixed specification before the generator expression. The standard
assertion form prepares all fixed specifications in declaration order, constructs
the product specification and existing bind-generators tree once, then leaves the
preparation scope before checking. Dependent child generator expressions remain
inside the original bind tree, evaluated only when their preceding values exist;
no eager second runner or different split/shrink schedule is introduced. Property
names, named diagnostics, ordinary options, effective coverage and replay retain
their existing owners. Empty declarations use the same checked preparation path.

Construction exceptions, including false causes, escape unchanged. A normal return
that retires a captured domain raises stale property preparation before a run has
started; the library does not fabricate replayable evidence for an unconstructed
generator. The std/test form records that failure through Gerbil's ordinary
TestResult/nonlocal-exit mechanism. Negative assertion controls use a fresh standard
TestCase and inspect its exact result/cause; they do not contaminate outer results,
ignore unexpected errors, spawn another CLI or replace the complete acceptance.
Fresh explicit invocation prepares new domains, while old reports retain their
original observers and still refuse retirement.

Ten generic controls cover malformed/stale declarations, later-specification and
generator invalidation with nested probes, original false/object causes, ordered
single evaluation, multiple values, input-spine ownership, single/multiargument
macros, dependent trial counts, zero arguments, scope release, shrinking and three
replay forms. The independent stdlib-only library includes these same cases.
The collection-properties example composes a named declaration with existing typed
service generators, Record/Function wrapping and FUN Reader mapping. It rejects
an obsolete factory before production/delivery, freshly shrinks a faulty service,
replays seed/concrete/portable witnesses without rerunning its declaration factory,
rejects old evidence and explicitly prepares a corrected passing service.

The RFC-pinned Rackcheck gen:bind retains dependent child construction and its
child random checkpoint in the shrink tree. That remains our existing bind owner;
this unit fixes declaration preparation rather than replacing that algebra.
The author's modular prototype construction likewise motivates composition through
existing operations, not an additional testing runtime. Mutable-domain admission
is our stated future-work protocol, not a claim about a Racket epoch mechanism.

PropertyPreparation.lean reuses guardedProduct and scopeCurrent instead of adding
another evaluator. Six laws establish first-observed source refusal, retention of
old authority as declarations grow, exact ordered state/value forwarding, original
construction causes, refusal after construction retirement and publication of the
actual ledger without transient directories. Top-level examples include evolving
owner sets, stale new declarations, false causes and zero-argument ancestor checks.
Premises remain finite sequential terminating callbacks, accurate declared source
observers and faithful host scope/ledger binding. Sources not yet returned by a
constructor cannot be discovered inside it. Direct caller argument evaluation,
arbitrary host effects, rollback and compiler/runtime verification remain outside
these laws. No resource limit or complete check is removed or broadened.

## P56: fixture lifetime admission before typed preparation

The scoped differential protocol had two concrete admission defects. A typed
callback retained after check-trace returned read a later raw fixture's computed
State twice before the generic layer refused its closed use. Separately, a
with-system function could catch the second-use exception and return the first
observation; the generic layer then published that observation as a valid report.
These violate the existing one-use scoped fixture contract. They are not a demand
for unrestricted continuation safety, concurrent fixture use or rollback.

Generic check-trace now accepts prepare-system: (default identity). Gerbil's
ordinary procedure contract admits that hook before model initialization. The
existing callback owner counts each active invocation before entering preparation;
closed and repeated calls refuse before inspecting the raw value. Final delivery
requires exactly one invocation and the actual observation's identity. Catching a
repeated-use error cannot reset the count or authorize an earlier receipt.

The same callback installs one existing with-generation-check scope. A caught
reentrant attempt interrupts the next checked boundary, including nested generator
pulls, post-preparation admission and subsequent observation/step actions. No
lifetime observer is retained by the report or generated tree. A normally completed
scope keeps its historical observation; later closed calls merely refuse and do
not change it. Constructor, preparation and actual callback exceptions retain
their original causes when they escape, including false. Source retirement remains
stale; misuse is an error, never a false property or shrinkable counterexample.

Typed check-trace extracts its existing Record/TraceSystem preparation into one
named function. Its with-system wrapper now establishes only the prior dynamic
source binding and invokes the generic callback. Consequently lifetime admission
precedes retain/getter/validation/initial-state work. The original parameterized
fixture ownership still spans preparation AND execution, then restores model
ownership before application teardown. This relocates the original work rather
than adding a second validator or per-field lifetime wrapper. FUN actions and
the ordinary trace-property Boolean projection continue through this same owner.

The pinned Rackcheck map/bind/with-shrink algebra still owns generator composition
and retained trees. This fixture extension belongs to our stated model-driven PBT
future work, not a Racket source-epoch mechanism. Gerbil's standard annotated
keyword/default argument syntax and dynamic parameters supply the implementation;
no upstream change, runner, namespace, registry or framework is introduced.

Seven independent cases cover procedure preflight, closed callbacks after success
and failure, caught duplicates, preparation/observation/step reentry, interruption
of nested production, exact false/object causes, source retirement, omitted use,
substituted receipts and malformed prepared fixtures. All 174 previous cases remain;
the independent stdlib-only compiled library now requires 181. Two typed examples
cover raw computed getters and a complete Record/Function/FUN chain: misuse produces
an error with zero shrink attempts, fresh faulty fixtures shrink to a valid
producer/consumer trace, wrappers remain checked, seed/concrete replay reproduces
failure, a closed callback cannot retire live evidence, explicit source revision
refuses old reports and fresh corrected preparation passes with balanced cleanup.

PropertyTraces.lean adds admitFixture through the existing guardedGeneration and
fixtureReceipt over the scope's use count and observed identity relation. Ten laws
prove closed/repeated/stale preflight refusal, exact preparation/run causes, source
retirement before actual effects, normalized fixture/state forwarding and irreversible
refusal of earlier receipts after further attempts. Top-level examples distinguish
false payloads/causes, stale sources, substituted receipts and forbidden metadata.
Faithful sequential counters, standard dynamic-scope unwinding, accurate source
observers, receipt identity and terminating callbacks remain premises. Arbitrary
concurrent access, call/cc reentry, host evaluator verification and user-caught
exceptions outside the protocol are not proved. Resource guards and full checks
are unchanged; no latency or allocation improvement is claimed by these laws.

## P65: shared primary-cause ownership during typed preparation failure

The audit reproduced a typed error-reporting defect. An owned generation factory
raised a primary exception after its opaque observer became unavailable. The
initialization catch queried that observer again; a secondary exception escaped
and replaced the primary, so no report reached the caller. The frozen public
check-property probe recorded the secondary identity and zero draws/properties.
The generic kernel already protected primary causes during status classification.

The existing failure-status function is now exported through its ordinary generic
module and reused by typed initialization. No duplicate classifier, record, guard,
catch hierarchy or namespace is introduced. The typed handler passes the same
primary cause into its existing report builder regardless of classifier/observer
failure. Confirmed source retirement keeps stale status; unavailable or malformed
secondary observation gives error with the original cause. Existing bounded,
unsupported and core-interruption precedence remains. Reports created before a
generic execution exists keep replayable false, zero trial/shrink progress and no
property witness. Consumer IO stays outside this error-classification boundary.

Six regression cases cover delayed metadata and owned-factory failures with false
and object primary/secondary causes, malformed secondary Boolean replies, false
hooks and epoch-first retirement, existing controlled statuses/core interruptions,
exactly one FUN delivery and unchanged consumer exceptions, and an integrated
callback service. The service reuses ServiceSignature and its FunctionArguments
sampler, nested Function/List inputs, optional/keyword arguments, a checked target,
and the original supplied core. Injected binding failure produces one non-replayable
primary-cause report; explicit correction permits decreasing shrinking and concrete/
seeded replay of a real service fault. A later owner revision refuses old receipts;
a fresh corrected service passes. Older error reports retain their original cause
and never become falsifying witnesses. Source/metadata fields that fail static
request admission remain outside this initialization-report boundary.

Eight initializationFailure laws compose the existing classifyFailure model at
one fixed diagnostic context: primary identity and absent execution, interruption
and epoch precedence, observer/classifier errors, false observation, stable status
and non-passing outcomes under a lawful classifier. Top-level examples distinguish
false causes, secondary exceptions, skipped callbacks and bounded exhaustion.
The typed generation-status classifier and source observation are pure at this
context; host dispatch, record field fidelity, source accuracy, callback termination
and FUN/IO delivery remain premises rather than a Scheme runtime proof. The model
retains original diagnostic identity; it does not roll back failed preparation or
arbitrary consumer effects. No elapsed-time improvement is claimed. The independent
library remains POO-free, and complete checks/resource limits are unchanged within
the RFC's finite future-work scope.

## P68: shared static run admission before declaration preparation

The public report-producing define-property form accepted seed -1 only after
executing its specification and generator expressions (two observed effects).
The standard assertion form had the same window. Typed checks also deferred
policy, name and size-limit admission until after sampler metadata and binding;
a metadata exception could replace the static configuration refusal. These
library-owned preparation actions are distinct from ordinary caller argument
evaluation. Request validation must precede them, rather than turn malformed
configuration into a replayable run or resample it.

prepare-property-check in the existing generic property module binds the original
keyword/default signature through Gerbil itself, admits static controls, and
returns an ordinary callable check. It invokes no size/source/policy/classifier
callback while preparing. The direct check-property function, both declaration
macros and the typed/FUN runner reuse this owner. The typed runner retains its established immediate argument refusal boundary;
remaining generic configuration errors use its existing non-replayable preparation
report. Complete request admission now precedes sampler metadata in either case. No option parser, new namespace, request
record, alternate runner, wrapper chain, PRNG or compatibility path is added.
Actual generators/specifications are admitted when the prepared check is invoked.
Each invocation retains the existing execute implementation and its fresh random
source, visited-source ledger, trial counters, coverage and shrink state.

Static controls remain exact nonnegative seed/shrink/size-limit values with a
positive case count. Constant sizes are exact nonnegative integers; procedure
sizes still require an explicit finite size-limit. Policy/name and observer/error
classifier recognition reuse existing contracts without executing callbacks.
Generic/named refusal is an ordinary configuration error before declaration effects.
Typed/FUN retains its immediate argument errors and existing non-replayable error
reports for policy/name/size-limit refusal, without sampler/source callbacks.
Valid-request metadata causes, source retirement, Boolean property failures,
coverage, shrinking and both replay forms retain their existing owners. A prepared
check captures configuration, not source epochs or a completed report: source
admission still occurs for each supplied producer/specification and every action.

Three independent regressions cover the complete invalid-options matrix before
named expressions, standard TestCase refusal before fixed/dependent builders, and
callback-free preparation followed by independent shrink/replay runs. Existing
false-cause and declaration-retirement controls also remain. Isolated acceptance
increases from 200 to 203 cases. Two typed controls cover zero metadata/observer
work for malformed size-limit/policy/name and a nested Function/List service using
Record PropertyConfiguration, FUN, a bounded size schedule, failed-then-fresh
configuration, shrinking, both replays, old-owner refusal and corrected execution.
The named-row diagnostic cases move to existing product examples to keep scope
examples below 1000 lines; module inventory and registration order are unchanged.

Eight finite Lean laws reuse inspectionReady, prepareInspection and the existing
admitReplayRequest/guardedGeneration gates. They cover zero cases, malformed exact
controls, mandatory scheduled-size bounds, legal bounded schedules, hook admission,
invalid-before-preparation, valid-request equivalence and original causes. Three
top-level examples include invalid seed before a failing builder and false causes.
Faithful host keyword binding/normalization, contract recognition, source accuracy,
terminating callbacks and standard FUN/IO delivery remain premises. This advances
the paper's future work; it does not prove the Gerbil compiler/runtime, PRNG
quality, arbitrary effect rollback or performance. All complete checks and fixed
compiler/heap guards remain; tests have no fixed wall deadline.

A downstream suite may bind a request once with ordinary module imports:

```scheme
(import (prefix-in :clan/poo/testing/property p.))
(def run-request (p.prepare-property-check seed: 42 cases: 100 size: 20))
;; Each (run-request generation property specification) starts a fresh run.
```

## P69: owned factory result admission before subsequent binding

The bridge audit reproduced a wrong-phase effect: an owned factory returned #t,
yet generator-core still read the later .current? getter before reporting the
invalid result. An exception in that getter could replace the factory protocol
failure. P51 already promises a checked factory result followed by hook binding;
this is a concrete missing postcondition, not unrestricted callback inference.

The private checked-generation boundary in testing/type now returns only #f or
the exact generic generator. The existing make-generator constructor and
sampler-generation binder share it. It retains the original ordinary `generic
generator required` error and introduces no wrapper, normalization or observation.
Only #f opts out to raw binding; a generator producing false remains present.
The factory's existing source postcheck precedes result recognition, so retirement
still wins and original exceptions (including false causes) bypass recognition.
Valid bridges, raw fallback and typed error/stale report classification retain
their existing semantics. Error classification may still observe declared source
hooks under the existing classifier; it is not further factory/binding work.

Product and recursive scalar bridge preparation now use the already imported
standard map-in-order, giving explicit stop-before-next-binding order. There is
no new namespace, carrier class, cache, graph implementation or hot-draw check.
Core generation, retained shrink trees, PRNG ownership and replay remain unchanged.
A checked optional constructor value retains identity; from-generator still
requires a present generator and does not acquire an opt-out interpretation.

Three bridge regressions cover malformed result kinds before raw/hook getters,
constructor consistency, exact factory exceptions and source-retirement priority,
and product/Map/recursive combinations refusing without later binding, drawing or
packing. Existing #f opt-out and false-payload controls remain. A complex collection
service example uses Record/Function fields and the existing service-factory-action
through FUN: malformed factory error without a run, explicit fresh retry, real
shrinking, seeded/concrete/portable replay, retained Function wrapping, old-owner
refusal and a corrected passing service. These are POO bridge cases; the independent
generic library stays at 203 cases and acquires no POO dependency. Registration
and compiler module counts are unchanged.

Eight finite Lean laws extend the existing PropertyPreparation bridge model with
a pure raw-result recognizer. They prove refinement to prepareBridge for typed
results, stale preflight, source-postcheck priority, original causes, malformed
result refusal, present owned values, opt-out handoff and fallback retirement.
Top-level examples distinguish malformed presence, source retirement and present
false data. Faithful runtime recognition, accurate epoch observers, terminating
callbacks, standard ordered traversal and FUN/IO delivery remain premises. There
is no claim of arbitrary callback rollback, compiler/runtime verification or
latency improvement. This advances the paper's future work. Existing failure
categories, complete checks, heap/compile guards and unbounded semantic-test
execution are retained.

## P71: shared observer binding before Map declarations

The remaining duplicate observer reader in `map-generator` treated a present
false `.current?` value as absence. Construction still failed later at the core
bridge, but only AFTER a computed Key getter had executed. The public probe
recorded `refused key-reads 1`; this is an observable preparation-order defect,
not missing generation or a new research requirement.

One private `source-observer` now serves closed `source-guard` preparation and
the Map factory's growing discovery ledger. It returns the original callable or
absence, using existing `with-sources` and `require-value` before the next field.
No additional observer wrapper, cache, iteration policy or namespace is added.
The Map guard keeps its epoch-before/hook/epoch-after ordering and the ledger
still closes over first-observed declarations. Callable false results remain
stale; malformed Boolean replies remain errors. A metadata exception preserves
its exact cause, including raised false, while normal retirement during the
getter precedes malformed-result classification. Noncallable presence now
refuses before Key, Value, core factories, key validators or drawing.

`map-service-action` accepts an optional existing value sampler through the same
factory. Its default and existing callers retain their behavior. The complex
Record/Function/FUN example repairs malformed inherited metadata, prepares a
complete two-entry service directory, shrinks both services without losing
Function wrappers, replays the failure, rejects the retired report, and explicitly
prepares fresh authority for retry. Four preparation regressions cover malformed
presence, exact getter causes and retirement priority, callable false/non-Boolean
replies, old-root refusal and fresh retry. The independent generic kernel remains
unchanged at 205 cases; all existing checks/resources stay in place.

Seven finite Lean laws in PropertyPreparation classify absent, malformed-present
and callable-present metadata AFTER the existing guarded read. They prove stale
preflight, retirement priority, exact causes, unchanged absence/callable receipts,
malformed refusal and suppression of all later continuations. Five top-level
examples instantiate those distinctions. Host recognition of procedure identity,
accurate pure observers, first-observation capture, standard dynamic scope and
terminating sequential callbacks remain premises. No arbitrary callback rollback,
compiler/runtime proof or timing improvement is claimed.

The Racket comparison reuses pinned Rackcheck `gen:bind` (core.rkt lines 98-108):
its retained child random state remains the model for dependency regeneration.
This unit changes neither that seed schedule nor the existing shrink tree. The
additional revision/metadata protocol is this project's finite future-work
extension. Advanced handwritten sample producers and consumer-owned source
admission retain their existing contract; they are not redefined as this defect.

## P75: joint admission of constant size and declared limit

A constant `size: 2 size-limit: 1` is already known to exceed its finite envelope,
but the named property still evaluated both declarations before returning a
trial-one runtime error. A typed probe also read sampler source metadata, whose
raised false replaced the configuration error. This is a decidable request
relation at the existing P68 preparation boundary, not inference about arbitrary
size callbacks.

`prepare-property-check` now checks that a recognized constant fits its recognized
finite limit. Gerbil still owns keyword/default binding; one existing constructor
serves direct checks, both named declarations, typed checks and FUN execution.
No option parser, record, namespace, wrapper or source observer is added. Defaults
remain the constant itself; zero size/cap and equality with the cap are legal.
No generator/specification/source/size/classifier callback runs during this pure
request check. Invalid constants keep the ordinary configuration-error category.

Named declarations refuse before their specification/generator expressions.
Direct typed checks retain their existing non-replayable preparation error with
trial zero, no actual trial size and no reporting-metadata reads. Valid-request
metadata exceptions, including false, remain exact. Reader/FUN retains its prior
known-owner capture and configuration-getter precedence; the new relation is
checked after those options are normalized, before the owned factory binds.
Caller argument evaluation and explicitly constructed samplers stay caller-owned.

Scheduled sizes are recognized as procedures, never invoked or compared to the
cap during preparation. Their explicit finite cap is still mandatory. The existing
runtime natural-value and bound checks, actual trial-size diagnostics, original
callback causes, source checks, discard/coverage and both replay paths remain.
No runtime check or resource limit is removed.

Three independent cases cover impossible constant pairs (including large exact
integers) without observers/classifiers, inclusive/default/zero bounds with replay,
and lazy scheduled preparation with unchanged runtime overflow and false causes.
The existing named-report and standard-TestCase invalid-request matrices gain the
same bound relation. Two typed cases verify zero sampler/report-metadata effects
on overflow and exact metadata causes for legal constants. All previous cases
remain; the isolated package requires 219 cases.

The existing nested Function/List service example now refuses both an unbounded
schedule and an impossible constant before factory binding. A repaired constant
retains genuine shrinking, concrete/seed replay and Function wrapping; a subsequent
bounded schedule still works, old source epochs refuse, and fresh corrected
preparation passes. It reuses the same Record configuration and FUN action rather
than adding a separate service/test framework.

Eight new pure laws in PropertySizes characterize the exact inclusive constant
interval, absent/negative limits, malformed constants, overflow, zero, schedules
and monotonic cap enlargement. The existing propertyRequestReady now uses that
predicate with the normalized final size-limit control; its preparation/source
laws remain the sole composed gate. Four top-level size examples and two composed
preparation examples distinguish static overflow, source refusal and exact false
causes. Faithful keyword normalization, pure kind recognition, accurate observers,
existing payload laws and terminating sequential callbacks are premises. No
unrestricted callback inference, host/compiler verification or latency claim is
made. This advances the paper's future work.

The pinned Rackcheck size combinators separate sized selection and explicit resize
from generator execution. This unit follows that separation while keeping our
own finite cap and source-bound request protocol explicit; it does not attribute
our additional admission rules to Racket. Complete checks, original heaps,
natural compiler/test completion and cancellation behavior are unchanged.

