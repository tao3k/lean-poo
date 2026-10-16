# Qualified services and source-bound selection budgets

This increment uses three distinct references: the reviewed Racket constructions
in `fare/poof` at `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, existing
Lean semantic laws, and independently executable Gerbil implementations and
native paired controls. Scheme builds and benchmarks require no Lean checkout.

## Construction correspondence

Appendix B describes standard primary/before/after/around groups and alternative
labelled reductions. The native implementation uses the existing C4 sparse index,
Type validation, per-call guards, negative watches and atomic publisher. It adds
qualified carriers and combiners, rather than another dispatcher. Its qualified
service examples combine current capacity arithmetic, reserve/cancel contracts,
shared generic expansion and cross-service joint revision.

`Examples/AlignedServices.lean` reuses `MethodCombination.effective` and
`simpleEffective` to prove standard/simple reservation equality for positive
in-capacity arguments, plus pre-body around refusal for invalid capacity.
Existing method-combination semantics remain the general sequencing and
short-circuit proofs. Native tests separately cover ordering of side effects,
original arguments in `next`, warm guards, no method execution during negative
inspection, empty optional results, suffix failure avoidance and atomic refusal.
The Racket source describes these combinations; it is not a full differential
qualified-dispatch execution oracle.

## Invariant check reuse

`Contract.Checks` contains input/output predicates and a formula with equality
witnesses to the current source. `Checks.specialize_eq` proves that rebinding
current dependent meaning reconstructs exactly `Contract.withMeaning`. Every
existing invocation acceptance/refusal and exact returned-state law therefore
continues to apply. The record contains no executor, returned result or old
snapshot. Native `with-meaning` enforces sufficient reuse guards using immutable
source identities; derived input/output/rule changes fall back to fresh checks.
This proof does not establish native pointer immutability or compiler correctness.

## Complete conditional selector budget

For actual preparation entries `n`, fallback count `f`, selection cost `s`,
setup `u`, support guard cost `g`, excess collections `k` and collection price `c`:

- Dynamic reference: `n*s`.
- Cached choice: `u + (1+f)*s + n*g + c*k`.
- Strictly cheaper cached budget selects cached; ties select dynamic.

`SelectionCacheCosts.selected_bound` proves the selected budget does not exceed
the reference. `workflow_bound` adds the same explicit base for descriptor
construction, binding, generic expansion and approval. These stages are not
made free by selector reuse. `no_calls` proves retained-context revisions cannot
justify selector setup. The examples show cold, stable, fallback and GC-budget
choices. Counts and prices are supplied premises, not predictions of future GC
or elapsed time. Native `SelectionCacheCosts.` rejects malformed/negative counts
and uses the same arithmetic. Native `choose-source` compiles the fixed mode once
at configuration and returns the exact source on dynamic fallback. Source/price
changes require reconfiguration. `configuration_covered` separately charges that
setup and requires enough selector saving to amortize it; no-call/dynamic cases
do not make configuration free. The conservative example uses illustrative
operation weights, not copied benchmark timings.

## Native evidence and remaining coverage

The native matrix includes one-time policy configuration, repeated cold-family preparation, cold invariant compilation,
construction, binding, rebinding, generic refresh, approval, complete joint
publication, a 15-node shared DAG workflow and qualified standard/simple service
publication. Each direct pair uses independent fresh processes, fixed all-control
warmups, ABBA order, natural and explicit-GC regimes, source/binary admission and
retained adverse samples. Stage microbenchmarks are not additive attribution of
full publication time. Complete results stay in ignored native build outputs;
only a concise measured summary belongs in the PR.

The unified generalized protocol is future work in the original reference.
Precompiled unconditional qualified
methods, general safe-recursive attestation/memo and arbitrary cross-type lens
migration remain explicit native alignment gaps. Dependent Lean proofs are not
missing runtime wrappers. The existing original-source audit retains its
completeness flags; this increment does not claim the whole paper is implemented.

The companion native summary is
[qualified selection results](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/performance/qualified-selection-summary.org).
Its final 1,920 children passed admission. Configured dynamic versus forced
selection caching had joint CPU deltas -7.031us natural / +0.609us collected,
and shared-DAG deltas -3.609us / -3.246us. One-time configuration itself cost
+19.141us / +17.332us in its direct comparison. Cold invariant-check compilation
still regressed; qualified workflows remained mixed. These native observations
neither instantiate every abstract cost premise nor prove universal acceleration.


## Forwarding and superclass-controlled services

The current increment places general operational laws beside the existing
constructors in `Object.MultimethodCombination` and complex examples in
`Examples.AlignedServices`. It adds no source modules or JSON inventory changes.
`callForwardChain_reference` and `append` expose fixed-dispatch composition;
`innerChain_append` and `stop` prove inherited control and omitted descendants;
`simulaEffective_pair` and `prefix_failure` give exact ordering and retained
failure-state laws. Examples prove invoice enrichment, phase-local payload scope,
current reservation arithmetic and revoked preflight traces.

These three controls follow the existing Lean extensions of the reference's
open combination direction. Appendix B's Racket construction admits sorted
labelled fragments and a wrapper/getter/setter interface; it is not a verbatim
Racket implementation of these three complete APIs. Native tests separately
validate optional payload typing, warm guards without redispatch, omitted inner,
Simula effect order/failure, invoice-only dependency invalidation and negative
cross-service refusal. The native example helpers retain functional nested generic
ownership; complete timings include their cold nested resolution. General prepared
methods and nested warm-cache transport remain separate optimization work.

Check preparation now has an independent `TemplateCosts.choose` horizon. One
fresh parent keeps ordinary rebuilding; repeated service templates can amortize
stamped shared checks. `selected_bound` preserves the operation budget, while
`configuration_covered` separately requires the choice fee to be paid. The example
`cold_configuration_unpaid` proves a nonzero decision fee cannot be covered by a
single-use fresh mode: clients already knowing that case can use the ordinary
source directly. It is not a free first configuration.

`SelectionCacheCosts.compiled_eq` proves hoisting immutable fixed arithmetic
preserves every choice. `validation_sites` bounds six invariant domain checks and
the fallback relation, hoisted once, plus one argument check per entry against
rechecking every site on every entry. These are validation-site counts rather
than total instructions, allocation totals, cycles or GC predictions. The native
callback follows the same split; repeated configuration can reuse its validated
immutable policy. Descriptor and selector reuse have separate budgets: the
illustrative sustained service shares checks but retains dynamic selection.

The updated native observations, including cold-policy regressions and matched
A/A controls, are in
[control combination results](https://github.com/tao3k/gerbil-poo/blob/feat/positive-closure-costs/doc/performance/control-combination-summary.org).

The current admitted native study contains 1,728 fresh-process children, 18
scenarios, 10 fixed controls and six direct comparisons. Reusing a validated
policy saves 18.516us natural / 17.797us collected in configuration; cold fresh
checks versus shared have CPU delta -5.195us / -0.074us with residual deltas
-1.484us / -1.375us. First configuration still costs work. Complete-publication
results remain mixed, including Simula regressions and nonzero A/A deltas from
identical sources. Those controls and historical cold-policy regressions are
retained; these observations do not prove optimal native strategy choices.

## Prepared effective methods and nested owners

The reference's ordered-fragment/effective-method separation and the companion
book's eight-entry cache exercise guide this step. Unified generalized MOP remains
future work. `MultimethodCombination` adds prepared forwarding, simple, inner and
Simula constructors and equality laws to their existing combinations.
`PreparedMultimethod.EffectiveSound` requires cached arity and preparation agreement
for every current argument of the shape. `call_correct` and `call_preserves`, fresh
creation and all three registration laws establish the complete cache invariant;
guarded candidates still reselect and prepare each time. No cached result is used.

`NestedMultimethod.call` returns outer and child successors together. Its success,
dispatch-failure and child-failure laws cover arbitrary nesting. `callChecked`
additionally admits a concrete child-provenance predicate and proves it for every
published successor; the native implementation checks private index AND invoker
callback identity. Native pointer equality is not a proof of arbitrary Lean
function equality. `AlignedServices` composes the existing Simula prefix/suffix
preflight with an actual prepared child/outer owner and checks accepted/rejected
successive requests. General cache/effect laws are proofs; closed requests are
executable checks.

`EffectiveCosts.prices` reuses `TemplateCosts`: cold sparse resolution, unconditional
misses, EVERY guarded compilation, allocation and excess-GC budgets precede per-call
shape lookup, invocation and transport. `workflow_bound` retains construction,
binding and admission in a genuinely common base. For different wrapper/invoker
carriers, `chooseWorkflow` and `selected_workflow_bound` instead charge distinct
fresh/prepared construction, binding and approval bases. The cold publication
example shows why reduced carrier construction can justify a prepared workflow
even when effective caching alone cannot amortize. `cold` and `configuration_covered`
explicitly prevent unpaid first setup/strategy fees. Miss counters include edits
and eviction; supplied operation weights are not measured Scheme times.

Standalone Gerbil implements five `prepared-*` constructors on the existing typed
sparse index, an eight-entry fused resolution/effective LRU, explicit multi-level
`nested` cache ownership and complete forwarding/Simula joint revisions. Shared
native invoker descriptors specialize once to compact private runtime state;
cache successors do not reconstruct lazy POO descriptors. It needs no Lean checkout.

The current 960-child source/binary-bound native study separates child construction,
first complete publication, warm checked calls, joint revision+one call and joint
revision+eight calls, with natural/collected regimes, ABBA and two A/A controls.
Final reference/prepared warm CPU deltas are forwarding -2.892/-2.508us and Simula
-1.848/-1.719us (4/4 faster in each regime). Full workflows remain mixed:
forwarding natural single revision +4.727us, Simula natural cold +31.398us and
Simula collected single revision +26.570us (0/4 faster). Simula eight-call medians
are -17.477/-17.328us, while its natural prepared/prepared A/A median is +40.266us
with a +140.828us adverse pair. The prior compact-source study was more favorable
but is historical; it is not substituted for the exact-final-source result.
The ordinary reference stays the default and optimized models are explicit choices.
All final paired prefix counters match; that is not heap identity. Allocation
bytes are unavailable across GC, and these data cannot causally attribute all
full-workflow variation. No universal speedup or compiler-correctness claim follows.

The earlier descriptor-per-successor experiment and its regressions remain local
historical diagnostics. They are not a paired before/after causal comparison.
See the companion package's `doc/performance/prepared-invocation-summary.org` for
the concise tables, adverse controls, source boundaries and local receipt hashes.
Full measurements, binaries and archives are not committed.
