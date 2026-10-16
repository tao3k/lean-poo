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


## Declared Simula shapes before joint approval

The next increment advances generalized-MOP future work using the reference's
sorted-fragment/effective-method split and explicit caching direction. The actual
native joint approver discards `probe` cache successors, causing repeated cold
lookup/assembly before the first real request. Construction-time `prepareShape`
admits only unconditional declared shapes, after checking arity. It requires no
sample argument and evaluates no method body or value-sensitive guard. Calls
still validate current arguments and derive their own C4 shape.

`prepareShape_preserves`, `prepareShape_definition`, `prepareShape_reference` and
`prepareShape_call_correct` establish both cache invariants, definition/invoker
preservation and current-definition dispatch semantics. `prepareShape_probes`
extends agreement to a whole sequence of discarded-successor probes; no action
or result is memoized. `prepareShape_recent`, `call_recent` and nested
`call_retains` account for returning the existing prepared owner, while method
and contract actions still run. Closed examples exercise successful probes,
changed arguments and revoked source context.

`ShapePreparationBudget` reuses `EffectiveCosts` and counts declared entries,
discarded cold misses, real first entries and ALL invocations. The per-layer
`preparation_covered` law includes setup, owner allocation, unequal construction
bases and supplied excess-GC cost. `selected_bound` retains the ordinary mode
when that total cannot be paid, including unused declarations. Child and outer
layers can use distinct weights. These are conditional operation budgets.

Standalone Gerbil uses the existing resolver, protected certificates, POO
projection constructor chain and joint publisher. Child-only and both-level
Simula models expose the tradeoff explicitly. Preallocated cache entries count
against resource admission, so zero-budget initial publication can refuse earlier;
only method-reference semantics are claimed unchanged, not every budget decision.
The native suite preserves exact old versions on failed publication. Scheme has
no Lean checkout dependency.

The paired study isolates protected child construction, changed generic
construction, admission-style discarded probes, first successor transfer,
complete staging, cold/steady calls and complete joint revisions. A separate
fixed one-operation allocation control admits byte observations only when BOTH
sides avoid GC and retain nonnegative counters. CPU, GC and residual paired deltas
remain separate. Phase medians are not added; A/A spread and adverse runs remain
visible. See the companion package's `doc/performance/simula-publication-summary.org`
for current evidence. Earlier prepared-transport numbers above are historical.


### Sharing the Simula definition instead of capturing each view

The phase study showed that eliminating repeated effective assembly alone left
cold generic construction and joint publication regressions. The next native
representation supplies current view as a real typed argument to one immutable
protected child definition. `contextPreflight_equivalent` proves its entire
prefix/suffix computation equals the view-capturing implementation for every
typed view and argument; revoked traces follow from the existing failure law.
Native tests additionally cover Object/input validation and exact shared child
identity across capacity/invoice revisions. Current outer bindings and contracts
remain dependent on the new view.

`ContextPreparationBudget.prices` reuses TemplateCosts: first child definition,
negative checks, shape preparation and model binding enter setup; each changed
view still pays outer binding; EVERY probe/call pays its added context argument
Type/representation work. `sharing_covered` and `selected_bound` charge supplied
excess GC and show when the representation is affordable. Cold, unused, call-heavy
or collector-heavy horizons can retain ordinary captured-view construction.

The native cold control constructs a fresh shared child and its model binding;
steady revisions reuse the immutable child source. These are controlled phase
measurements after a common initialization prefix, not OS process-startup timings.
Complete native data remain local, with two A/A pairs and strict source identity.

Current native matched study (960 children): shared context versus previous
prepared transport saves 38.375/38.852 us per complete joint revision under
natural/collected GC, 4/4 faster pairs each. Recorded CPU-minus-GC differences
are -23.266/-21.766 us; the separately computed medians are not additive causal
components. GC-free one-operation controls admit 91,504 fewer allocated bytes
in all four pairs per regime, with zero bytes difference in context/context A/A.
Fresh child-plus-model factory cold publication instead costs +43.180/+53.852 us,
and warm invocation +0.197/+0.154 us. Explicit alternatives remain available.
Natural repeated A/A drift (-8.875 us) and collected outliers remain in the
native concise summary; no universal speedup, heap identity or retained-space
claim follows. Earlier shape preparation alone left full stage publication
slower (+4.727/+9.961 us). Both studies are retained as distinct local evidence.

## Compiled Simula callbacks and fused cold factories

The Racket fragment/effective-method split also permits compiling the complete
ordered side-method chain rather than building traversal closures per call.
`MethodCombination.compileParts` constructs a reusable monadic continuation;
`compileSimula` right-folds specific-first suffixes and left-folds general-first
prefixes. `compileSimula_correct` proves equality with `simulaEffective` for
arbitrary callback lists and lawful effects. Current arguments and failure order
are preserved. `compiledContext_equivalent` transfers the existing current-view
Simula equivalence, with accepted, capacity-refused and revoked examples.

The standalone native `compile-simula` uses standard folds and extracts each POO
callback only during preparation. Its existing typed sparse dispatcher, negative
certificate and FUN/IO publication/contract chain remain in control. A fused cold
`context-simula-template program` constructs the generic with seed, declarations
and projection in one prototype extension. The explicit reusable-template binding
path changes only the child seed; native tests assert projection/contract/admission
identity and independently supplied child identity, and exercise joint revisions
plus old-version refusal. No mutable global dispatch state is introduced.

`SimulaFactoryBudget` / `SimulaFactoryCosts` include once-only wrapper preparation,
every child/check/binding, callback construction, every current call and excess
GC. `selected_bound` and `compilation_covered` give supplied-operation bounds.
Direct cold construction uses its actual binding price and no unused shared
skeleton; a reused skeleton must still be paid once across its whole horizon.
Native cold and bind phases are separate controls. These proofs do not establish
compiler correctness, elapsed-time acceleration, heap identity or predicted GC.

The staged lifecycle composes these representations using the native Model's
`.prepare` override: initial publication uses the existing captured-view program;
`.publish` performs a checked handoff to the shared compiled definition. Every
warm call simply invokes its current version. Importantly, the family owner
changes at the first handoff, so the existing owner check rebuilds/rechecks the
complete family even for equal contexts. No certificate is retagged to hide that
cost. Later unchanged contexts use normal reuse. `stagedPreflight_equivalent`
and `stagedPreflight_stream` prove phase choice preserves current-view computation
and arbitrary request streams; the native tests separately check owner handoff,
subsequent exact reuse, current versus old capacity, shared subsequent children
and atomic negative-watch refusal. Module initialization is outside phase timings
and remains explicit setup in whole-horizon cost reasoning.

`ContextPreparationBudget.staged_bound` requires the later selected saving to
cover the workflow wrapper's extra binding. Its setup must charge the complete
first owner handoff; common initial captured-view work stays in explicit base.
This separates phase composition from a claim of free setup or unchanged
resource-admission timing. Native study details: simula-factory-summary.org.

The final 1056-child study compares staged versus previous context-prepared:
cold factory/publication/first call -35.773/-26.781 us, initial warm call
-0.171/-0.310 us (natural/collected; 4/4 faster each). Recorded CPU-minus-GC
cold differences -24.219/-15.586 us retain non-GC work separately. These phase
controls exclude module initialization. First owner handoff adds 2,192 allocated
bytes in all GC-free pairs versus previous context; stage/revision changes remain
mixed, including natural revision +6.133 us. Against original captured prepared
transport, cold -48.836/+18.242 us and initial warm +0.174/-0.053 us remain mixed.
No claim of universal speedup or eliminated post-handoff hot argument costs.
The first two pure-context studies failed to reliably remove cold/hot regression;
their adverse results and A/A drift/outliers remain in the native summary.

## Owner storage and post-handoff context binding

The standalone family keys are validated symbols. The opt-in sized-projection
mixin uses Gerbil's original native eq table with a support-length capacity hint for
new private tables; it still constructs/checks all generics at owner handoff.
The Lean `GenericFamily.Partial.emptyWithCapacity` companion (in the cost-model
owner) certifies no entries for arbitrary reserved capacity, preserving the existing
source model. No capacity hint supplies a method-origin or negative certificate.
The native tests cover duplicate/empty/invalid support and new-owner negative
refusal while keeping the old family usable.

`MethodCombination.bindSimula` specializes one context at reconstruction. Native
`bind-simula` directly calls each two-argument prefix/suffix with fresh units and
the bound view, avoiding an extra per-call context row and Object validation.
The bound child still validates current units and Unit output using the existing
sparse generic; the constructor validates the reconstructed Object once. Closed
projection immutability and pure Type callbacks are premises, not discovered from
successful samples. New views reconstruct new children; old versions retain their
own views. Arbitrary mutable context reuse or cached successful results is not
admitted by these claims.

`compileParts_contramap` and `bindSimula_correct` prove the transformation for
arbitrary callback lists and lawful effects. The concrete bound view laws and
examples retain capacity/release failures and state traces. `SimulaBindingBudget`
prices all binding/setup/call/GC work; `binding_covered` requires repeated-call
saving to cover reconstruction, and `tables_covered` combines independently
supplied table prices only when their inequality actually holds. Revision-heavy
horizons can keep shared context. These are conditional supplied-work bounds,
not proofs of elapsed time, native hash tables, compiler behavior or collector cost.
Current native study: simula-owner-summary.org, with separate post-handoff calls,
first and later revisions, unchanged reuse and GC-free allocation controls.

The final native binding shares the complete prepared program. Its
`prepared-context` invoker stores a private typed context, while `bind-context`
retains exact method/index/precedence/prepare/invoke/cache data and updates only
validated context owners. `PreparedContextMultimethod` models this using a prepared
result of type `Context → Result`; `bindContext_program`, `bindContext_sound`,
`call_correct`, `call_retains` and `call_context` prove the current-data/cache
boundary. Context is not an input to dispatch or guard selection; context-sensitive
applicability must stay in Args. `NestedMultimethod.callChecked_context_change`
formalizes rejection of a context change in a cache-only successor. Native tests
also attempt that replacement and retain the old child. The native eq capacity hint follows the Gerbil expander pattern. The earlier
symbolic-table trials, with and without shared program binding, were adverse and
remain separate evidence; their supplied price inequality does not admit them.

Isolated allocation controls located the remaining owner difference in generic
construction, with zero contract-binding byte difference for this trace. The final
owner path stages every fresh checked cell first, then privately copies comparable
service storage, prunes old-only keys and overwrites ALL current values. Changed
owners cannot retain old generic certificates. `overwriteStorage_current` and
`rebuiltLookup_reference` prove the resulting masked lookup is independent of prior
storage; `rebuiltLookup_certified` obtains authority only from the fully fresh
certified reference. Support contraction/expansion takes fresh sized storage. Pending
cells/copying/pruning are included in actual native allocation and supplied prices.
The native tests exercise same-cardinality key replacement as well as empty/subset
supports and a negative failure midway through the first owner handoff.

The fixed 13-scenario native study admits 1248 fresh children, with four ABBA
pairs per comparison and GC regime. Against pure compiled context the first-owner
allocation excess is 768 bytes, reduced from the preceding 2192-byte report;
against staged it saves 1424 bytes. Switched-owner hot calls save 96 bytes.
Isolated generic construction saves 1232 bytes against staged, while the isolated
contract-binding delta is zero; precomputed phase inputs forbid summing these
medians as a full allocation decomposition. Full first/later publication still
has CPU regressions, and eight-request publication is mixed. The fixed 256-request
burst improves three natural-GC pairs and all four collected pairs. These
results support explicit horizon-aware choices, not an automatic universal default.
The native summary retains A/A drift, prefix-counter differences, rejected backend
trials and independent source/binary identities. No full data is committed.

### Standard empty-storage construction

The next representation strategy uses Gerbil's existing `HashTable.new` interface
with an explicit positional capacity. A private empty eq-table descriptor is
initialized once, then supplies independent empty context/service tables. The
native first-owner path no longer copies old entries, stages pending pairs or
prunes old support. It still runs the same ordered projection, method registration
and negative checking. Later same-owner service changes retain ordinary COW and
exact unchanged siblings. Initial descriptor construction is not a free operation.

`GenericFamily.Partial.rebuild` composes the original certified `Partial.build`.
`build_lookup_eq`, `rebuild_lookup_eq` and `rebuild_empty_reference` prove pointwise
lookup equivalence and the first exact typed refusal for arbitrary ordered key
lists, including duplicates. These are operational constructor observations, not
just lookup laws over already successful cells. The actual native factory's
emptiness, immutability and compiler implementation are separate correspondence
premises. `EmptyStorageCosts.covered` requires the removed keyword dispatch,
staging/pruning work to pay interface setup and supplied excess collections;
construction, binding and joint approval stay in the common base.

AlignedServices reconstructs real heterogeneous reserve/cancel/quote services,
including duplicate reserve, zero/large capacity, revised reservation/invoice and
late forbidden cancellation. Illustrative cost cases reject short or GC-heavy
horizons even with cheaper table creation. Native controls isolate first/later
family construction, typed child binding and contract binding, alongside complete
publication and post-owner hot calls. Precomputed phase inputs forbid adding their
medians into an asserted full-workflow decomposition.

The source-bound 1248-child empty-storage study reports first-owner allocation
-2544 bytes versus prior bound and -1776 versus pure compiled context, eliminating
the preceding +768-byte difference in this trace. Later revisions save 1952 bytes
versus prior bound; isolated typed binding still costs 320 bytes versus a shared
unbound template, and isolated contract binding is unchanged. Later complete
revision CPU improves -5.188/-6.227 us versus prior bound (natural/collected),
with residual CPU -5.430/-3.922 after recorded GC. It still loses +0.531/+1.797
against staged. Natural first-revision CPU loses +23.695 us against staged;
A/A drift cannot erase that observation. Therefore the native strategy stays
explicit, with no universal cold/startup/timing claim and no pooling of old runs.
