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
and uses the same arithmetic. The conservative example uses illustrative
operation weights, not copied benchmark timings.

## Native evidence and remaining coverage

The native matrix includes cold-family preparation, cold invariant compilation,
construction, binding, rebinding, generic refresh, approval, complete joint
publication, a 15-node shared DAG workflow and qualified standard/simple service
publication. Each direct pair uses independent fresh processes, fixed all-control
warmups, ABBA order, natural and explicit-GC regimes, source/binary admission and
retained adverse samples. Stage microbenchmarks are not additive attribution of
full publication time. Complete results stay in ignored native build outputs;
only a concise measured summary belongs in the PR.

The unified generalized protocol is future work in the original reference.
Forwarding payloads, inner/Simula helpers, precompiled unconditional qualified
methods, general safe-recursive attestation/memo and arbitrary cross-type lens
migration remain explicit native alignment gaps. Dependent Lean proofs are not
missing runtime wrappers. The existing original-source audit retains its
completeness flags; this increment does not claim the whole paper is implemented.
