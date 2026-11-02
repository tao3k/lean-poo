# RFC: model-driven collection property tests

This RFC is the design entry point. Detailed protocols, examples, laws and
acceptance records live in the topic documents below; implementation receipts
are not duplicated here.

- Scope: finite, domain-aware generation; source-checked lazy shrinking;
  dependency-preserving stateful traces; and explicit seed/concrete/portable replay.
- Layering: generic modules under `testing/property` use Gerbil standard
  mechanisms; POO owns Type/Record derivation, validation and FUN/IO integration.
- Status: The documented finite protocols are implemented within their stated domains.
  Historical counts do not certify a new revision; both PR #13 heads require CI.
- Boundaries: callback termination, faithful codecs, truthful revision clocks
  and fixture/model correspondence remain explicit premises. This does not claim
  unrestricted inference, arbitrary cyclic evaluation or compiler/runtime proofs.

## Reading guide

Start with architecture, then downstream integration. Use the protocol topics
for implementation work and the feature headings for a specific audit.
Each feature is owned by exactly one topic; related documents link to that owner.

| Topic | Contents |
| --- | --- |
| [Architecture and source comparison](pbt/architecture.md) | Module ownership, source basis, scope and design decisions. |
| [Downstream integration and acceptance](pbt/integration.md) | Public surface, collection adapter, examples, proof placement and acceptance matrix. |
| [Generation control and source scope](pbt/generator-control.md) | Generator algebra, bounded retries, size controls and inherited source judgments. |
| [Data generation and retained products](pbt/data-generation.md) | Scalar families, finite directories, retained products and resource admission. |
| [Typed descriptor discovery](pbt/type-discovery.md) | Recursive carriers, first-observed metadata and revision ownership. |
| [Function generation and observation](pbt/function-generation.md) | Call declarations, demand-driven derivation and finite Function values. |
| [Stateful models and dependency traces](pbt/model-traces.md) | Normalized commands, fixtures, repair and state-dependent execution. |
| [Lazy shrinking and interrupted search](pbt/shrinking.md) | Demand, proposal ownership, budgets and retained failure witnesses. |
| [Counterexample replay and portable handoff](pbt/replay.md) | Codec identity, source consistency, bounded framing and replay failure semantics. |
| [Preparation and declaration admission](pbt/preparation.md) | Reader configuration, factory ownership and checked preparation failures. |
| [Property diagnostics and test integration](pbt/diagnostics.md) | Coverage, standard assertions, bounded inspection and report authority. |

## Change discipline

Extend the existing protocol topic when a real gap is reproduced. Record the
implementation, negative controls, proof premises and complete-check evidence
there. Update this index only when the design or topic ownership changes.
Do not append per-round logs or duplicate a receipt across topic documents.
