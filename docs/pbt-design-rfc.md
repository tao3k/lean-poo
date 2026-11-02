# RFC: model-driven collection property tests

This RFC is the design entry point. Detailed protocols, examples, laws and
acceptance records live in the topic documents below; implementation receipts
are not duplicated here.

- Scope: finite, domain-aware generation; source-checked lazy shrinking;
  dependency-preserving stateful traces; and explicit seed/concrete/portable replay.
- Layering: generic modules under `testing/property` use Gerbil standard
  mechanisms; POO owns Type/Record derivation, validation and FUN/IO integration.
- Status: P0–P85 are implemented within their documented finite domains.
  Historical counts do not certify a new revision; both PR #13 heads require CI.
- Boundaries: callback termination, faithful codecs, truthful revision clocks
  and fixture/model correspondence remain explicit premises. This does not claim
  unrestricted inference, arbitrary cyclic evaluation or compiler/runtime proofs.

## Reading guide

Start with architecture, then downstream integration. Use the protocol topics
for implementation work and the recorded P-unit headings for a specific audit.
Each unit is owned by exactly one topic; related documents link to that owner.

| Topic | Contents | Recorded units |
| --- | --- | --- |
| [Architecture and source comparison](pbt/architecture.md) | Module ownership, source basis, scope and design decisions. | Design and acceptance |
| [Downstream integration and acceptance](pbt/integration.md) | Public surface, collection adapter, examples, proof placement and acceptance matrix. | Design and acceptance |
| [Generation control and source scope](pbt/generator-control.md) | Generator algebra, bounded retries, size controls and inherited source judgments. | P23, P24, P25, P26, P27, P32, P64 |
| [Data generation and retained products](pbt/data-generation.md) | Scalar families, finite directories, retained products and resource admission. | P13, P18, P21, P22, P28, P29, P47, P48, P55, P57 |
| [Typed descriptor discovery](pbt/type-discovery.md) | Recursive carriers, first-observed metadata and revision ownership. | P31, P37, P38, P46, P49, P50, P62, P63, P72, P79, P80, P81 |
| [Function generation and observation](pbt/function-generation.md) | Call declarations, demand-driven derivation and finite Function values. | P19, P33, P61, P74, P78, P85 |
| [Stateful models and dependency traces](pbt/model-traces.md) | Normalized commands, fixtures, repair and state-dependent execution. | P14, P20, P30, P54, P59, P60, P70 |
| [Lazy shrinking and interrupted search](pbt/shrinking.md) | Demand, proposal ownership, budgets and retained failure witnesses. | P17, P82, P83, P84 |
| [Counterexample replay and portable handoff](pbt/replay.md) | Codec identity, source consistency, bounded framing and replay failure semantics. | P15, P16, P36, P58, P73, P76 |
| [Preparation and declaration admission](pbt/preparation.md) | Reader configuration, factory ownership and checked preparation failures. | P34, P51, P52, P53, P56, P65, P68, P69, P71, P75 |
| [Property diagnostics and test integration](pbt/diagnostics.md) | Coverage, standard assertions, bounded inspection and report authority. | P35, P66, P67, P77 |

## Change discipline

Extend the existing protocol topic when a real gap is reproduced. Record the
implementation, negative controls, proof premises and complete-check evidence
there. Update this index only when the design or topic ownership changes.
Do not append per-round logs or duplicate a receipt across topic documents.
