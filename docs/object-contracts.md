# Structural value contracts and composed admission

The original Racket text's section 5 describes type descriptors as ordinary data
with recognizers, I/O operations and additional constraints. Appendix B explicitly
leaves generalized prototypes to future work. This implementation uses that Type
and lens vocabulary. Diagnostic composition and the checked observation workflow
advance the future work; they are not a new Scheme type system or a claim that
all type-system TODOs are closed.

## Three corresponding layers

| Responsibility | Gerbil | Lean |
| --- | --- | --- |
| Ordered refusal accumulation | `object-diagnostics` `diagnostic-all` | `ObjectDiagnostics.all`, `all_nil_iff`, `all_append` |
| Gated phases | `diagnostic-then` | `andThen`, refusal/acceptance/associativity laws |
| Finite shape and optional ancestry | `ObjectContract.` | `ObjectContract.View`, `Contract`, `diagnose_nil_iff` |
| Required field semantics | existing Type recognizers and diagnostics | `required_semantics_iff` under an explicit checker law |
| No undeclared field reads | slot-name inventory, then declared `.ref` calls | `required_lookup_congr` |
| Existing invocation boundary | `metadata.typed` / `metadata.invoke` | `predicate`, `predicate_holds_iff` |
| Value admission before a consumer | `checked-action` using existing `Observation.` bind | `checkedAction_refused`, `checkedAction_accepted` |

`View` is an explicit finite observation adapter. Its lookup must correspond to
actual Scheme slot lookup and its names must enumerate actual public slots. A
stored false value is a present value, not a missing lookup. The model has no
foreign implementation oracle: it proves the supplied finite interpretation.

## Four phases and two distinct kinds of failure

Non-object/ancestry refusal precedes field observation. Inventory and required
field errors accumulate. Only their empty result enables whole-object constraints;
only successful constraints enable obligations. Ordinary issue lists accumulate
inside a phase. Scheme callback exceptions stop execution and retain their exact
identity; malformed issue lists are programming errors, not user-field refusals.
The pure Lean list laws do not prove arbitrary callbacks terminate or model
exceptions as ordinary diagnostic issues.

Membership uses empty diagnostics. Semantic soundness/completeness of custom
Types requires the explicit law that empty diagnostics agree with that Type's
recognizer. Merely supplying a `.diagnose` slot is not a proof of that law. Path
accuracy for user callbacks is also their responsibility; format checks alone
cannot prove a domain-specific path correct.

Inheritance of a descriptor is ordinary override, not a theorem of subtyping.
Replacing required fields or obligations can weaken a contract. To retain
independent obligations, compose them with `diagnostic-all`; do not infer logical
refinement merely from prototype ancestry. Closed parent inventories can also
reject newly introduced fields; explicit schema delegation owns that policy.
General polymorphism, subtype inference and type-driven generators remain open.

## Executable composed scenario

`examples/object-contracts.ss` decodes through the existing `io` Json methods and
preserves all input keys. The shape contract runs before lens arithmetic. A
persistent revision then produces a separate candidate; the complete contract
checks capacity and transport relations before the consumer writes JSON. Two
relation failures accumulate with their full paths. Reusing the action checks each
new input; no accepted-result cache is introduced. Function Type validation still
passes its actual wrapped procedure to the consumer, including multiple returns.

`Examples/ObjectContracts.lean` uses the same five service fields, Int-valued
capacity/use, and the exact 1–65535 port interval, with an explicit port-recognizer
equivalence theorem and negative-integer controls. It checks false versus
absence, ancestry gating, accumulated relationships, invocation input refusal and
normalization boundary. Scheme tests independently exercise actual slot laziness,
receiver-local descriptor preparation, JSON I/O, persistent updates and exceptions.
Neither fixture proves the parser, arbitrary MOP overrides, compiler/runtime,
resource performance, external authorization or automatic dependency discovery.
Descriptor declarations are immutable during use; normal source/revision discipline
is still required when a consumer introduces mutation. Callback external effects
are not rolled back by refusal.

## Explicit strengthening and invocation association

`Functional.ObjectContractRefinement` adds `refine`: shape and existing constraints
stay effective, and an additional diagnostic phase runs only after the full
original contract accepts. General laws characterize acceptance as conjunction,
preserve the exact original refusal report, and prove associative regrouping.
Gerbil uses its existing `=>` inherited computation, so this phase is rebound to
the effective descriptor even after preparing a parent. This is not an inference
that ordinary descriptor inheritance is subtyping. Custom MOP overrides must
still honor the structural protocol.

`Functional.EvidenceBinding` models the companion's existing `bind-evidence`.
It relabels the original formula into an `Option` atom space and appends a fresh
binding atom, preserving all original connectives and input/output policies.
Acceptance retains the original rule and exact subject/descriptor/context
associations. Under admitted input/output and a returned candidate, mismatch
refuses in the logic phase and publication retains exactly the old state.

The identity carriers must model reference identity; equality of serialized
records is insufficient. The model assumes a total pure projection. Actual Scheme
`eq?`, receiver preparation, projection exceptions and retry behavior have
separate executable controls. Matching freely constructed fields is not authority
or freshness. Bind from the original invocation template for a new context;
nesting bindings retains the earlier obligations, including obsolete ones.

The finite publication scenario is in `Examples/ObjectContracts.lean`; the Scheme
counterpart is `examples/contract-publication.ss`. It uses checked FUN admission
before state production, then the existing invocation publication protocol. The
original paper's section 5 supplies recognizers, type descriptors and I/O; these
explicit strengthening/binding operations advance Appendix B's future work and
the user's structural contract design. They are not claimed as original Racket
APIs, an authenticated receipt system or a proof of effect rollback.

## Nested Function validation and bound publication

The companion `object-contract-validation` now distinguishes structural recognition
from explicit validation. It recursively validates declared ObjectContract fields,
reuses existing Function wrappers, batches changed fields into a persistent object
inheriting its source, then checks full diagnostics and refinement on the checked
root. No change retains exact identity; Function wrapping changes the candidate.
`checked-action` and `bind-evidence` use that actual returned root.

`FunctionValidation.lean` proves input/source/output gating and successful output
normalization, including function-valued output without decidable function equality.
`ObjectContractValidation.lean` reuses ordered `Validation.traverse`: failed batches
cannot reach commit; successful batches retain their supplied representation laws.
It proves final refinement on the normalized root and combines admission with the
existing binding theorem on application-supplied reference identifiers.
`Examples/ObjectContracts.lean` adds dynamic argument/result rows, higher-order
callbacks, normalized reference binding, raw/stale refusal and current retry.

Proofs cover total pure callbacks and finite declared batches. Representation laws,
reference/identity correspondence and immutability remain premises. Scheme tests
exercise actual wrappers and exception identity; neither layer proves the parser,
compiler/runtime, arbitrary cyclic object termination or rollback of effects.
Other container families, external schema adapters, optional/keyword arities,
wrapper deduplication and higher-order blame remain open. This extends the paper's future generalized
prototype work; section 5 supplies the Type descriptor recognition/validation basis.

## Container recursion and finite schemas

The existing Scheme List/Tuple Types now recursively call child validation and
return complete wrapped containers. A shared structural traversal checks proper
lists and exact tuple arity before normalization, follows nested ObjectContract
schemas without prematurely running their refinement, and records zero-based
indices in diagnostics. No source list/vector is mutated; unchanged containers
retain host identity. Named-field schemas are existing ObjectContract descriptors,
without a new schema DSL. Arbitrary external Schema Types need explicit adapters.

`LeanPoo/Functional/ContainerValidation.lean` reuses ordered traversal and the
object validation pipeline. Its nine laws cover successful position-wise
normalization/length, unchanged values, tuple arity and positions, final checked
acceptance, original child errors and schema refinement. The previously proved
`validated_binding` law applies to the exact final container reference.
`Examples/ContainerContracts.lean` composes a task list, finite schema, heterogeneous
tuple and Function list, including two returned values, sequential transforms,
refinement failure, malformed tuple, callback output rejection and raw/stale
reference refusal followed by current retry. Scheme exercises the corresponding
actual wrappers through JSON/FUN and bound publication.

The Racket `ListOf` in section 5 provides recursive membership; the new wrapping
composition advances future generalized-prototype work. Proofs interpret finite
pure callbacks, vectors as tagged rows and immutable identities as supplied IDs.
The fixture's named inventory is fixed by its Lean record type. Host representation,
parsing/runtime correctness, arbitrary external adapters, cyclic closure, wrapper
deduplication and higher-order blame remain outside these claims.

## Pair, Map, Sum and Union

The companion `variant-validation` now integrates the four existing Type
constructors with shared structural traversal. Pair validates both positions;
Map normalizes keys and values without changing the source, preserves the host
hash policy through `hash-new`, and refuses normalized-key collisions; Sum checks
tag before payload and installs the returned wrapped payload while inheriting its
source. Union recognition remains existential, while normalization commits to the
first structural branch and checks its own returned value. Selected errors cannot
fall through to a more permissive alternative. JSON dispatch is unchanged.

`LeanPoo/Functional/VariantValidation.lean` adds sixteen laws for components,
normalized map positions/length/collision checks, Sum tag/payload preservation,
ordered structural selection, unmatched branches and committed Union errors.
Final refinement and exact-reference publication reuse the existing object laws.
`Examples/VariantContracts.lean` composes Pair → map snapshot → Sum → Union →
refined Function schema and an approval callback. It covers active/data variants,
invalid tag, collision, Union fallback refusal, wrong output, root relation and
raw/stale evidence rejection followed by retry. The Scheme example uses existing
JSON/FUN and named route execution, without relying on host map traversal order.

The finite model requires table-key equivalence to agree with actual host hashing,
valid Type declarations, total pure callbacks and immutable reference mapping.
It does not prove Scheme identity/allocation, the hash implementation, JSON parser,
compiler/runtime or external effect rollback. Ordered committed Union validation
is not equivalent to existential membership. These are explicit future-work
extensions of the section 5 descriptor constructs, not a claim of whole-paper
completion. Other Type families, cyclic closure and wrapper deduplication remain.

## Sentinel optionals and TypeValuePair

The companion `optional-validation` extends Maybe, OrFalse and TypeValuePair through
existing Type/structural methods. Void and #f keep distinct representations; absent
branches do not even demand their child Type. Present validation locks the selected
child: a wrong Function result cannot become outer absence to evade checking.
Sentinel results remain legal when the child Type explicitly accepts them.
TypeValuePair now checks the carried Type, validates the payload rather than the
whole pair, and retains that exact Type alongside the actual normalized cdr.

`LeanPoo/Functional/OptionalValidation.lean` adds ten laws for sentinel identity,
shape/child errors, selected membership, complete acceptance, invalid descriptors,
descriptor retention and dependent payload success/failure. Existing ObjectContract
refinement and binding proofs provide the final composition. The worked Scheme
pipeline uses optional typed plugin rows and optional fallback through JSON/FUN,
refinement and exact binding. `Examples/OptionalContracts.lean` executes matching
present/absent paths, wrong carried interfaces, output refusal and current retry.

The typed fixture fixes its record/container grammar, uses descriptor/reference
tokens and supplies a pure host correspondence. It does not certify dynamic
parsing, host identity/allocation, compiler/runtime correctness or effect rollback.
This advances section 5 descriptor/generalized-prototype future work. Class-specific
policies, external schema adapters, cyclic closure and wrapper deduplication remain
open; the I/O formats and executable-value serialization limitations are unchanged.
