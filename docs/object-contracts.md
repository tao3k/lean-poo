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
