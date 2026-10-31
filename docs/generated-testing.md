# Declarative signatures and generated tests

This extends the descriptor construction described in the original Type
Descriptors / I/O Validation and Beyond section. That section names input/output
validation, pseudo-random generators and value compressors. The new concrete
Gerbil protocols advance that direction of future work; they are not presented
as an implementation already supplied by the Racket listings.

## Three-way correspondence

| Concern | Gerbil | Lean |
| --- | --- | --- |
| Required / optional positions, rest, declared and required keywords | `mop.ss` Function descriptors; `function-signature.ss` uses the host keyword escapes | `Functional.FunctionSignature.Signature`, `Call`, `accepts` |
| Ordered case-lambda shapes | `CaseFunction` selects first structural match; no fallback on type/body failure | `select_first`, `select_sound`, `invoke_type_error` |
| Supplied-only normalization | Child Types wrap nested Function values before one target invocation; defaults stay in the target | `supplied_length`, `invoke_shape_error` |
| Descriptor generation | `property-testing.ss`, explicit `.generator` extension, higher-order products | `samples`, `samples_length` under stable draw premises |
| Call-row generation | `FunctionArguments` in `function-testing.ss`; overlapping shapes draw the first selected clause's types | Structural selection laws, finite controls in `Examples/GeneratedCalls.lean` |
| Shrinking | Domain membership, strict natural measure decrease, retained falsity, finite attempt budget | `admissible_sound`, `shrink_preserves`, `shrink_budget` |
| Reuse | Reports capture descriptor/sampler/dependency revisions; stale outcomes and replay are refused | `admit_stale` |

The property model's candidate list is the observed stream, including candidates
generated after restart. Its fuel counts every proposal, not just accepted
shrinks. The model assumes callbacks terminate and return finite proper candidate
lists; host callback termination is protected operationally by the existing
process watchdog and heap limit, not proved by fuel.

## Acceptance and boundaries

`Examples/GeneratedCalls.lean` belongs in the top-level Examples directory.
The Scheme `examples/signature-service.ss` combines optional List callback fields,
keyword defaults, recursive Function wrapping, descriptor-driven call generation
and Reader/FUN consumption. Both repositories retain their complete checks and
resource limits. No Scheme runtime or test imports a Lean checkout.

Generators derive Bool, Integer, UInt, String, Exactly/Enum and bounded recursive
List, Tuple, Pair, Union, Maybe and OrFalse graphs. Other opaque Types,
refined Types and Function *values* supply an explicit `.generator`; the example
supplies a semantically chosen identity callback. Arbitrary closure synthesis,
inference and subtyping remain open. Automatic guarded recursive data generation
is now implemented; see [recursive-generators.md](recursive-generators.md).
Function call shrinking currently preserves the supplied shape and shrinks its
values. It does not promise deletion of optional parameters or global minimality.

A property must return a Boolean. Generation, validation, measure and property
exceptions remain errors with their original cause; they cannot produce a pass.
Zero trials are refused. Every trial and shrink result checks source revisions;
custom samplers must register additional mutable callback dependencies, or pass
those sources explicitly through `check-property`'s `dependencies:` argument.
Descriptors mutated during construction and undeclared ambient state are outside
the stable callback premise. This is sequential revision admission, not an atomic
concurrent publication protocol.

Replay fixes seed, trial count, size, shrink budget and sampler. Repeatability
requires the same host PRNG/runtime and stable callbacks/ambient state; it is not
a cross-runtime distribution theorem. A passed sample is not a universal proof.
`minimal?` describes only exhaustion of the supplied immediate smaller candidates;
budget exhaustion never certifies that minimum.

Recognition of a Function remains procedure recognition. Its checked invocation
requires a host procedure compatible with the declared formal signature. The
wrapper does not introspect or prove native arity, termination or side effects;
host defaults/body errors propagate. A declared keyword API uses Gerbil's standard
`#!key`/`#!rest` forwarding; signatures with no keyword API preserve legacy raw
positional keyword values. Source callback dependencies must be declared.


P58 closes portable handoff configuration and physical framing admission.
Gerbil parameter contracts run before observers/computed metadata; standard
reader EOF and a separately guarded physical EOF probe precede decoding. Invalid
requests leave caller ports untouched; malformed input may be consumed and needs
explicit fresh input. Revision/exception behavior and nested Function wrapping
remain with their existing owners. Eleven finite Lean laws model request/source/
framing order, assuming faithful host port operations rather than proving the
reader or I/O rollback. See [P58](pbt-design-rfc.md#p58-portable-handoff-request-admission-and-physical-framing).


P59 closes static trace request admission before computed declarations and
fixture acquisition. Standard Gerbil contracts cover generic/typed check requests,
typed finite limits/dependencies and trace-property binding. Existing model folds,
source checks, Record/Function wrapping and FUN delivery remain the execution
owners. Eleven finite Lean laws reuse Boolean admission and guarded preparation;
callback arity, termination and host cleanup are premises. See
[P59](pbt-design-rfc.md#p59-trace-request-admission-before-declarations-and-fixture-scope).


P60 captures typed trace ingress before computed metadata and registers explicit
owners in the existing first-observation ledger. Validation, repair, checking and
generation reuse the existing Record, source and FUN protocols. Caller spine edits
cannot retarget commands or dependency identities; payloads remain shared. Eight
finite Lean laws model the original request handoff and guarded preparation;
faithful host copying/observers and callback termination remain premises. See
[P60](pbt-design-rfc.md#p60-owned-trace-ingress-and-first-observed-explicit-dependencies).
