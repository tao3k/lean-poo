# Literal singleton, integer-width and byte descriptors

This advances the article's Appendix C/D type-protocol future work. The Racket
reference supplies modular subtype obligations, not this finite candidate solver.
Runtime validation, finite syntax admission, inference and proof interpretation
remain separate obligations.

## Decidable coverage

| Descriptor | Admitted metadata and meaning |
| --- | --- |
| Null | The empty list, distinct from void and a zero-length byte vector |
| Unit | The void singleton; accepted by Maybe without evaluating its child |
| UIntN | Literal integer width 0..4096; inclusive 0 through 2^width - 1 |
| IntN | Literal integer width 1..4096; inclusive -2^(width-1) through 2^(width-1)-1 |
| Bytes | Any u8vector; identity validation, no copy/freeze of its mutable contents |
| BytesN | Literal integer length 0..65536; exact vector length |
| UInt256, JsInt, Bytes32, Bytes64 | Existing runtime descriptors, with their existing fixed width/length views |

Compilation calls the existing POO constructors and named descriptors. Gerbil's
std/number/misc predicates define the width membership used by named scalar
recognition. No modular normalize operation, byte conversion or host coercion is
used to make an invalid value pass. Metadata admission precedes exponentiation
or construction. Each width charges max(1, ceil(width/64)) shared work units;
syntax/search/normalization still consume their existing units. Large composed
requests can exhaust the default quota even when each individual descriptor is
supported. Callers retain the existing explicit budget APIs.

Widths are metadata, never Type variables or callback expressions. Whole Type
candidates can choose among different widths. Wrong arity, negative/nonintegral
widths and IntN zero are malformed; over-limit widths are unsupported; insufficient
work is exhausted. Neither incomplete inference nor refusal calls the declaration
builder. Negative completed comparisons, no solution, ambiguity and user callback
exceptions remain distinct. No Any is synthesized.

## Replacement and identity

Numeric widths reuse the existing inclusive interval and finite literal/ordered
Union coverage machinery. Exact endpoint checks include UIntN zero, which accepts
only zero. BytesN includes Bytes and the same fixed length; unbounded Bytes needs
a whole Bytes branch, since finitely many fixed lengths cannot cover every vector.
Null/Unit use intrinsic singleton recognition. Null and the empty Tuple share
readable membership; Unit supplies Maybe's void sentinel. Other optional payload
rules remain conservative, and public Union branch/Sum tag/Map key rules remain
unchanged. Wrapper-bearing Union alternatives still fail complete flat admission.

Aliases and interval views are not syntax normalization. Original source names,
widths and order remain in captured metadata and declaration artifacts. Invariant
Map keys do not change even for two extensionally equivalent spellings. Runtime
BytesN's existing descriptor cache can expose Bytes32/Bytes64 display aliases;
source identity is the captured syntax, not a forced rewrite of that cache.
Exactly/Enum's existing literal vocabulary is unchanged: named Unit/Null do not
admit mutable vectors or arbitrary literal expressions into metadata.

## Integrated acceptance and proof boundary

DescriptorServiceType prefix-binds Input and infers Output under Output <: Input.
Existing call observations constrain nested callbacks, then the same complete
qualified fragment builder installs the method. Null, Unit, signed-to-unsigned
and byte-buffer scenarios reuse infer-signature-calls and the common FUN/IO,
refinement, publication and exact evidence chain. Tests cover overflow and length
failures before callback effects, qualifier order, refinement failure/retry,
no-solution/ambiguity, malformed/exhausted admission, aliases and invariant keys.
Small widths additionally use an independent finite membership enumeration oracle.

PrototypeTypeDescriptors keeps the existing PrototypeTypes namespace and models
intrinsic descriptor identities, tagged value carriers, interval observations and
literal admission. intrinsicCheck_sound proves universal same-carrier inclusion
via existing IntegerRange.replacement; numericView_exact connects integer widths
to the existing range interpretation. Byte length never becomes an integer value.
metadataUnits_bounded proves the explicit width preparation charge is at most
1024, independently of value enumeration; it does not measure allocation or GC.
inferIntrinsic_sound reuses complete declaration inference to preserve both bounds
and the exact original descriptor pair, including alias identity. Integrated guards
and endpoint counterexamples are in the top-level Examples/PrototypeTypes.lean.

The new model is an intrinsic descriptor interpretation alongside the existing Ty
algebra, not a proof of the Scheme parser or every runtime Type constructor.
Projection/recognizer correspondence, optional wrapping, host calling conventions,
compiler behavior, serialization, mutation and cache implementation remain explicit
runtime premises and regression obligations. Arbitrary width expressions, host
predicate implication, implicit Class/Schema callback discovery, dependent
TypeValuePair catalogs, general Boolean algebra and unrestricted recursion remain
open or outside the current decidable boundary. Full resource limits and complete
local/exact-head CI checks remain enabled; no Lean checkout is used by Scheme.
