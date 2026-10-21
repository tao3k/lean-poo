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

## Intrinsic numeric families

The companion Scheme implementation now admits its existing Number, Real and
Float runtime descriptors through the same finite syntax registry, recursive
compiler and numeric comparison used by integer intervals. Gerbil number?,
real? and flonum? remain authoritative; no generic ancestry-to-subtyping rule,
implicit value conversion or floating literal metadata is introduced.

`PrototypeTypeDescriptors.lean` adds numeric observation classes distinguishing
exact integers, other exact reals, flonums and nonreal numbers. Its
`numericFamilyCheck_sound` proves universal inclusion for Float/Real/Number and
integer interval views. `numericFunction_replacement` reuses the original arrow
variance theorem; `inferNumericFamily_sound` composes the existing whole
`inferDeclared` solver and preserves both original bounds and the exact artifact.
The existing top-level `Examples/PrototypeTypes.lean` covers rational/nonreal
separation and a prefix-specialized, uniquely selected Float declaration.

Scheme's `examples/numeric-services.ss` explicitly converts measurement tables
and calibrator boundaries using standard hash mapping and composition. The
existing qualified declaration, recursive Function, refine, bind-evidence and
FUN/IO protocols remain responsible for publication. Regressions retain Map-key
and carried-Type identity, ordered alternatives, keyword/case boundaries, policy
failure and independent retry. No Scheme checkout depends on this Lean project.

The semantic proofs require faithful interpretation of the host numeric
predicates and valid source function behavior. They do not establish arithmetic
or conversion accuracy, codec equivalence, arbitrary descriptor override behavior
or compiler/runtime correctness. This is the article's type-protocol future work.

## Rational and literal modulus protocol

The existing `Rational` descriptor uses Gerbil `rational?`: integers, exact
noninteger rationals and finite flonums are accepted; NaN and infinities are not.
It includes into Real/Number. Float does not include into Rational. Real can
include into a completely admitted flat ordered Union when both Rational and
Float are covered. This checks two obligations without changing branch order,
wrapper selection, invariant Map keys or carried descriptor identity. A missing
family, unsupported sibling or exhausted quota cannot become successful coverage.
Floating/complex literal metadata remains unsupported; no Any is synthesized.

`(Z/ n)` admits a literal positive exact modulus with at most 4096 bits. Admission
uses standard `positive-integer?`, and compilation constructs the existing Z/
descriptor whose recognizer is `uint-below?`. Its exact integer view is [0,n-1],
so endpoint, Enum and ordered flat Union rules reuse the existing interval solver.
No residue enumeration or modular `.normalize` is performed by validation or
inclusion. Whole finite candidates may choose different moduli; a modulus itself
is not a Type variable. Zero, negative, inexact, missing or extra arguments are
malformed; larger metadata is unsupported; insufficient work is exhausted. Each
parser pass charges one visit per 64 metadata bits, at most 64 visits, separately
from the shared syntax/search/compilation work. Catalog and wrapper quotas persist.

`examples/numeric-services.ss` now includes rational sensor batches converted to
residue tables, checked calibrators and checked batch callbacks. Conversion is
explicit producer behavior using standard hash mapping and composition. A second
real relay preserves exceptional flonums through the joint Rational/Float view.
Both reuse Input prefix specialization, whole Output inference, qualified method
fragments and the existing FUN/refine/bind-evidence action. Tests cover unique,
ambiguous and unsuccessful search, malformed/exhausted metadata, independent
host-predicate membership, immutable snapshots, nested argument/result refusal,
policy refusal and fresh retry. An invalid producer result is rejected, not reduced.

Lean extends the existing PrototypeTypes namespace: `numericFamilyCheck_sound`
separates finite/exceptional flonums; `numericFamilyUnionCheck_sound` proves joint
coverage with an actual member of the original target list. `residueRange_exact`
connects interval membership to 0 <= value < n; `residueRange_includes_iff` and
`residue_replacement` prove safe readable replacement for arbitrary admitted
moduli. `residueMetadataUnits_bounded` bounds metadata word visits without value
enumeration, and `inferNumericFamily_union` composes complete unique declaration
inference with ordered joint coverage while retaining the exact artifact. Existing
Function variance laws apply to nested calibrators. Host numeric classification,
faithful wrappers/binders, fixed input snapshots and source behavior are premises;
these theorems do not establish arithmetic/conversion/serialization correctness,
primitive allocation or GC costs, concurrent heap safety, or the host compiler.
This is an extension of the article's Appendix C/D type-protocol future work.
