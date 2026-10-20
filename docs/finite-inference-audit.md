# Finite inference audit and witnessed emptiness

This extends the article's Appendix C/D type-protocol future work. The Racket
reference motivates explicit subtype and modular-extension obligations; it does
not implement this finite candidate inference algorithm. An empty record value
used as a composition seed is inhabited and is not an empty Type.

## Remaining substantive coverage

| Priority | Finding | Acceptance / next boundary |
| --- | --- | --- |
| P2 finite Or protocol | Runtime Or lacked recursive wrappers and inference admission | CLOSED through existing ordered selection, shared selected-child normalization and all-branch source coverage. Original Or membership selection, Union structural selection, descriptor kinds, Map keys and codec boundaries remain distinct. Complete callback-directory publication and conditional Lean laws are covered. |
| P2 first | Impossible mandatory products/rows were refused across kinds | Implemented here: positive finite emptiness witnesses feed the existing replacement judgment, shared inference, ordered parameter specialization and whole declaration admission. |
| P2 covered | Runtime Null/Unit and fixed-width numeric/byte descriptors | Closed for literal bounded UIntN/IntN/BytesN, Bytes, singleton names and existing fixed aliases; see intrinsic-descriptors.md for admission, interval/carrier and artifact laws. Dynamic widths remain unsupported. |
| P2 bounded catalog | TypeValuePair and captured Class/Schema catalogs | Implemented for explicit finite stable directories and snapshot-local identity tokens. Arbitrary dependent/callback discovery remains unsupported; see intrinsic-descriptors.md and the maintained Gerbil audit. |
| Outside current boundary | Arbitrary predicate implication/emptiness, implicit principal or higher-rank inference, unrestricted recursive language inclusion | Unsupported; neither samples nor an Any fallback establish these laws. |

Existing finite Function/case language, keyword-origin, Pair/Map/Sum/Union and
explicit Object/Record protocols retain their documented bounds. This audit does
not claim complete runtime Type coverage or mark every TODO complete.

## Implemented judgment

The parser first admits both complete finite expressions. Comparison retains its
existing fast successful path; only a failed judgment attempts empty-replacement?.
empty-type? consumes the existing shared work counter and reuses range-bounds,
empty-range?, field-required? and Gerbil's short-circuit list combinators:

- Never, empty Enum and reversed finite integer ranges have no accepted value.
- Tuple/Pair need one empty mandatory child.
- Nested Union/Sum need every alternative payload empty, including zero alternatives.
- Object fields are mandatory; Record requires an explicitly required empty field.
- List/Map can be empty collections. Maybe/OrFalse have sentinel inhabitants.
  Optional fields, procedures, opaque Types and unknown predicates cannot prove
  emptiness. A negative witness search does not prove inhabitation.

Direct Union and Sum sources keep their existing branch/tag replacement protocol,
even if empty. Union targets still require complete flat intrinsic admission;
an empty source cannot hide wrapper-bearing alternatives. Map keys retain exact
normalized identity. No descriptor is
rewritten to Never, deduplicated, reordered or replaced by Any. A witnessed empty
enclosing product may cross carrier kinds: this is vacuous readable inclusion,
not a permission to convert values, mutate slots or bypass validation.

Explicit Mu uses its existing finite approximant only. Nothing here discovers
emptiness of an unrestricted recursive fixed point. Both admission and witness
work remain bounded; malformed/unsupported syntax, negative judgments, exhaustion,
no solution, ambiguity and callback exceptions retain distinct outcomes. An empty
candidate can satisfy a bound; inference does not claim that an observed Type has
a realizable runtime value. Builders run only after complete unique inference.

## Integrated checks and proof scope

EmptyCallbackServiceType prefix-binds Value and infers a structured Dead callback
input under Dead <: String. It reuses infer-signature-calls, the typed qualified
fragment builder and the common refinement/publication/evidence action. A real
UInt call succeeds; its returned callback retains the impossible input wrapper.
The regression checks refusal before callback effects, negative refinement before
consumer admission, retry, no solution, ambiguity, admission/quota failures,
required/optional rows and inhabited empty-container/sentinel controls.

Lean's EmptyType and emptyCheck_sound prove finite witnesses. EmptyLaws exposes
scalar emptiness and carrier projection/selection premises; EmptyType.refuses
then proves universal rejection, not a finite sampling claim. requiredField_refuses
states the required-field projection law independently of row representation.
The existing check/check_sound, Subtype and replacement theorem include the new
rule, while Union branch, Sum tag and Map key invariants remain proved.
Examples/PrototypeTypes.lean proves the disabled callback fixture and exact
inferred declaration artifact after prefix specialization.

These are conditional denotational laws. Host predicate identity, required-field
projection, parser behavior and runtime wrappers are separately tested; the Lean
model does not prove the Gerbil compiler, callback termination, GC or allocation
costs. The row lemma requires an actual required-field projection premise, not
an inference from nominal Class ancestry or a proof of the Scheme row compiler.
No Scheme source or test depends on a Lean checkout.

### Impossible tagged payloads

The existing Sum-to-readable-row judgment reuses positive finite emptiness before
each branch's complete row obligation. Original variants and candidate artifacts
remain unchanged. Every inhabited branch must still pass the full check; empty
containers and optional sentinels are inhabited and cannot discharge it. Direct
Sum/Map-key identity and codec boundaries stay intact. RowTypes proves exhaustive
branch obligations, inhabited-branch checking and universal readable replacement
with explicit child/empty interpretation and distinct tag/value labels. See
row-types.md and the corresponding Gerbil tagged-worker integration controls.

### Singleton-empty List coverage through the existing Null judgment

A witnessed impossible element makes `(List Element)` inhabited by exactly `()`,
not an empty Type. Previously List-to-Null succeeded and Null-to-intrinsic-Union
succeeded, but their composition was refused. The shared replacement rule now
requires the existing positive `empty-type?` child witness and delegates to the
same `Null` comparison under the original quota. It retains the List AST in the
inferred assignment, descriptor, signature and declaration artifact.

Only entirely intrinsic identity-validating targets use this view. For example,
`(List (Pair Never (Function (UInt) (Integer))))` covers
`(Union Bool (Union Keyword Null))`, including inside Pair/Map values and Function
results. No payload or child callback can run on nil. An empty vector or Map is
another carrier; a List of empty Lists, optional sentinels or empty vectors has
possible nonempty lists. Neither can borrow this witness. Map keys and direct
ordered alternative descriptors remain invariant. A Union containing Function
or other wrapping branches stays outside this rule, even if it contains Null.

The existing `infer-descriptor-service` factory and `descriptor-service-action`
compose the whole workflow: prefix-bind the intrinsic Union input, infer the
original impossible-element List output from complete call observations, install
qualified methods, wrap the returned callback, refine publication policy and
bind exact context evidence. Policy refusal does not consume the observer;
a fresh action can retry. Two distinct singleton-List descriptions remain
genuinely ambiguous. Invalid callback arguments, nonempty batches, unsupported
late branches and quota exhaustion retain their original failure semantics.
`t/empty-inference-test.ss` exercises this complete chain without another driver.

Lean's `emptyListCheck_into_iff` proves that target membership of nil is both
necessary and sufficient, using the existing witness and actual List membership.
`emptyListCheck_normalized` preserves the exact value under the intrinsic target's
explicit identity-on-nil law. `inferEmptyList_into` preserves the original complete
unique declaration artifact and transfers every actual source value. Top-level
`Examples/PrototypeTypes.lean` includes ordered flat-view, normalization and
ambiguity controls. Host carrier interpretation and child emptiness soundness
remain explicit; arbitrary recognizers, effects, mutable writes, codecs and
compiler correctness are not proved. This advances the article's finite type
protocol future work, not an existing Racket inference solver.
