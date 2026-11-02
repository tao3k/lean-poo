# Intrinsic scalar coverage in ordered Union

This advances the article's Appendix C/D type-protocol future work. It does not
attribute this finite inference procedure to the Racket reference.

## Decidable fragment

The source is the intrinsic String, Symbol or Keyword family. The target is a
finite ordered tree containing only known flat intrinsic families, literal
Exactly/Enum and integer intervals. For the fragment without Any, coverage holds
exactly when some nested branch contains the same complete intrinsic family.
Earlier finite alternatives may select individual members; they cannot cover
an infinite family collectively. Cross-family conversion is never inferred.

| Target | Checked result |
| --- | --- |
| Same-family primitive, possibly nested among flat alternatives | Covered |
| Finite literal alternatives and other disjoint families only | Not covered |
| Function/container/refinement/custom validator inside the tree | Outside this rule; no shortcut through an earlier matching family |
| Malformed/unsupported metadata | Typed syntax refusal, even after a matching branch |
| Work quota exhausted | Typed exhaustion, never a successful or partial result |

String literal metadata remains unsupported because strings are mutable. Known
Symbol/Keyword literals retain exact identity. An explicit Any retains its
existing semantics, but no Any is manufactured and the exact-family theorem is
stated for the admitted positive fragment without Any. Complements, arbitrary
predicates, dependent type implication and general set-algebra inference remain
outside this criterion.

## Keyword transport and failures

Gerbil's string?, symbol? and keyword? predicates identify distinct families.
Neither #!key nor #!rest is a Keyword value. Keyword-to-Union value inclusion does
not change keyword-stable-type? or permit conversion between positional and
keyword-interpreting signatures. Public literal token origins keep their prior
guard, and Union-to-Union order/duplicates and Map key identity remain invariant.

A Keyword value passed to a rich keyword signature must use the existing
encode-arguments/decode-arguments protocol. The shared publication action now
encodes its semantic positional input according to the declared keyword mode;
it does not treat a keyword value as a named parameter. Unescaped values and
escaped marker payloads remain subject to shape/type failure. Callback signatures
without keyword parameters continue to accept Keyword data directly.

Selection still commits to the first matching branch. A selected validation
error never tries a later branch. Full-tree intrinsic admission is required
before coverage, and all normalization/comparison work uses the existing quota.
False/no-solution, ambiguity, typed exhaustion and user callback failures remain
distinct; no incomplete or nonunique assignment reaches a declaration builder.

## Shared workflow and verification

scalar-union-service-type and infer-scalar-service use the original rich
Self/Super signature and shared call/declaration factory. The existing
optional/keyword/rest host binder supplies a missing bonus from the checked input.
The same identity callback is recursively wrapped. Numeric, text, Boolean and
scalar policies share one signature-refinement-action and the existing FUN/IO
publication/evidence action. Scalar refinement can refuse before its consumer;
evidence remains bound to the exact current context, and a fresh request retries.

Tests cover all three families, ordinary/fresh uninterned symbols, fresh keywords,
mutable String values without String literal metadata, duplicate/order controls,
finite-only gaps, wrapper shortcuts, keyword and escape boundaries, selected
errors, complete declarations, nested callbacks, inference ambiguity/exhaustion
and refine/evidence success and refusal. No test requires a Lean checkout.

Lean keeps the existing namespace and separates PrototypeTypeSyntax,
PrototypeTypeCoverage and PrototypeTypes by function. Homogeneous Symbol/Keyword
Enum leaves use abstract natural-number literal IDs. scalarWhole_iff proves the
necessary and sufficient whole-family criterion. scalarFresh constructs a missing
member beyond every finite literal cutoff, rather than sampling a finite test
set. scalarCheck_sound/complete retain family classification and complete flat
admission. scalarUnion_validate reuses first-selected identity validation;
inferredScalar_sound preserves every constraint and the exact bound artifact.

Host name encoding and the connection from abstract IDs to intrinsic family
values are explicit interpretation premises. The proofs do not verify the host
keyword parser, arbitrary/mutable Type overrides, String/Symbol conversion,
serialization, GC or primitive bit costs. Ordered validation requires fixed
shape/membership and identity behavior. Full resource limits, complete local
checks and exact-head CI remain required independently of the model proofs.
