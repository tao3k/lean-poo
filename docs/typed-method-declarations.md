# Certified typed method declarations

The Scheme declaration protocol now connects existing method fragments,
`.defgeneric` and typed multi-dispatch through `MethodDeclaration.`'s existing
`method` form. Its signature is an existing negative-watch certificate, shared
by identity; its contributions are existing named declarative edits.

Ancestor edits precede local edits. Each explicit edit batch retains its current
registration, prepend, guard and removal semantics. The final inherited group
is lazily installed and checked once through Gerbil promises. Invocation uses
the existing dispatcher and returns result plus complete immutable successor,
without hiding mutable cache ownership or caching guard decisions.

The article's Appendix B (Multiple Dispatch, Combining Method Fragments,
Generalized Prototype Combination) supplies the conceptual ordering, filtering
and composition. This unified declaration protocol advances its stated future
work; it is not presented as an existing Racket declaration API.

`LeanPoo/Functional/MethodDeclarations.lean` reuses `DeclarativeMetadata` and
`DispatchExtension` to prove completed-candidate acceptance, edit-batch parity,
cache soundness, transfer of every negative assumption to a successful invocation
successor and retention of the seed on refusal. The supplied admitted Args type,
common signature, stable Types/precedence/watches and callback discipline are
premises. These proofs do not verify Gerbil macro expansion, Type normalization,
compiler correctness, external effect rollback or a machine-time bound.

Top-level `Examples/TypedMethodDeclarations.lean` exercises two-axis dispatch,
inherited edits, value-sensitive guards on the same cached shape, completed-batch
cancellation and distinct registration/negative failures. Scheme's existing
`examples/declared-methods.ss` adds the shared-diamond FUN approval/IO workflow;
`t/typed-method-declaration-test.ss` tests every existing method policy, refusal,
retry, supported metadata invalidation and explicit old-snapshot behavior.

Explicit finite certified declarations are covered. Arbitrary inferred generic
syntax and unrestricted recursive compilation remain open in Scheme TODO.md.
