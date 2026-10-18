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

## Inferred and prefix-specialized declarations

The current bridge adds `specialize-prototype-type`, `instantiate-declared`,
`infer-declared`, `instance-signature` and checked `bound-parameters` observations
in the existing Scheme modules. A ground prefix creates a residual type schema;
only full instantiation or uniquely completed bounded inference can invoke the
higher-order declaration builder. Finalized forms use the existing expander,
Slot inheritance, typed registration and negative-watch checks. All typed groups
are prepared before return; ordinary computed fields remain lazy.

The inferred signature's Type positions now include required/optional/keyword/rest
inputs, ordered CaseFunction clauses and exact multiple outputs. The existing
sparse dispatcher retains its negative watches and cache owner; invoke-declared
returns all user values followed by that owner. See the rich signature protocol
below for supported variance, binding sites and failures.

No-solution and ambiguity retain reports with no instance and no builder call.
Exhaustion and malformed/unsupported syntax remain type refusals. Builder,
registration and negative-watch errors preserve their existing causes. Bound
parameter overrides, reopening and direct descriptor revision changes refuse
before a completed instance is returned. Existing source guards freeze context,
source and candidate during construction. External effects are not rolled back.

`PrototypeTypes` proves fixed-prefix/residual environment laws and original
constraint entailment; `Parameters` proves the bound identity/revision predicate;
`MethodDeclarations` proves unique builder provenance, nonunique/exhausted
suppression, failure-phase distinction, positional frames and final admission.
The top-level executable example composes actual binding, finite inference,
certified method installation and calls, plus a stale-descriptor control. The
semantic model assumes admitted carriers, faithful substitution/source identity,
stable transitive Type behavior and supplied builders. It does not verify the
Gerbil compiler, arbitrary callback termination or runtime performance.

Per-request type budgets bound the existing finite algebra/search. Separate
prefix, residual inference and signature requests each retain their own explicit
quota. These are not a global CPU bound for arbitrary callbacks; full test heap
and watchdog limits remain unchanged. The article's generalized-prototype and
Self/Super type constraints motivate this future-work extension.


## Rich signatures and result ownership

`Functional.FunctionSignature.TypedSignature` projects the same finite call shape
for required/optional/rest arguments and declared/required keywords. `mapTypes`
visits inputs, optional values, keyword Types, rest Type and all outputs. Its
shape/selection and composition laws connect complete finite substitution to the
host's first-match case semantics. `replaces_sound` derives pointwise structural
subtyping in both variance directions under equal shape metadata. The Scheme
checker is conservative about keyword and clause order; it cannot prove arbitrary
case coverage or principal host signature inference.

`finishValues` checks exact output cardinality before ordered validation and pairs
the fully checked row with its immutable successor. Its laws cover zero outputs,
wrong counts, preservation of wrapped results and exact owner. `invokeValues`
connects selection, argument normalization, body execution and output completion;
selected type/body/count errors retain their cause and cannot try a later clause.
`Examples/TypedMethodDeclarations.lean` combines the rich service schema, a returned
Function, optional/keyword/rest Types, prefix/residual inference and original
Self/Super bounds. It also exercises variance, exact counts and zero outputs.

Gerbil reuses `function-signature.ss`, core formal binding/keyword forwarding,
`call/values`, existing combination continuations and sparse dispatch. Its public
`invoke-declared` returns all user values followed by one cache owner. A rich
`multimethod.call` uses a result list plus owner internally for every declared
Function, including single and zero outputs. Low-level `make` retains its
separate scalar Result carrier in the same dispatcher. Standard/forwarding/inner chains
preserve all results; simple reductions retain their one policy result and
Simula retains Unit. No incompatible signature is filled with invented values.

The proofs assume faithful descriptor projection, admitted Type validators,
stable Type/callback semantics and host parameter decoding. They do not verify
Gerbil macros, the compiler, arbitrary callback termination or runtime costs.
This is generalized-prototype/type-system future work motivated by the article's
Appendix B combinations and Appendix C constraints. The Scheme documentation and
regression tests specify the implemented grammar and rejection boundaries.
