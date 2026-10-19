# Bounded prototype polymorphism, subtyping and inference

For the Object/row and guarded Mu extensions, see [row-types.md](row-types.md).

This implements a decidable part of the original type-system **future work**.
The Racket discussion in “Prototypes are Useful Even Without Subtyping”, “Type
Descriptors” and Appendix C/D motivates explicit universal Self/Super parameters,
subtype constraints and `(Proto A B) = (Fun A B -> A)` with `A <: B`.
It does not provide the following solver as an existing paper implementation.

## One composable protocol

`type-relation.ss` admits this finite expression grammar:

```scheme
Any | Bool | Integer | UInt | declared-variable
(List T)
(Tuple T ...)
(Function (output ...) (input ...))
```

The Function ordering is exactly the existing descriptor constructor's outputs,
then inputs; the corresponding paper notation is `(Fun input ... -> output ...)`.
There is no second executable Function representation. `expression-type` compiles
only ground expressions through the existing Type/List/Tuple/Function constructors.
`UInt` now checks nonnegative exact integers rather than inheriting Integer's
recognizer unchanged; zero and negative output controls exercise this distinction.

`subtype-expression? source target [budget]` decides **derivability in this
algebra**. Rules are reflexivity, Any as top, UInt <: Integer, covariant List/Tuple
observations, and Function argument contravariance/result covariance. Tuple width
and Function input/output counts match exactly. It does not treat mutable slot
writes as covariant or infer semantic relations from prototype ancestry.
A negative judgment means no derivation here, not a counterexample to an arbitrary
semantic implication. Unsupported descriptors are refused even against Any.

Proper-list inclusion also admits Null into List and Pair into List when the
head replaces the element Type and the complete tail replaces that same List.
The recursive tail may be another Pair, List or Null. This uses the original
replacement judgment and shared quota, not a second flattening or validation
engine. Tuple is a vector in Gerbil: even the empty Tuple is disjoint from Null.
No conversion, Map key widening or ordered Union rewriting is implied.
`PrototypeTypeDescriptors` proves universal list-spine inclusion from child
inclusion and preserves the original selected shape through complete declaration
inference. The carrier model distinguishes empty vectors from empty lists;
host constructor correspondence and recursive wrapper behavior remain runtime
obligations. The handler-batch example and regressions exercise that boundary.

The converse singleton case uses the existing positive empty-Type witness:
`(List Dead)` replaces Null only if Dead is proved empty. The List remains
inhabited by nil; an empty Tuple/Map/List or an optional sentinel is an inhabitant,
not proof of an empty element Type. Pair recursion carries this fact into exact
singleton tails. No public descriptor, Map key or ordered Union tree is rewritten.
`emptyListCheck_sound` and `emptyListCheck_inhabited` prove both sides of this
distinction; `singleton_tail` retains the exact head and `inferEmptyList_sound`
retains the original completed declaration artifact. Empty-witness interpretation
and host carrier projection remain premises. The singleton-handler example
composes this with inferred qualified methods, nested Function wrappers and
FUN/refine/bind-evidence; equivalent candidates remain ambiguous.

Maybe/OrFalse targets now share general payload lifting and exact sentinel
coverage. Same-kind covariance retains its fast child proof; broader optional
sources must cover both their original sentinel and their payload. Bool and
immutable Exactly/Enum sources check every literal, using false only as OrFalse's
sentinel and Unit only as Maybe's sentinel. Different nesting orders may include
the same values while retaining distinct candidate metadata and genuine ambiguity.
Map keys, direct ordered Union identity and keyword/escape origin checks are not
relaxed. Optional Functions do not become unconditionally callable.

OptionalValidation's payload_replacement, sentinel_replacement,
finiteCoverage_sound and inferOptional_sound prove the corresponding readable
inclusion and exact original declaration provenance under complete host
interpretation/child-inclusion premises. Runtime sentinel bypass, present child
errors and recursive wrapping keep the existing normalize/validate-optional
semantics. Arbitrary callback effect equivalence and host compiler correctness
are outside this relation; Scheme tests exercise the separate runtime obligations.

`prototype-types.ss` connects that algebra to `parameters.ss`:

```scheme
(prototype-type prototype '(Self Super)
  '(Function (Self) (Self Super)) '((Self Super)))
```

Variables are unique and exactly match the prototype's `.parameters`. Constraints
are two-expression lists, representing the paper's `<:` relation. Explicit
`instantiate-prototype` checks complete ordered ground substitutions and every
bound before compiling the descriptor and calling ordinary persistent `specialize`.
The instance retains `prototype`, `descriptor`, `expression` and `substitution`.
Inherited/computed fields continue to use the final specialized receiver.

`infer-prototype scheme candidates queries [budget]` enumerates the Cartesian
product of a **finite, explicit ground universe**, deduplicating equal candidates.
Queries are `(actual expected)` inequalities; actual is ground and expected may
contain declared variables. These join the scheme's bounds. Only complete unique
inference constructs an instance. Several valid assignments remain ambiguous;
there is no first-match guess, sample-based inference, principal-type assertion,
implicit widening, or inference of arbitrary predicate implication.

`examples/polymorphic-services.ss` supplies both the appendix's higher-order
function prototype and a service whose output is narrower than its input. Existing
`checked-action` Reader/FUN sequencing recursively wraps Function fields before
`refine` whole-object checks. Exact `bind-evidence` subject/descriptor/context
identity then guards the existing publisher. Stale context refuses publication and
preserves the old state. There is no new monad, evidence authority or global cache.

## Bounds and failure semantics

The default shared work budget is 8192; admitted range is 1..1048576. One counter
covers input-pair preflight, expression/constraint checks, structural comparisons,
substitution, candidate search nodes, and descriptor compilation across the whole
request. Checking and compilation do not reset the inference counter. Syntax
preflight has maximum pair-tree depth 64, including list spines; cyclic syntax
refuses before list traversal, substitution or descriptor callbacks.

| Outcome | Meaning / exposed result |
| --- | --- |
| subtype true / false | Derived / not derived within the admitted algebra |
| unique | Exactly one complete candidate assignment; carries one instance |
| no-solution | Completed finite search with no assignment; no instance |
| ambiguous | Completed finite search with multiple assignments; no instance |
| TypeRefusal `exhausted` | Work or syntax-depth limit; no partial candidate/instance |
| TypeRefusal `unsupported` | Unknown atom, constructor or unsupported signature form |
| TypeRefusal `malformed` | Invalid declaration, variable set, arity or configuration |
| TypeRefusal `bounds` | Explicit substitution violates a declared inequality |
| Existing validation/body error | Original exception propagates; no retry/fallback |

`type-refusal?` / `type-refusal-kind` inspect controlled refusal without parsing
messages. Every schema is revalidated and its expression/bounds copied on entry;
mutable public metadata is not a durable proof token. Original source lists cannot
silently rewrite the captured syntax. Stable schema/prototype metadata and standard
Type definitions during each sequential request remain premises. There is no atomic
concurrent mutation claim. Previously returned instances never grant fresh evidence
for a different descriptor/context identity.

Rank-two/higher polymorphism, unrestricted recursive type equations/carriers,
unbounded row inference, dependent/effect inference, user-defined predicate
implication and optional/keyword/rest/CaseFunction **subtyping** remain outside this
algebra. Those existing executable Function forms still work through their own
validators; this judgment refuses unsupported syntax. Runtime values are always
validated/wrapped through their instantiated descriptor: a subtype result never
bypasses validation or proves host arity, termination, effects or cached evidence.
Finite bookkeeping bounds do not bound arbitrary computed-slot/consumer callbacks;
process timeouts and heap limits remain mandatory and unchanged.

## Three-way evidence and acceptance

The Gerbil focused suite covers primitive inclusion and negative UInt values,
nested Function variance, exact output counts, explicit bound refusal, higher-order
Proto specialization, complete unique/ambiguous/empty search, recursive Function
wrapping in containers, refine/FUN consumption, and exact evidence publication.
Resource and unsupported controls are distinct from negative derivability.

The companion Lean module `Functional.PrototypeTypes` independently defines the
finite algebra, declarative Subtype, sound bounded checker, substitution, complete
finite inference and refusal. Proofs establish checked derivations, **conditional**
semantic replacement, every inferred constraint, unique candidate validity,
no-solution exclusion within the supplied universe, and incomplete-search refusal.
Its interpretation explicitly requires behavioral Function variance; Scheme's
`procedure?` recognizer alone cannot discharge that premise. A separate mathematical
arrow theorem states input/output replacement directly. `Examples/PrototypeTypes`
uses the same nested service signatures and finite Self/Super candidate constraints.

This is a correspondence of named rules and controlled outcomes, not a verified
Gerbil compiler, exact runtime cost model, or proof of all Type-system future work.
Lean's fuel bounds derivation depth / abstract assignment scans; Gerbil additionally
charges syntax, search and compilation visits. No Scheme test or library imports a
Lean checkout. Full existing single-process tests and Lean resource-guarded checks
remain required; focused controls do not replace either gate.

See [intrinsic scalar Union coverage](scalar-coverage.md) for String/Symbol/Keyword,
its exact decidable scope, shared publication chain and proof interpretation bounds.

See [finite inference audit and emptiness](finite-inference-audit.md) for remaining P2 coverage and the required-field witness protocol.

See [literal intrinsic descriptors](intrinsic-descriptors.md) for singleton, width, byte, alias and admission coverage.

## Finite dependent TypeValuePair catalogs

The Scheme grammar now admits explicit catalogs such as `(TypeValuePair UInt Bool)`.
These are sets of actual shared descriptor identities, retaining declaration order.
Catalog coverage requires every source identity in the target; payload subtyping
does not change a carried UInt descriptor into Integer. Map key identity and ordered
Union normalization retain their existing stricter rules. Intrinsic names are literal
and distinct; Any/Never, computed descriptors, free catalog entries and arbitrary
predicate discovery are unsupported. The whole catalog can be a type parameter.

The shared Scheme `type-value-catalog` helper reuses existing dependent validation,
recursive Function wrapping and actual slot-read replay. Its explicit runtime list
may contain custom/Function Types, without extending the finite inference grammar.
Old observations refuse after supported source/ancestor edits; reconstruction retries.
The common qualified declaration/FUN/refine/bind-evidence chain tests exact carried
identity, false payloads, keyword/escape carriers, policy failure and retry.

`Functional/OptionalValidation.lean` proves catalog coverage and replacement for
arbitrary payload predicates, missing-tag refusal before child work, exact descriptor
retention and selected normalized membership. Its stale law proves guard short
circuit, assuming host replay actually detects source drift. The existing finite
solver examples distinguish unique/no-solution/reordered ambiguous catalogs. These
do not extend `Ty` to unrestricted dependent types or prove the Scheme compiler,
host registry identity, arbitrary callback effects or concurrent mutation. This
advances the article's type-protocol future work. Dynamic Class/Schema capture
has the finite scope below; arbitrary discovery remains open. See Scheme
`doc/intrinsic-descriptors.md` for the executable boundary.

## Accepted-assignment construction

`CheckedAssignment` and `checkedUnique` retain the constraints proved by a
completed bounded search. `instantiatePrepared_eq` removes only repeated pure
checks of that captured assignment, while keeping the same live refresh and
assembler, exact errors and constructed artifact. `instantiatePrepared_refuses`
still blocks stale metadata before assembly. Public mutable schemas are not
proof certificates; the Gerbil path is restricted to its private complete solution
and copies raw syntax independently from public normalized alternatives.

`Formula.conjoinAtom_holds` in EvidenceBinding proves the fused fresh-atom
conjunction, including separate short-circuit and error laws. The integrated
examples remain in top-level `Examples/PrototypeTypes.lean`. The comparison-work
bound counts pure constraint replay, not total runtime, allocation or GC.
Gerbil's paired factory/publication benchmark measures those remaining costs
separately with unchanged validation, refusal and resource guards.

## Guarded declaration catalogs

`admitReflected_eq` in `Functional/MethodDeclarations.lean` models retaining one effective Slot catalog
from typed forcing through final root-signature admission. The final admitter still
receives the successor state, checks source equality and current descriptors, and
keeps every forcing/admission error. Catalog order and membership must remain
stable during forcing. Gerbil supplies that premise for supported registered
edits through its existing construction guard and dependency invalidation closure;
arbitrary unregistered host mutation and concurrent edits are outside that scope.
Nested Object catalogs still use the original traversal. `reflected_catalog_work`
removes one abstract projection charge, not a proven number of bytes or GC time.
`admitDeclaredSource_project` additionally permits reuse of pure normalized
metadata after exact source equality. Gerbil normalizes a private copied AST so
replaced public literal subtrees cannot mutate that captured result. Post-builder
syntax, binding and source checks remain; exact quota thresholds are not equated.

## Stable finite Class/Schema directories

Scheme `capture-type-catalog` resolves an explicit finite name list through the
existing POO getter and Type protocols. Opaque, snapshot-local tokens carry real
Class or external Schema descriptors. Aliases within one capture share identity;
a fresh capture creates a separate scope. Tokens flow through the existing Type
syntax, inference, prefix specialization and typed declaration compiler. Their
judgment is nominal identity, without structural implication from a Class parent,
a Schema predicate or printed metadata. A whole token can stand for a Type;
TypeValuePair catalogs retain the original descriptor tags and recursive wrappers.

Capture observes standard Class declared/effective Slots and declared child Types,
plus explicitly supplied source objects, with at most 64 names, roots and visited
Types. Metadata work is budgeted; arbitrary callback termination is a premise.
Computed selectors use the existing registered-dependency discipline for cache
invalidation. External Schema/custom-Type hidden dependencies must be declared;
there is no automatic semantic dependency discovery or new Schema compiler.

`reobserve-slot-reads!` shares the original Slot replay traversal, delivers its
complete checked dependency closure to outer collectors, and rechecks after
observers. Cold getters and metadata construction do not rerun. Old source/Slot/
approval observations refuse before a validator runs; successful work is checked
again before publishing. Original callback exceptions keep their cause and effects.
Fresh capture/re-specialization retries under new identity; a fresh but rejecting
Schema still rejects. Missing fields, invalid Types, malformed/unsupported capture,
work exhaustion, stale sources and ordinary inference outcomes remain distinct.

`OptionalValidation.CatalogType` and `catalogIdentity` model scope separation.
`captureCatalog_sound` connects accepted materialization to complete ordered
resolution and source admission. `catalogCall_sound`, `_stale`, `_changed`,
`_error` and `_stable` state exact before/after-stamp publication, short circuit
and normalization preservation. `Examples/OptionalContracts.lean` checks aliases,
fresh scope refusal, late capture failure, shared approval/Slot stamp changes and
unchanged dependent Function wrapping. Host identity and complete, correctly
recorded registered sources are explicit premises; these laws do not prove the
Scheme parser, arbitrary callback implication, metaclass discovery or concurrency.
This extends the article's type-protocol future work. See the companion Scheme
`doc/intrinsic-descriptors.md` for exact APIs and remaining unrestricted scope.
