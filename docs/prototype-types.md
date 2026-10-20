# Bounded prototype polymorphism, subtyping and inference

For the Object/row and guarded Mu extensions, see [row-types.md](row-types.md).

This implements a decidable part of the original type-system **future work**.
The Racket discussion in “Prototypes are Useful Even Without Subtyping”, “Type
Descriptors” and Appendix C/D motivates explicit universal Self/Super parameters,
subtype constraints and `(Proto A B) = (Fun A B -> A)` with `A <: B`.
It does not provide the following solver as an existing paper implementation.

Map-key invariance below applies to potentially inhabited entries; the final
necessarily-empty Map section gives the explicit positive-witness exception.

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


Optional sources now also replace ordinary intrinsic flat targets through the
same two-branch obligation. `(OrFalse (Exactly #t))` covers Bool;
`(Maybe Never)` covers Unit, while `(OrFalse (Enum))` covers exactly false.
Empty children never erase their source sentinel. Entirely intrinsic flat Union
targets can jointly cover both branches, including nested void/false optionals,
numeric intervals and Keyword leaves. Each check retains the original candidate
AST and shared work quota. Wrapper-bearing Union targets, invariant Map keys,
direct ordered Union relations and keyword/escape origins are not widened.
Optional Functions remain non-callable without checking their present branch.

`infer-decision-service` exercises this inside Pair fields with a recursively
wrapped Function, a concrete Bool decision and Unit acknowledgement. It reuses
the complete prefix-specialization/declaration/FUN/refine/bind-evidence chain;
invalid sentinels, returned callback inputs, policy retry and genuine equivalent
candidate ambiguity are checked. No Any is synthesized. Missing coverage is false;
unsupported metadata and exhaustion keep their typed refusal semantics.

Lean's replacement_into_iff proves both source obligations are necessary and
sufficient. normalized_replacement establishes membership of the exact returned
value under the existing normalizer, preserving its checked Function wrapper;
inferOptional_replacement retains the original completed declaration artifact.
Host descriptor interpretation and the flat target's identity validation remain
premises. These are readable inclusion laws, not arbitrary effect equivalence or
compiler verification. This finite type protocol advances the article's future
work; it is not attributed to the reference Racket implementation.


### Source alternatives into ordinary intrinsic targets

A completely intrinsic flat Union source can now replace an ordinary intrinsic
flat target only when EVERY original branch replaces that same target. The shared
flat-subtype? rule already owns ordered andmap traversal, literal/interval/byte
judgments and quota charging; the public replacement dispatcher now admits this
direction. For example, negative-range/zero/UInt alternatives replace Integer,
and Exactly/Enum Boolean alternatives replace Bool. Nested and overlapping source
branches retain their original order and syntax. An empty Union has no values;
vacuous coverage does not make runtime validation accept a fabricated value.

This is a read/validation inclusion, not a serialization conversion. Direct
Union-to-Union replacement remains invariant, including semantically equivalent
reorderings. Map keys keep exact syntax. Any wrapper-bearing or non-flat source
branch refuses this path even if another branch would match a particular sample.
Missing coverage is false; malformed/unsupported syntax and shared work exhaustion
retain distinct typed refusal semantics. Keyword/escape origin restrictions and
first-match validation errors are not relaxed, and no Any is introduced.

infer-measurement-service puts the rule inside UInt-indexed Map values and Pair
fields next to a recursively wrapped Function. It reuses complete inference,
prefix specialization, qualified declarations and descriptor-service-action's
FUN/refine/bind-evidence chain. Regressions check source/Map identity, false data,
returned callbacks, policy failure/retry, bad branches and genuine ambiguity of
original candidate descriptors. Ordinary subtype observations do not rewrite the
selected output declaration to its target.

VariantValidation.sourceCoverage_exact/sourceCoverage_sound prove exhaustive
branch obligations and universal membership. sourceCoverage_normalized reuses
committed Union validation to retain the exact value under explicit source and
target identity premises; selected-error controls retain the original cause.
DeclarativeMetadata.inferSourceUnion_sound connects complete unique search to
both original ordered artifact provenance and universal inclusion. Top-level
Examples/PrototypeTypes.lean exercises overlapping branches and failure controls.
These generic interpretation laws complement the restricted Ty checker; they do
not claim its completeness, Scheme parser correctness, arbitrary callback effect
equivalence or host compiler verification. This advances the article's type
protocol future work; Racket does not supply this finite inference algorithm.

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

### Empty dependent directories

The exact zero-entry `(TypeValuePair)` directory supplies positive finite
emptiness evidence to the common replacement relation. Mandatory products and
rows inherit that evidence; a List with this element type contains only nil,
and an optional field with this payload must be absent. Descriptor metadata is
retained in the inferred original candidate. No payload recognizer is consulted
to establish emptiness. Nonempty directories, including captured Types whose
recognizers always return false, remain opaque. Empty List/Map, Maybe's void and
OrFalse's false remain inhabited; invariant Map keys and ordered Union trees
retain their existing rules.

`infer-plugin-service` in the companion Gerbil `examples/polymorphic-services.ss` composes the complete
finite solver with existing specialization, typed declarations and the shared
FUN/refine/bind-evidence publication action. Its regression fixture keeps a live
Function-valued dependent plugin, removes only a provably absent optional layout
obligation, retains carried Type identity and recursive wrappers, and exercises
failure/retry, ambiguity and source-edit refusal. The validators themselves are
unchanged: malformed pairs, invalid Types and missing catalog membership retain
original diagnostic priority before payload validation.

The companion Lean laws `OptionalValidation.catalogEmpty_sound` and
`catalogTyped_empty` establish uninhabited membership and missing-Type refusal.
`Examples/OptionalContracts.lean` composes these with `catalog_replacement`,
`inferRowView_sound` and `absentField_observe` to derive unique original-layout
selection, semantic replacement and actual absence. Live callback behavior and
host descriptor interpretation remain explicit premises of their existing laws.
This is finite type-protocol future work beyond the article's Racket construction,
not a completeness theorem for arbitrary predicates or a proof of the host runtime.

## Necessarily empty Map carriers

The common replacement rule keeps keys invariant and values covariant whenever
source entries may exist. It now also accepts another Map layout when the existing
positive finite empty-Type witness proves the source key **or** source value
uninhabited. In that case every admitted table has zero entries. Its empty hash
carrier is inhabited: it does not become String, Never or an empty element for
List. A nested necessarily empty Map therefore cannot justify emptiness of an
outer Map. Direct ordered Union replacement and keyword/escape rules are unchanged.

This is observational readable replacement, not permission to insert target keys
or mutate a table. Candidate syntax, original key/value descriptors and comparator
policy are retained. No opaque recognizer is queried to infer emptiness; hidden
unsupported syntax still refuses admission, and work exhaustion is distinct from
negative coverage. Unknown callback semantics and nonempty finite catalogs supply
no witness. No Any is synthesized.

`infer-retired-route-service` reuses the complete descriptor-service solver,
prefix specialization, qualified declarations and descriptor-service-action's
FUN/refine/bind-evidence chain. A live handler remains recursively wrapped beside
a retired table with its original impossible-key metadata. Integrated controls
cover unique selection, distinct original candidates remaining ambiguous,
nonempty insertion refusal before consumer admission, clearing/retry, exact
subject/context evidence, and intact raw callbacks. Existing Map validation uses
Gerbil hash snapshots/new-table policy through validate-bindings; an empty source
is retained by identity and invokes no child validator. No extra table traversal,
cache or descriptor registry is added.

Lean's existing checker, Subtype derivations and replacement theorem include the
same empty-key/value rule. `map_key_or_empty` exposes the exact alternatives;
`map_key_invariant` now requires nonempty component semantics. The interpretation's
emptyMap law is explicit. `VariantValidation.map_empty_snapshot` derives zero
entries from complete per-entry membership and either uninhabited component;
`map_empty_replacement` derives success for arbitrary target key/value validators
without executing them or a collision comparison. Top-level PrototypeTypes and
VariantContracts examples exercise complete inference, prefix substitution,
universal replacement and Function-bearing snapshots. Faithful host snapshots,
carrier/comparator preservation, callback behavior and supported source stability
remain explicit boundaries; this advances finite type-protocol future work,
not unrestricted predicate inference or a proof of the host runtime.

## Source Union coverage for readable containers

A source Union may replace one ordinary List, Tuple, Pair, Map, Record or Object
view when **every original branch** passes the existing complete carrier/child
relation for that same target. This extends the earlier flat scalar rule; it does
not reorder, flatten, delete or rewrite alternatives. Direct Union-to-Union
comparison stays invariant. Root Function/opaque-target inclusion is not expanded
by this rule. Incompatible vector/list carriers, improper Pair tails, missing
fields and live Map-key changes still refuse through their existing judgments.
Nested Function fields use their existing variance and wrapping obligations.

An empty source Union is uninhabited and vacuously covers an admitted ordinary
container; its runtime validator still refuses every value. Complete syntax
admission precedes comparison, so an unsupported late branch cannot be hidden by
an earlier successful branch. Each branch comparison shares the existing work
quota. Exhaustion remains distinct from a completed false result, no solution
or genuine ambiguity. No Any is synthesized.

The existing infer-worker-service factory now accepts original ordered
Record/Object alternative candidates. The worked regression retains UInt8 and
UInt callback layouts, inherited Record/contract field validation, nested
Map/List callbacks, complete prefix inference and qualified declarations. Its
FUN/refine/bind-evidence chain retains exact subject/context evidence, original
candidate syntax, approval refusal/retry and raw callbacks. A first-selected
UInt8 callback still refuses an out-of-range result even when a later UInt layout
would accept it; validation never retries that later branch. Reversed original
candidate trees remain genuinely ambiguous. Public ObjectContract sexp is a
nominal display, so provenance uses captured finite syntax rather than display
identity. Existing validators, Gerbil collection mechanisms and publication
abstractions are reused without another dispatch or cache layer.

Lean's existing Subtype/check/check_sound/replacement chain now covers ordinary
List/Tuple/Pair/Map targets using all original branch derivations and the existing
Union shape interpretation law. Row-bearing host views additionally use their
existing field laws. VariantValidation.union_normalized_member proves membership
of the **actual normalized result** in an original selected branch;
sourceCoverage_wrapped transfers that result through complete branch coverage.
Unlike the earlier flat identity law, it does not assume normalization leaves
raw values unchanged. Existing union_error still preserves selected failure.
Top-level PrototypeTypes/VariantContracts examples compose complete declaration
inference, original artifact provenance, prefix substitution, universal inclusion
and normalized Function-bearing payloads.

This advances the article's finite type-protocol future work. Branch membership,
faithful host carrier/row interpretation and behavioral Function inclusion remain
explicit premises; procedure recognition alone does not certify behavior. No
mutable-write permission, arbitrary predicate inference, unrestricted recursion,
effect rollback or host runtime/compiler verification is claimed.

## Complete source-branch checks for finite data views

Source Union decomposition now uses one common branch judgment for admitted
ordinary finite data targets: built-in flat scalars, List/Tuple/Pair/Map,
Record/Object, Maybe/OrFalse, TypeValuePair catalogs and Sum. This closes the
previous whitelist omission for optional/dependent/tagged views. Every original
branch must replace the SAME complete target through its existing rules; known
sentinel and empty-carrier evidence can therefore compose across nested layouts.
No new implication between arbitrary predicates or opaque descriptors is inferred.

Direct Union-to-Union identity, opaque token targets and direct Sum tag-skeleton
rules retain their existing bounds. Callable targets are covered below. Neither
alternative order nor original directory identities are rewritten. Unsupported
late metadata refuses complete admission, budget exhaustion is distinct from a
negative judgment, and original candidate trees remain distinct for ambiguity.
Keyword and escape origins still use the existing dedicated transport relation;
that private flat-origin relation is not replaced by data-view coverage. No Any
is synthesized. An inhabited optional/container sentinel is never bottom.

`infer-availability-service` builds on the existing descriptor-service schema,
complete prefix inference and qualified declaration builder. Its packet pairs a
live handler with a tagged ready/idle state. Ready payloads preserve void, false
or an exact captured Type; idle payloads preserve false or checked handler lists.
Original candidate Union layouts combine all these views before existing
FUN/refine/bind-evidence publication. Regression cases exercise both actual
Function Type identities and bounds, every sentinel, nested callback wrapping,
returned callbacks, exact evidence/context, strict tag order, genuine ambiguity,
approval failure/retry and rejection after a captured source-directory change.
Gerbil validation and hash/collection mechanisms are reused unchanged.

Lean's common source-Union checker case now covers every corresponding finite
Ty data target while preserving direct Union bounds; callable targets are covered
below. Existing
Subtype derivations and replacement remain the proof path; the additional host
sentinel, row and dependent carriers use their established interpretation laws.
`VariantValidation.union_success` exposes the actual selected branch, successful
child normalization and normalized membership. `union_normalized_member` reuses
that success law, so `sourceCoverage_wrapped` still applies without raw-value
identity. OptionalContracts examples combine it with the existing void/false
protocol and catalogTyped_sound/catalog_replacement to prove wrapped payload
membership AND exact carried-token preservation. PrototypeTypes examples cover
complete Sum/optional declaration inference, original artifacts, prefix binding
and universal behavioral inclusion. Later invalid Function results remain errors.

This advances the article's finite type-protocol future work. Faithful host
carrier/sentinel interpretation, behavioral Function contracts, source-read
stability and callback effect/termination obligations remain explicit. No
mutable-write permission, unrestricted recursive inference, effect rollback,
parser equivalence or host runtime/compiler verification is claimed. The full
TODO/P2 ledger is not declared complete.

## Callable source alternatives inside container interfaces

The P2 audit found that the common source-Union rule excluded Function and
CaseFunction targets even when every original branch passed their existing
replacement judgment. This blocked callback directories such as
`(Map (List (Union callback-a callback-b)) <- UInt)` from satisfying a shared
callable interface. The rule now uses the SAME all-branch traversal and shared
quota for these explicit targets. It delegates each child to the existing
ordered call-language checker: inputs are contravariant, outputs covariant,
multiple-value counts exact; optional/keyword/rest transport and first matching
case selection retain their original checks. No new callable representation,
user recognizer implication, branch reordering or Any fallback is introduced.

This is a decidable part of the article's Type Descriptors/Appendix C future
work; the Racket reference does not already implement this finite solver.
Gerbil's case-lambda performs actual procedure dispatch, existing recursive Type
validators install wrappers, and the shared whole-declaration builder composes
FUN/refine/bind-evidence. The implementation adds no second dispatch engine.

`infer-callback-directory-service` publishes a Map/List callback directory and a
Tuple fallback through a Pair packet. Complete inference rejects a candidate
whose optional first case shadows a later two-result case. The selected original
Union stays in the report; an equivalent reversed candidate is ambiguous rather
than silently canonicalized. Tests cover checked calls and multiple results,
invalid argument suppression, first narrow result failure without later fallback,
exact consumer evidence, unchanged raw references, policy failure and retry.
A separate matrix covers Record fields, rich keyword/rest signatures, unsupported
late metadata, exhaustion and empty alternatives.

Direct Union-to-Union and inhabited Map-key layouts remain invariant. A Union
containing a present-or-absent Function cannot become unconditionally callable.
An empty Union has vacuous inclusion but cannot validate a procedure or publish a
runtime inhabitant. Opaque target discovery and unrestricted recursive/effect
inclusion remain unsupported. Static false means no derivation in this algebra;
malformed/unsupported metadata and budget exhaustion retain typed refusals.

Lean's `check_union_function` proves the exact bounded all-branch equation,
including vacuity without fabricating a procedure witness. Existing check_sound,
sourceUnion/replacement and declaration inference laws compose through Map/List
covariance and prefix substitution; Examples/PrototypeTypes.lean supplies positive,
negative and exact-artifact controls. The behavioral inclusion theorem explicitly
requires faithful Union and Function interpretations. Procedure recognition alone
proves neither totality nor output behavior. Gerbil regression tests separately
exercise CaseFunction's richer call language; the Ty checker models fixed arrow
rows, not the whole Scheme decoder, effects, GC or compiler.

### Or and ordered normalization

Gerbil's existing Or now participates in finite syntax, substitution and complete
source-branch inference, compiling through the original constructor. Its first
actual member and Union's first structural match remain distinct. Both reuse one
selected-child validator and retain recursive wrappers, original failures and
selected returned membership. Direct ordered alternative targets, Map keys,
keyword-mode boundaries and codec/index semantics retain their existing rules.

VariantValidation.orValidate specializes the existing ordered engine with actual
membership. orValidate_success, orValidate_error and sourceCoverage_or_wrapped
prove exact selection/results, original failure and universal readable inclusion
of the returned wrapper. Examples/VariantContracts.lean composes those laws with
complete unique inference and original declaration artifacts. Soundness requires
faithful host membership and child inclusion; arbitrary recognizer effects and
compiler/codec correctness are separate obligations. This is type-protocol future
work. The Gerbil callback-directory regression runs the same higher-order
Map/List/Tuple, specialization/declaration/FUN/refine/evidence workflow for both
constructors. Standard bounded generation, shrinking and replay reuse the existing
alternative graph, including transparent-cycle refusal and resource limits.

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

Raw keyword coverage now shares the existing finite emptiness witness for
impossible container origins. The original descriptor remains intact; actual
empty collections/sentinels stay live and complete closure still gates every
call region. See [finite-inference-audit.md](finite-inference-audit.md#impossible-container-origins-in-raw-keyword-coverage)
for the retired-keyword publication example, failure semantics and proof scope.
