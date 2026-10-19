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
