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
subtyping in both variance directions under equal shape metadata. The extended `FunctionCoverage` model now proves complete finite partition
coverage and typed replacement across unequal ordered call languages under a
shared decoded wire interpretation; principal host inference remains outside scope.

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

## Joint calls, catalog coverage and source discipline

The companion implementation now collects supplied-call and expected-result
constraints from an existing Function/Object signature expression, reusing Gerbil
shape selection and normalization. All named observations and original bounds
share one finite assignment, followed by one whole builder. Explicit Object
Function leaves are required methods; a root Function needs a corresponding
factory-derived group. Ordinary data contracts remain a separate validation step.

`FunctionSignature.inputConstraints`, `outputConstraints`, `callConstraints` and
`jointConstraints` prove complete supplied row cardinality, exact output counts,
ordered clause commitment and all-or-error joint collection. Inputs produce
`ground actual <: formal`; outputs produce `formal <: ground expected`. The
model's field lookup represents checked explicit Object path projection; parser,
keyword wire decoding and source/descriptor projection remain host premises.

`DeclarativeMetadata.inferDeclaredCalls` reuses the existing bounded search and
proves every original/call constraint under the SAME environment, complete unique
builder provenance, contradictory sibling rejection and exhaustion refusal.
`catalogCurrent` reuses `Parameters.bindingsCurrent` over path/expression keys and
exact descriptor/revision stamps. `admitDeclaredInterface_sound` requires both the
captured source and every required catalog member before returning an artifact.

Factory groups retain a private source stamp, using ordinary extensible Type
metadata rather than a registry. Declaration construction detects missing siblings,
wrong fields, copied source data, direct descriptor revision and callback mutation
of the captured syntax/binding frame. `invokeDeclaredSource` models direct revision
observations before work and after successful result/cache completion: stale input
cannot execute; changed output exposes no owner; original errors keep their cause.
These observations are not atomic revocation of concurrent writes or verification
of arbitrary transitive Type callbacks. Stable builtins/callback discipline and
faithful host descriptor identity/revision observations remain premises.

The top-level example combines the rich shared catalog, generated constraints,
Self/Super prefix/residual inference, two actual certified generic installations
and invocations, complete interface admission, source changes and revision controls.
Symbolic source labels/descriptor IDs illustrate the generic source-equality laws;
they are not compiler correspondence evidence. No new axioms or `sorry` are used.

The concentrated TODO ledger retains OPEN candidate-dependent signature kinds,
fields supplied only by unresolved rows, wider ordered-case replacement and
implicit/principal/higher-rank/effect inference. This remains the article's stated
generalized-prototype/type-system future work, with no runtime speed claim.


## Finite container inference integration

Pair, Map, Sum and ordered Union now enter the same finite prototype expression,
substitution and complete candidate inference used by typed method declarations.
This advances the paper's type-system future work; it is not attributed to an
existing Racket solver. Map arrows canonicalize before candidate deduplication.
Pair components and Map values are observationally covariant; Map keys retain
normalized syntax. Sum retains its exact ordered tag skeleton and compares payloads;
Union retains exact ordered normalized branches, including duplicates. No mutable
write law or arbitrary branch-language inclusion is inferred.

`Functional.PrototypeTypes` proves checker soundness, exact key/tag/branch
preservation, conditional semantic replacement and every inferred constraint for
these constructors. `Examples/PrototypeTypes.lean` uses a shared routing signature
with nested callback variance and composes the existing `VariantValidation`
collision law. Scheme's `container-inference-test.ss` exercises actual prefix
specialization, call-derived constraints, declared generic invocation, recursive
wrapping, refine/FUN/evidence publication and failed-request retry. Surface kinds,
unique Sum tags, stable descriptor callbacks and faithful host projections remain
explicit premises; proofs do not establish GC timing, compiler correctness or
permission to mutate covariant containers.


## Explicit Record results and Class initialization

Finite `(Record ((name Type required/optional) ...) open/closed)` expressions now
flow through the same prefix specialization, call-derived inference and typed
declaration builder as other Function arguments/results. The Scheme compiler
reuses Class. and RecordSlot; actual multiple inheritance, computed overrides,
defaults and initialization hooks retain their existing checked execution.
Record data callbacks remain distinct from certified method groups: a root Record
is explicitly refused as a method catalog before its builder can run. Object
catalog paths remain the declaration protocol.

`Functional.ClassValidation.RecordType` now shares RowTypes' named-row representation
with the original `(key, Type, optional)` metadata. Its `recordCheck` delegates to
the shared closed-key/presence/read judgment; `recordCheck_sound` derives the named
relation, including width and reordering. `record_field_replacement` retains the
distinct positional law for applying the same ordered observed value list to two
field lists. Both use one `slotAdmits`/`slot_replacement` law. Class initialization
still proves validation before and after a hook separately; no mutable write,
nominal subtype or arbitrary callback behavior follows from a default value.

`Examples/ClassContracts.lean` and Scheme's `RecordServiceType` share the same four
fields, optional callback, fixed Self prefix, original bound, Integer argument and
expected Record constraint. Complete finite search selects Super = Integer before
installing a generic. The Scheme example combines prepared qualifiers,
`.defgeneric`, multiple inheritance, a computed override, checked hook, FUN,
refinement, evidence binding and IO, including failure/retry controls.
This advances the paper's type-system future work using its distinction between a
class prototype and an instantiated runtime Type descriptor. Implicit inference
from arbitrary Class/Slot callbacks and candidate-dependent layouts remains open.

The complete local gate also exposed redundant solving in the existing queue
selection stress test. `Prepared.chargeRun` computes a charge from a retained run;
`chargeRun_eq` proves exact equality to `Prepared.charge` when that result is the
actual selected run. The stress test retains every scenario/profile/oracle/ceiling
assertion while sharing that result. No timeout, heap limit, checked workload or
cost conclusion is weakened, and this is not a Scheme wall-time speed claim.

## Candidate-dependent signature and field selection

The Gerbil solver now substitutes each complete finite assignment before deciding
its signature kind and Object field/row layout. All sibling call inequalities and
original bounds are checked under that same assignment. Accepted alternatives keep
their own normalized layout and queries. Existing declaration factories still
require full named-method coverage and current source/descriptor revisions.

`PrototypeTypes.collectCandidates` models complete bounded projection, with
candidate-local `bounds` rejection and whole-request propagation of other failures.
Its soundness and completeness theorems associate every retained layout with its
actual assignment and validation; no admitted alternative can be silently omitted.
`DeclarativeMetadata.inferDeclaredCandidates` composes this with the existing
unique-only builder, proving candidate/projection/constraint/builder provenance
and suppression of artifacts on projection errors. `Examples/TypedMethodDeclarations.lean`
projects rich signatures from two candidate field layouts, collects the existing
joint Function constraints, and exercises two-generic construction, ambiguity,
unsupported syntax after an accepted prefix, exhaustion and no-solution.

The projection and Boolean validation must faithfully represent Gerbil normalization
and bounds checking. The existing subtype and Function selection laws discharge
the finite relations where modeled; these theorems do not verify Gerbil expansion,
Type callbacks, parser implementations, GC or compiler execution. This advances
the appendix's type-system/generalized-prototype future work. Arbitrary reflective
Class/Slot discovery, unrestricted recursive/semantic language inclusion and
principal/effect inference remain outside the decidable finite scope.

## Ordered case language coverage

`Functional/FunctionCoverage.lean` keeps the existing `Functional.FunctionSignature`
namespace and models the complete declared language, rather than sampled calls.
It proves value erasure, arity clamping and first-selection preservation; complete
keyword-mask membership and shape coverage; then typed first-selection, exact-count
output covariance and all supplied input/key contravariance. `inputAt_representative`
proves that checking the extra rest representative covers every further position.
`replacesLanguage_sound` derives its ceiling and duplicate-free target key universe
and quantifies over **all** target-accepted decoded calls.

Gerbil reuses the existing `function-signature.ss` selector, keyword decoder and
normalizer through a shared checked signature projection. Its key subsets stream
under the caller's quota; malformed/unsupported/exhausted requests cannot expose
partial coverage. Its Boolean replacement now admits the controlled cross-mode rules below.
The original coverage theorem concerns the shared decoded domain;
projection fidelity, common wire interpretation and subtype interpretation of
opaque/runtime Type descriptors are premises. It does not verify host procedure
arity, totality, defaults/recognizer effects, macro expansion, parsing or compilation.

The existing top-level example checks unequal fixed/rest and keyword regions,
overlap refusal, original prefix substitution, complete inference and the existing
full declaration builder; `inferredCoverage_sound` links successful publication
to the universal replacement theorem. Scheme's executable example additionally
threads the inferred callback through recursive wrapping, FUN/refinement and exact
evidence publication. Regression controls include a separate operational wrapper
oracle on all small arities/key orders and quota exhaustion after an admitted cell.
This continues the paper's hypothetical type-system future work.


## Different keyword interpretation modes

`Functional/KeywordArguments.lean` stays in `Functional.FunctionSignature` and
models Gerbil's existing decoder, not a new calling convention. Ordinary outer
values decode identically in both modes. Keyword decoding rejects duplicate or
dangling keys; key escape transports one positional value; rest escape ends token
interpretation. `decode_minimum` proves `positions + 2 * supplied-keys <= raw-length`
for every successful spelling, including escapes and every keyword order.

`Functional/KeywordCoverage.lean` retains `Functional.FunctionSignature` and uses
both raw decoder bounds: `n+2k <= raw-length <= 2n+2k+1`. A trailing rest escape is
part of the upper bound; the encoder's optional marker is not part of the lower.
`replacesKeywordTarget` now derives global source/target modes and checks each
raw-length region's **actual first** source case. Counts beyond the maximum fixed
prefix share its stationary rest representative, proven by `rawCounts_complete`.
Fixed/optional prefixes and several ordered cases may jointly cover a bounded
raw language without unbounded Any rest. Defaults are never supplied artificially.

`decode_direct` proves a no-key minimum row equals its original token sequence.
The earlier `rawAnyPositions` theorem remains an explicit sufficient special case;
it is not a fallback policy in the Scheme checker. The value-sensitive rule below
retains each data Type and each protocol marker instead.

`replacesPositionalTarget` reuses `replacesLanguage`, adding finite stable supplied
input checks. `inputAt_representative` lifts these to all rest positions.
`replacesPositionalTarget_sound` combines raw decoding agreement, actual first
selection, input contravariance and exact output covariance. Its explicit carrier
interpretation premise says recognized stable Types have ordinary outer tokens;
it does not claim to verify arbitrary runtime recognizers. The finite Lean Ty
vocabulary includes scalars, containers, functions and ordered Union; Scheme's
additional admitted Maybe/Object/Record syntax uses its actual carrier guards.
Top-level `Examples/TypedMethodDeclarations.lean` links both rules to original
prefix specialization, complete unique inference and the existing whole builder;
`inferredRawCallback_sound` and `inferredPrefixCallback_sound` make the
publication-to-universal-law link explicit. The latter substitutes the existing
Value prefix into a typed fixed case and an optional raw case before complete
inference enters the existing two-generic builder.

Gerbil extends its existing `covers-signatures?` traversal and Type relation,
reusing the decoder, normalizer, standard key deduplication and streaming masks.
It never changes a caller's argument row to establish subtyping. The raw-region
rule is sufficient, not maximal mixed-wire semantic inclusion. Bounded non-direct
rows use the value-sensitive origin traversal described below; unbounded tails retain position-specific origins through the certified product
graph below. Unsupported syntax
and quota exhaustion keep existing typed refusals; false rejects a candidate;
complete no-solution/ambiguity/exhaustion cannot execute the declaration builder.
The Scheme examples continue through FUN/refine/bind-evidence with actual keyword
defaults and exact raw token sequences. Independent direct-wrapper controls over
1365 token rows, original upper/lower boundaries, fixed/optional/ordered cases and
failure paths are in `t/keyword-coverage-test.ss` and `t/keyword-prefix-test.ss`.

As the original text explicitly leaves Scheme's type system hypothetical, this
is type-protocol future work. Host procedure arity/totality, default/recognizer
effects, compiler execution, arbitrary predicates and general mixed-wire inclusion
remain outside the proof/decision boundary. No performance claim follows from
these coverage proofs.


### Value-sensitive non-minimum raw rows

`Functional/RawArguments.lean` keeps `Functional.FunctionSignature`. `RawSpelling`
retains positional Types, individual key payload Types, key order and both escapes.
Its lower/upper raw bounds are proved independently of examples. `rawCovers` checks
all feasible grammar transitions at each raw offset; every recursive transition
consumes data/key state and tokens. Feasible fuel exhaustion refuses. The Scheme
implementation uses a request-local standard hash table for completed states and
its existing shared admission quota; no persistent memo certificate is introduced.

`rawCovers_sound` is universal over payload Types, all key permutations and all
RawSpelling derivations. Each supplied origin retains its own slot-admission law;
`rawSlots_sound` lifts that law to all supplied positions. `enumMarker_sound` and
`keywordMarker_sound` retain literal membership and the distinction between keys
and escapes. `stationaryRaw_sound` remains a sufficient envelope law. The current graph rule
below retains positions instead of imposing that envelope on every slot. The model does
not prove host memo allocation costs, actual Gerbil compiler execution, or automatic
assignment of decoded runtime values to their Type origins. That correspondence
and validator interpretation remain explicit premises plus runtime regression gates.

The existing top-level `Examples/TypedMethodDeclarations.lean` adds an Any-free
five-token endpoint: finite marker slots, two Integer payload slots and an exact
final rest escape. A Bool payload candidate refuses. Original prefix substitution,
complete unique inference and `buildCheckedShared` publish the chosen declaration;
`inferredValueCallback_sound` connects that publication to the universal raw-origin
law for every bounded spelling, and `valueEndpoint_payload` proves real subtype
inclusion for the endpoint's numeric payload. No new namespace is introduced.

Gerbil compiles existing `Keyword`, `Exactly` and `Enum` descriptors from checked
immutable literal syntax. Only raw-origin admission compares identity-preserving flat Union alternatives
extensionally; public Union bounds remain invariant, including flat Unions.
Wrapper-bearing Union never uses this raw-only inclusion.
`KeywordValueCallback` and its inference service enter the original unified
method-declaration/FUN/refine/bind-evidence chain. The 9331-row independent runtime
oracle and negative/nested-Function/stationary/budget controls reside in
`t/keyword-values-test.ss`. No recognizer is sampled to establish subtyping, no
incoming row is rewritten, and no missing evidence is repaired with Any.

This remains Appendix C/D future work. Opaque ordinary-value refinements, arbitrary predicate inclusion,
default effects and unrestricted inference remain outside the decidable boundary.


### Exact ordinary literals and correlated infinite tails

The current Scheme judgment replaces the per-region origin DAG/envelope with a
finite product of decoded position, remaining keys, raw offset and rest mode.
`Keyword` has no ordinary value; `Exactly`/`Enum` retain only ordinary literals for
that transition. Escape payloads and rest suffixes retain the full Type. Flat Union
and Maybe restrictions reuse the existing constructors; opaque/wrapper-bearing
origins remain conservative. The finite literal filtering equivalence and the
impossibility of a one-token protocol literal supplying itself as data are proved
by `ordinaryLiterals_mem` and `protocol_singleton_not_data`.

Independent counter limits preserve prefix positions and repeated rest Types.
`rawCounter_add`, `rawCounter_product`, `rawCounter_tail` and `inputAt_rawCounter`
prove transition and slot-lookup correspondence for arbitrarily large actual
positions. `rawTailCounts_complete` ensures a decoded tail still checks all later
raw source-arity regions, not only the shortest decoded representative's upper bound.

Reachable edges are recorded before backwards closure from legitimate endings.
The result then independently validates that all endings are live and every edge
into live starts live, along with ordered slot evidence. `rawGraphCheck_sound`
proves that evidence for every accepting path, including arbitrarily many repeated
cycles. `rawGraph_empty` excludes all accepting paths from a certified empty initial
state, so only truly unused arity regions may skip source/output requirements.
An unfinished visited set is insufficient; exhausted work never publishes evidence.

The existing top-level example adds a graph whose first slot excludes Bool while
later keyword payload slots admit it. Complete original inference and specialized
`buildCheckedShared` publication imply the universal graph-trace law in
`inferredCorrelatedCallback_sound`. The Scheme examples additionally compose a literal
rest-escape prefix with an infinite numeric rest family through existing declarations,
FUN/refine/bind-evidence. Nine new cases in `t/keyword-rest-test.ss` include a 3906-word
independent runtime oracle, tails through 257 positions, a late arity-12 bad first
source case, unused-result variance, literal controls and quota-before-builder failure.

The proof boundary remains explicit: concrete graph construction must cover the
decoder's typed-origin traces, and host validators must satisfy their interpretations.
The proofs establish universal certificate/counter/literal laws, not Gerbil compiler
correctness or unrestricted predicate inclusion. This advances the article's hypothetical
type protocol; arbitrary effects and opaque ordinary refinements remain future work.

### Closure representation and traversal reuse

Gerbil now shares one private arrow/target traversal between reachable product
construction and predecessor closure, and uses standard completed-result hash
memoization. `rawRegionCovers_ext` proves that changing live-set order or duplicate
representation while preserving membership cannot change the certificate judgment.
Traversal termination, producer completeness and concrete hash behavior remain
separate runtime obligations; quota exhaustion is still a refusal.

### Named Record views through the existing declaration driver

`Functional/RowTypes.lean` now reuses its closed-key shape rule for required/optional
Record fields. `recordCheck_sound` proves all source observations satisfy the
target view, assuming the supplied child comparison preserves observations.
Required targets require required source fields; missing optional fields require a
closed source. Open targets permit width and field reordering; closed targets
reject open sources and all extra declared keys. Construction order is unchanged.

`Examples/TypedMethodDeclarations.lean`'s `inferredRecordView` binds Self=UInt,
selects Super=Integer through a reordered nested callback view, and uses the
original `buildSelected` specialization/declaration builder.
`inferredRecordView_sound` transports the existing Type interpretation into the
record observation law after successful publication. The Gerbil example uses its
original inherited Record factory and FUN/refine/bind-evidence action. Independent
Class-validator controls include nine layouts, sixteen observations, optional
absence, hidden incompatible values, Function variance, Map key invariance and
refusal before consumption. This advances the type protocol future work from
Appendices C/D, not arbitrary Class subtyping, effect equality or mutable writes.


### Effective Function metadata

Function admission, negative-input traversal, inference views and descriptor
construction now share `call-with-function-types`. It uses Gerbil's `agetq`;
source-preserving substitution uses `map-in-order` and `alist->plist`, rather
than another positional option protocol. The existing Function descriptor still
owns argument/default/result checking and the existing FUN/refine/bind-evidence
chain owns consumption and publication.

Semantic candidate identity and subtype normalization use the same effective
schema: option binding order and explicit empty defaults do not create distinct
candidates. A rich signature has all four metadata bindings in descriptor order;
an all-default signature has no metadata tail. Captured source expressions retain
the original spelling. Case order, field construction order, keyword declaration
order, required-key payload order, Map key invariance and ordered Union branches
are preserved. Duplicate/unknown/malformed options and exhausted admission retain
typed refusal before builder execution; normalization supplies no Any fallback.

`t/function-options-test.ss` checks all 24 option orders, explicit defaults,
prefix substitution, nested callbacks, invariant Map keys, ordered Union/cases,
and a rich service callback through refinement and evidence binding. The Lean
FunctionSignature model proves permutation invariance for unique option kinds,
default elimination, normalization idempotence and substitution commutation.
Its typed input premise excludes unknown raw syntax; Gerbil admission tests cover
that boundary. These extend the article's type/MOP future work, not host compiler
or effect semantics, arbitrary predicate equivalence or unrestricted inference.


### Sentinel optionals in the finite type protocol

`OrFalse` now follows the same syntax admission, Type-child traversal, positive
recursion guard, specialization, observational covariance and descriptor compilation
as `Maybe`. Compilation calls the original `OrFalse` constructor; `optional-validation`
remains the sole runtime selected-child/sentinel validation protocol. No second
optional wrapper or generic dispatcher is introduced. The constructor-name predicate
is shared between prototype parameters and Mu binders, so the phases cannot admit
different free-variable vocabularies.

Only false is absent for OrFalse; only void is absent for Maybe. Nested optionals
retain both sentinels. The two constructors do not replace each other. Map keys
remain invariant and ordered Union branches remain literal; sentinel alternatives
are not erased or used as an Any fallback. Keyword-mode coverage inspects an
optional's exposed child: OrFalse UInt is token-stable, OrFalse Keyword is not.
Ordinary-origin restriction retains the optional constructor even when its child
reduces to Never, because the sentinel is still inhabited.

`OptionalRoutingServiceType` fixes the invariant Key prefix, jointly infers Self
and Super from nested callback inputs/results, then uses the original route method
fragments and FUN/refine/bind-evidence publication. Its regression controls include
unchanged false Map entries, wrapped present callbacks, missing Maybe values,
refinement refusal, ambiguity, bounded exhaustion and a complete fresh retry.
Controlled Mu expansion uses the existing decreasing approximant program: depth
zero remains Never, not false and not resource exhaustion. Negative recursion
through Function inputs still refuses. No arbitrary TypeValuePair-carried descriptor,
Class callback, semantic predicate or unrestricted recursive inclusion is inferred.

The Lean finite algebra now has distinct Maybe/OrFalse constructors, with recursive
identity, child covariance, substitution and conditional interpretation laws.
OptionalValidation proves sentinel-preserving inclusion and selected-child
membership after successful present normalization. The top-level route example
uses original bounded inference and the specialization/declaration builder and
proves publication retains both a complete replacement derivation and builder
result. Wrapper behavior/host effects remain interpretation premises. This is
Appendix C/D future work, not a claim about the original Racket implementation's
static inference or the correctness of Gerbil's compiler and collector.


### Scalar families and immutable labels

The finite language now includes the existing String and Symbol Types and
immutable Symbol values in Exactly/Enum. It compiles to the original runtime
descriptors. `scalar-recognizer` is one private table of built-in Gerbil predicates:
syntax admission, constructor reservation, flat literal inclusion and keyword-wire
stability use that shared lookup. Unknown names do not fall back to Any. This is
finite POO policy, not another implementation of Gerbil contracts: host `using`
admits the example observer, and the original descriptors own runtime validation.
Mutable/derived POO recognizers are not evaluated during finite derivation.

String and Symbol are separate families; their conversion methods imply no
replacement relation. Symbol data is distinct from keywords, #!key and #!rest.
Exactly/Enum literal names remain data during prefix substitution, even when they
spell a parameter or constructor. Uninterned symbol identity survives capture;
changing the caller's Enum list cannot change the compiled snapshot. Mutable
strings are accepted as String *values*, but remain unsupported literal metadata
for Exactly/Enum, preventing mutable keys from entering the finite literal algebra.
Map key invariance and ordered Union selection remain unchanged.

`TextServiceType` prefix-binds Label=Symbol and infers Value=String among explicit
Bool/Symbol/String candidates from input/result/callback observations. It uses the
original qualified fragment builder. Numeric and text services now share one
`signature-publication-action`: FUN approval, generic call, root refinement and
exact bind-evidence publication. Their policies supply their own descriptor; no
parallel effect interpreter or fallback dispatcher is introduced. Tests cover the
original scalar descriptors against independent host predicates, literal capture,
keyword transport, nested finite recursion, complete publication and fresh retry.

Lean extends the existing Atom algebra rather than adding a new type judgment.
`atom_inclusion` proves that an accepted scalar relation is identity or UInt <:
Integer; `text_distinct` excludes implicit text conversion. Original checker
soundness, substitution and finite inference laws continue to apply. The top-level
prototype example runs the original prefix/residual parameter binder and declaration
driver and proves successful publication retains all constraints and its builder
result. Its Symbol-family observation abstracts the finite literal label set; it
does not prove host predicates, symbol interning, conversion, parser or macro
implementation. These are Appendix C/D type-protocol future work. Arbitrary Class
callbacks, mutable literal semantics and unrestricted inference remain OPEN.
