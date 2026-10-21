# Finite inference audit and witnessed emptiness

This extends the article's Appendix C/D type-protocol future work. The Racket
reference motivates explicit subtype and modular-extension obligations; it does
not implement this finite candidate inference algorithm. An empty record value
used as a composition seed is inhabited and is not an empty Type.

## Joint final-source admission

Gerbil's final parameter getter could previously revise source syntax after its
equality check and still let signature preparation return a certificate. Later
binding getters could also invalidate earlier descriptors. The shared binding
continuation now finishes with a pure joint check of known direct revisions and
held binding metadata; source syntax/closed-suffix checks run after getters.
Whole declaration admission passes catalog walking as the same gate's consumer:
one grammar/binding validation surrounds getters, followed by pure postconditions
without repeating the complete parser or Type validator.
Retained root/nested signature origins are checked by direct revision after the
last source getter as well, under the existing catalog-current laws.
It uses existing revision/invalidation, Type and qualified declaration mechanisms,
without traversing the complete cached read-dependency graph or rerunning getters.

`DeclarativeMetadata.finalizeDeclaredSource` composes the existing source-snapshot
and bound-identity gates. Four laws preserve exact source equality, bound identity
and direct revision, exact artifacts, refusal and original callback exceptions.
Examples/Parameters.lean covers changed syntax, reopened parameters and changed
descriptor identity/revision. Gerbil regressions add staged finalizers, later
binding getter invalidation, real nested catalog reads, exact failure causes and
fresh inferred declaration/refine/bind-evidence/FUN/IO publication with callbacks.
Post-getter source interpretation and direct revision discipline remain host
correspondence premises. Effects are not rolled back; arbitrary transitive
callback semantics and compiler/heap correctness are not established. This closes
a finite future-work implementation omission and makes no elapsed-time claim.

## Complete requests before source refresh

Schema ownership alone did not protect caller-owned request inputs. Gerbil's
computed parameter getter could replace a `(UInt)` candidate buffer with `(Bool)`
before inference copied it. The shared explicit/prefix/raw/call entry paths now
capture all their input syntax before reading schema getters. One bounded copier
serves schemas and requests; canonicalization and query/call admission reuse owned
data. The existing solver and unified declaration continuations remain unchanged.

`PrototypeTypes.InferenceRequest` and `inferCapturedRequest` reuse `inferCaptured`
and the bounded solver. Four laws preserve exact capture/getter refusal, complete
classification, original candidate membership and every original bound. Top-level
Examples/Parameters.lean changes both live buffers after capture and checks empty,
ambiguous and refused requests. Gerbil controls cover all shared entry paths,
declaration-builder exclusion, nested Function wrapping and the complete observed
descriptor-service refine/bind-evidence/FUN/IO chain with failure/retry.
Faithful syntax capture, candidate enumeration and call projection remain host
correspondence premises. Runtime nonaliasing is tested; arbitrary concurrent raw
mutation, effect rollback and compiler correctness are not inferred from Lean's
immutable request records. This advances the article's finite type-system future
work and makes no performance improvement claim.

## Captured schemas before computed metadata

Gerbil's shared schema gate now bounds and copies variables, expressions, bounds
and binding-list topology before computed parameter getters or Type admission.
Previously a getter could weaken `Self <: Super` into `Self <: Self` before the
copy, admitting the forbidden Integer-output/UInt-input instantiation. Original
descriptor identities and revision stamps remain unchanged; existing prefix,
inference and whole-declaration mechanisms consume one captured schema.

`PrototypeTypes.inferCaptured` composes faithful immutable constraint capture,
source refresh and the existing complete bounded solver. Its four laws preserve
capture/getter refusal order, exact classification and every original accepted
bound. Examples/Parameters.lean distinguishes the original unique solve from the
extra candidate accepted by a live-buffer reread, and retains exhaustion.
The Gerbil observed descriptor-service example carries this through nested
Function wrapping, qualified declarations, refine/bind-evidence and FUN/IO,
including rejected publication and retry. Host syntax projection and actual heap
nonaliasing remain explicit runtime correspondence premises. Arbitrary callback
purity, rollback, unrestricted inference and compiler verification are not proved.

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

### Impossible container origins in raw keyword coverage

A reproduced mismatch remained between ordinary replacement and the raw decoder
product graph: `Never` keyword payloads were recognized as impossible, while
`(Pair Never Function)`, impossible Tuples/rows and empty TypeValuePair directories
were treated as potentially supplied. This refused valid positional callbacks
for keyword callers whose retired keyword cannot carry any actual value.

The duplicate scalar-only `empty-origin?` algorithm is removed. The graph now
reuses the same positive finite `empty-type?` witness as ordinary replacement for
positional, ordinary and keyword payload origins. Gerbil `hash-ensure-ref` caches
only completed true/false results within this graph; quota/host exceptions never
install an answer. The existing work counter covers witness preparation and
traversal. No successful coverage, approval or source snapshot is cached across
requests or revisions.

This is not permission to discard empty collections. Nil inhabits List Never;
empty Maps/vectors and optional void/false sentinels remain live keyword payloads.
Unknown Class/Schema descriptors cannot supply emptiness evidence. Source clause
selection, raw/rest position correlation, marker/keyword boundaries, exact output
variance and original ordered descriptor metadata remain unchanged. Complete
backwards closure is still required even for a region claimed to have no calls.
Unsupported syntax and work exhaustion remain typed request failures.

`RetiredKeywordServiceType` and `infer-retired-keyword-service` reuse the existing
prefix solver and qualified declaration factory. The returned positional callback
uses the existing Gerbil argument decoder, rather than another parser. The
`keyword-rest-test.ss` workflow combines inferred metadata, raw escapes, infinite
rest tails, recursive callback wrapping, FUN/refine/bind-evidence, exact context,
policy refusal/retry and genuine candidate ambiguity. Actual retired payloads and
live incompatible outputs refuse before consumer admission. The original retired
keyword stays in the target contract; it is not removed from the declaration.

Lean's existing FunctionSignature protocol adds `rawPruneEdges_mem` and
`rawGraphPath_prune`: under a sound positive witness, every realizable original
trace retains exactly its ordered edges, including arbitrarily many rest cycles.
`rawGraphCheck_pruned_sound` composes this with the existing complete closure
certificate, retaining a selected source and every slot law for each actual call.
Top-level `Examples/RawArguments.lean` includes complete unique
publication with the original graph, dead/live edges, fuel and missing-source
controls. Host decoder correspondence and child-witness interpretation remain
explicit; arbitrary predicate implication, compiler/runtime correctness, effects
and performance are not proved. This advances the article's finite type-protocol
future work, rather than an already implemented Racket inference solver.

## Original field selection during signature preparation

A computed parameter getter could rewrite a caller-owned Object method path
before `instance-signature` selected its Function. A different valid sibling
therefore supplied the descriptor and private origin stamp. Signature preparation
now admits and copies the complete finite symbolic path before any instance or
binding getter. Selection and provenance use the same owned path; later requests
observe subsequent buffer edits. Shared Function path admission replaces the two
walkers' duplicate checks. Cycles, malformed paths and exhausted requests refuse
before source effects; getter errors retain their original cause. Negative-watch
payload immutability/purity remains the existing dispatch precondition.

The nested run/audit example combines candidate inference, whole declaration
admission, returned Function wrapping, refinement and exact evidence publication
through FUN/IO, including approval/policy refusal and retry. Lean proves capture
and refresh failure order and successful selection at the original path, under
faithful host capture/refresh/compiler interpretation. This advances finite type
future work; it proves neither arbitrary mutation/rollback nor Scheme compilation.

`FunctionSignature.prepareSelectedPath` composes capture, refresh and compilation;
its `capture_error`, `refresh_error`, `eq` and `sound` laws retain the original
selection. `Examples/Parameters.lean` distinguishes run's two outputs from audit's
single output and checks later-request selection and failure ordering. Scheme's
`examples/signature-service.ss` and candidate-inference regressions execute the
corresponding nested publication chain. Direct source/binding revision checks
remain in force; no Any fallback or transitive callback stability is introduced.

## Coherent Type parameter binding

A source `.parameters` list could change order after schema admission but before
ordinary positional specialization read it again. Pure instantiation then returned
`(Pair UInt Bool)` with actual fields T=Bool and U=UInt. Prefix and inferred
assembly now share `bind-type-parameters`, which compares the original variable
order with the SAME name snapshot consumed by the existing positional binder.
Reordered/added/removed valid names refuse `bounds` before cloning. No second
getter follows admission; generic `specialize` also uses this single implementation.
Gerbil's multi-binding `using` handles the new continuation's ordinary contracts;
standard take/drop and existing persistent `.cc` still own construction.

Eight typed entry paths and three metadata changes exercise the complete boundary.
A generic control edits the source after snapshot admission and proves construction
still uses that snapshot. Original getter/admission failures retain their cause.
Repair through the supported slot protocol permits an independent request; the
shared signature-service action then composes prefix specialization, inference,
qualified declarations, recursive Function wrapping, refine and exact evidence/FUN/IO
publication. Nonunique reports remain explicit application errors, not guessed Types.

Lean's existing Parameters namespace proves original order, exact residual suffix,
field mapping, excessive-argument refusal and incremental composition. The generic
positional model's `declaration` refusal represents the typed host's `bounds` gate;
source errors are transported separately. Host snapshot/admission/descriptor
interpretation are premises, not compiler/heap/concurrent-mutation proofs. This
advances the finite type future work without extending its research boundary.

`Parameters.specializeExpected` and its six laws model the shared gate;
`Examples/Parameters.lean` contrasts swapped old fields with rejected order changes
and exact direct/staged bindings. The executable acceptance is in parameters-test
and candidate-inference-test, including the full specialized-action example.
Admission callbacks must preserve the copied names they receive. Arbitrary
callback purity, rollback, transitive source stability and unbounded inference
remain outside this protocol. Existing resource limits and full checks remain required.

## Retained bindings through source refresh and construction

A residual schema's earlier Type parameter could be replaced during a later
`.parameters` getter, while its remaining names stayed unchanged. Pure construction
returned `(Pair (List UInt) Bool)` with actual T=Bool; immediate bound inspection
then rejected that already-returned instance. A direct revision edit to the retained
composite descriptor exposed the same omission.

One private `with-checked-bindings` continuation now reuses existing identity and
revision admission around the whole consumer, followed by its callback-free final
revision fence. Schema preparation, actual positional binding and public bound
inspection share it. No getter runs after the fence; no second grammar walk or
new constructor is introduced. Supported slot-definition changes and direct Type
revisions refuse bounds before a successful result escapes. Original failures
keep their cause and prior effects; repair/retry never lowers a revision stamp.

Nine typed entry paths cover each relevant parameter-read phase for retained
identity and revision changes, with no early builder. A higher-order residual
service retains an Input Function, infers its Output Function and returns a
converter producing another checked Function. Fresh reconstruction, policy
refusal, recursive wrapping and exact evidence publication use the existing
qualified declarations/refine/FUN/IO chain.

Parameters.specializeCurrent composes existing retained-binding and checked-name
models. Its five laws prove stale/order refusal, reuse, exact new fields/suffix
and preservation of every disjoint retained identity/revision, plus original
inspection errors. The existing prepareDeclaredSignature laws supply the enclosing
before/after-callback admission; no parallel effect model is added. Faithful host
snapshots and revision propagation for supported edits are premises. Arbitrary
raw/concurrent mutation, transitive callback discovery and compiler correctness
remain outside this finite future-work protocol. Full checks and resource limits
remain unchanged.

## Public Type request ownership

A live finite-directory observer could rewrite another public operand during
admission: a false Tuple replacement became true, and nested Function compilation
could accept a Bool after its caller syntax was edited. Public `expression-type`,
`subtype-expression?` and `function-covers?` now share `call-with-type-inputs`:
Gerbil's ordered map captures EVERY operand with the existing bounded copier
before invoking the original consumer. Internal inference already owns its input
and continues to use its existing checked operations without another copy.

Source order, leaf/token identity, ordered clauses, errors and one request quota
remain. Copy visits consume that quota; exhaustion before admission invokes no
observer. Callback edits remain visible to later independent requests, and their
original exceptions are not replaced. Existing catalog invalidation still refuses
stale sources; this is not a permanent metadata certificate or a rollback policy.

`checked-operation-action` composes an explicit compiled operation contract with
prefix specialization, finite constraint inference, qualified declarations and the
existing refine/bind-evidence/FUN/IO service. Controls cover both binary operands,
shape changes, an invalid sibling that an observer tries to erase, nested wrapper
inputs/results, policy refusal and fresh retry. Lean `withCapturedInputs` proves
original-input consumption, error preservation and composition with `check_sound`,
conditional on faithful host capture and Type interpretation. It does not prove
Scheme heap copying, arbitrary callback behavior or compiler correctness. This
advances the article's type-protocol future work, not a missing Racket theorem.
