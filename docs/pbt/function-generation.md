# Function generation and observation

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [P19: call-input demand and derivation reuse](#p19-call-input-demand-and-derivation-reuse)
- [P33: sound short-circuit admission of supplied Function call fields](#p33-sound-short-circuit-admission-of-supplied-function-call-fields)
- [P61: first-observed Function input declarations](#p61-first-observed-function-input-declarations)
- [P74: first-observed finite Function result tuples](#p74-first-observed-finite-function-result-tuples)
- [P78: captured finite Function call requests](#p78-captured-finite-function-call-requests)
- [P85: first-return ownership of Function call declarations](#p85-first-return-ownership-of-function-call-declarations)

## P19: call-input demand and derivation reuse

The typed Gerbil call generator previously eagerly prepared every declared input
Type, even a completely shadowed case-lambda clause or an absent rest suffix.
An unused constructor exception could therefore refuse an otherwise supported
call language. It now captures input identities immediately and derives only the
supplied fields of the structurally selected first clause, using the project's
existing `defonce` / Gerbil promises. Successful derivation is shared across
occurrences, shrinking and replay; actual sample values are never cached. Selected
unsupported Types still fail with their exact cause and no Any/branch fallback.

`demandInput` / `demandInputs` and eight laws in `PropertyGenerators.lean` model
identity lookup, successful reuse, exact errors, demand locality, empty rows,
repeated fields, stopping after refusal and preserving earlier cache entries.
The existing signature-selection laws determine the actual demanded row. Source
currentness remains a separate necessary guard: unforced declared Types remain
parent dependencies, and demanded children retain their transitive sample guards.
Regression controls and a keyword/optional/rest/multiple-return Function workflow
compose Record configuration, FUN, shrinking, concrete/seed replay and fresh retry.

This models finite sequential demand under faithful descriptor identity and
promise reuse. It does not prove the host promise runtime, callback termination,
concurrent forcing, hidden mutation, GC or constant-time preparation. Constructor
failure occurs during demand before the property, rather than being rewritten as
falsification. General Type synthesis remains outside the declared algorithm.

## P33: sound short-circuit admission of supplied Function call fields

The audit found a value-admission defect in the project's `FunctionArguments`
recognizer. `(FunctionArguments (Function [Integer] [Integer]))` accepted the raw
row `("bad")`, while the real checked Function rejected that call with TypeError.
The field conjunction was evaluated and then discarded by a trailing let-body
`#t`. Positional validation also used eager `map`: an early false predicate could
still run a later throwing predicate and replace ordinary refusal with its error.

`testing/function.ss` now returns the actual field conjunction and uses Gerbil's
runtime `andmap` for the paired positional Type/value walk. It is the standard
short-circuit traversal in `src/gerbil/runtime/util.ss`, not another evaluator.
Each supplied positional/optional/rest/keyword field uses the existing source
boundary. A false field stops later predicates; an exception remains exact; a
registered revision refuses before the next field. There is no fallback Type,
new namespace, shape search, value-based clause backtracking or default evaluation.
Selection/encoding/decoding still use the runtime signature protocol, so ordered
case-lambda first match and keyword/escaped-literal interpretation are unchanged.
This guards the project's finite supplied-field walk, not arbitrary operations
inside a user Type predicate or unrelated Type implementations.

Six ordinary cases in the existing representation suite cover required/optional/
rest rejection, keyword ordering/omission and escaped literals, inherited producer
sources, shadowed clauses and exact errors, invalid generated rows rejected before
the property, and complex service integration. Real checked Function wrapping is
an independent rejection control. `service-admission-tests` extends the existing
signature-service example: explicit input domains, optional callback Lists and
keywords compose with actual service defaults, checked nested Functions and FUN.
The correct service passes; a host implementation discrepancy supplies a typed
witness that shrinks and supports concrete and seed replay. PropertyConfiguration
remains the standard Record. No generic-kernel dependency or runner is added; the
independent standard-library package remains 97 cases.

Eight `guardedAll` laws extend the existing PropertyProducts module with the
source-checked Boolean fold: empty admission, stale preflight, exact false/true
head behavior, revision refusal, original causes, equivalence to `List.all` for
fresh pure outcomes, and suppression of subsequent stages after refusal. Source
scope fidelity, fixed ordered supplied fields, accurate pure observers and
terminating predicate calls remain premises. A domain rejection is not a false
property witness; host contracts, arbitrary Type callbacks, termination, GC and
wall-clock behavior are not verified by these laws. Omitted inputs do no predicate
work; active supplied-field source checks still have their ledger cost. No timing
improvement is claimed.

The [Rackcheck filter structure](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt)
short-circuits before constructing accepted descendants; the Gerbil standard
conjunction expresses the corresponding finite field-admission policy here.
The 1G source-interpreter aggregate-module load failed before suite execution and
is not counted as acceptance. The focused compiled suite runs through the standard
CLI with the same 1G/90-second gate; complete checks run without its focused filter.
Process, depth, search, node and proposal limits remain unchanged.


## P61: first-observed Function input declarations

The audit found a preparation defect, rather than a missing generator domain:
a delayed nested signature keyword getter could revise its enclosing Function.
The old FunctionArguments sampler then captured the new epoch and returned current.
The frozen reproduction checks revision/read count 0 immediately before public
`generator` entry; the old result was revision 1 / accepted-current. Effects during
caller-side initialized object construction are outside this boundary.

FunctionArguments now captures the Function before its signature getter, clauses
before clause metadata, and each returned positional/optional/keyword/rest Type
before the next getter. It reuses the typed source ledger and action scope through
normal module imports. Field spines and keyword entry pairs are copied at discovery;
known identities never renew their first epoch. The existing early keyword-mode
pass and ordered clause semantics remain. Metadata callback causes, including
thrown false and MOP's self-mutation error, keep their original precedence.

One source guard on the existing shape generator carries the completed epochs
through bind, the standard 128-entry LRU, products and lazy child promises. There is
no second cache, signature clone, replacement parser, or per-consumer wrapper.
Shadowed and omitted children stay unforced; output Types and optional defaults
are not inspected to generate supplied inputs. A cached layout cannot acquire new
authority by a hit or by clearing a sampler's public dependency list. Fresh retry
requires explicit new preparation, while old reports remain obsolete.

Six regression cases cover Function/clause retirement, earlier positional and
keyword Type retirement, exact callback causes and dynamic-scope restoration,
dormant inputs in ordered signatures and cached-layout renewal refusal. The complex
service example combines nested Function callbacks, List inputs, optional/keyword
shapes, a FUN action, shrinking, concrete/seeded replay, retirement and explicit
corrected retry. Existing unsupported-domain failures remain explicit.

Eight finite Lean laws in PropertyPreparation model guarded discovery, exact
causes, first-observation retention, stale cached work, bookkeeping cardinality and
refusal before construction. Top-level examples include duplicate input IDs,
false causes, obsolete layouts and explicit renewal. Source clocks, faithful
shallow copying, standard MOP behavior and terminating callbacks are premises.
Unversioned mutation of hidden metadata aliases and concurrent heap isolation are
not proved. The size bound counts retained identities, not elapsed time or total
hash-table work. This is the RFC's finite future-work protocol, not a claim about
the compiler/runtime or completion of unrestricted recursive/type generation.
All full acceptance checks and resource limits remain unchanged.

## P74: first-observed finite Function result tuples

Two public probes exposed late aggregate admission. A first result producer
returned an invalid scalar, yet the next row still ran and threw false, replacing
the tuple-protocol error. A later draw could also change a previously returned
tuple spine before the final table copied it: the first row changed from `(7)`
to `(99)`. This is the finite table's ordered result boundary, not unrestricted
procedure inference or a promise to freeze arbitrary generated payloads.

The generic generator now maps one private tuple recognizer/copier over the
result producer before building the existing fixed product. Each normal result
must be a proper finite list and its spine is owned before the next draw.
`function-tree` receives only that checked product and no longer repeats a full
shape scan and tuple copy for every assembled table. This uses the existing
`generator-map` and `generator-sequence` algebra, without another protocol, public
namespace, sampler class, iterator, random-source owner or compatibility path.

Ordinary malformed tuples retain `finite function results must be value tuples`,
now with the first offending tuple as irritant rather than a completed aggregate.
Original draw exceptions, including raised false, remain exact. Source retirement
still wins after a normally returned draw and before tuple admission. Empty tuples
mean zero return values; a tuple containing false remains present data. Malformed
lazy children still fail before returning a proposal and therefore do not acquire
a proposal charge. Existing raw keyword rows, call forwarding and multiple-value
delivery stay with the standard finite-function procedure. Empty input directories
invoke no result producer; the outer generator keeps its own source admission.

This captures stored result tuple spines only. Mutable payload objects and hidden
preimage values retain their declared immutability/source obligations; mapping
does not deep-freeze an advanced producer's original tree. Coordinate shrinking
continues to retain unchanged product siblings and their first-observed sources.
Seed splitting, supplied result neighborhoods and portable table restoration are
unchanged. No wall-clock or universal allocation improvement is claimed.

Four independent cases cover early malformed/cyclic/improper tuple refusal,
shallow spine ownership with payload identity, source/cause/charged-proposal
priority, and seed-state equality, real shrinking, both replays and portable
finite-table restoration. All previous cases remain; the isolated package now
requires 216 cases. A complex Record/Function/FUN service deliberately produces
an invalid first result and a later false cause, repairs explicitly, shrinks a
real finite dispatch table, validates Tuple wire data, restores wrapped Function
fields and rejects old source epochs before fresh retry.

Eight finite Lean laws in PropertyProducts reuse `finiteSequenceParameters` for
the same ordered guarded traversal. They prove empty-row behavior, first refusal,
first tuple retention, no partial table on tail failure, head lookup, exact table
length and complete key/order preservation. Five top-level examples distinguish
malformed results, false causes, source retirement, captured false data and
zero-value tuples. Faithful shallow host copying, the fixed product invariant,
accurate source observers, declared payload laws and terminating sequential
callbacks remain premises. These are finite protocol proofs, not verification of
Gerbil/Gambit, arbitrary mutable preimages or unrestricted Function behavior.
This advances the paper's future work.

The pinned Rackcheck `gen:bind` and shrink-tree mapping remain the source model:
compose admission into the retained producer tree, rather than redraw or validate
an already completed aggregate. This unit changes neither that seed discipline
nor the existing lazy shrinking policy. All checks, heaps, compiler completion
and cancellation behavior remain unchanged.

## P78: captured finite Function call requests

The audit reproduced a request-ownership defect through public function-apply.
The caller supplied `(declared)` to a table containing declared and retargeted
rows. Its table observer rewrote that caller-owned spine before lookup, and the
call returned the retargeted row's `(2)` instead of the requested `(1)`. The same
ordering allowed malformed direct request spines to enter source observation.
This concerns finite request topology, not inference about arbitrary Functions
or deep immutability of argument payloads.

The generator module now has one private function-results operation containing
the existing with-function source boundary, exact-row lookup and detached result
tuple. Public function-apply admits a proper finite list and shallow-copies its
spine before entering that operation. The ordinary function-procedure passes its
already owned rest row directly to the SAME operation. There is no second lookup,
per-call Type wrapper, new record, module or namespace. The procedure path adds
no request recopy; the direct public path pays for one copy of its row width.
Gerbil still owns rest construction, keyword forwarding and multiple values.
No host allocation/time theorem or latency improvement is claimed.

A malformed direct row refuses through the standard contract before inherited
or table observers. Well-shaped requests retain their existing inherited/table
source priority, strict Boolean judgments and exact callback exceptions. Unknown
rows keep the ordinary finite-domain Error, now carrying the captured request
rather than a retargeted spine. Raw keyword order and escape representation stay
part of row identity; no call-language decoding or value normalization is added.
Source changes still refuse normal publication. Payloads, including false values,
mutable domain objects and procedures, retain their identities and declared source
laws. This does not freeze nested mutable payloads or roll back observer effects.

Four generic regression cases cover source-side head/improper/cyclic spine edits,
pre-observer refusal of malformed direct requests, captured unknown-row diagnostics
with payload identity, and shared direct/procedure behavior for empty rows, zero
and multiple values, raw keywords, false/object causes and stale tables. The cases
join the existing PropertyProducts example module and ordinary kernel suite;
there is no new runner/module inventory. The isolated standard-library package
requires 231 cases. Existing P43 inherited-scope and P74 result-tuple tests remain.

The existing finite-service Record/Function example composes FUN preparation,
first-row malformed-result refusal, real shrinking, seed/concrete replay and
portable Tuple restoration. Its decoder deliberately exposes a raw call row to
the restored table's observer; the direct call must retain the requested first
result before normal Record construction wraps the Function. Owner revision still
rejects the old report/codec and explicit fresh preparation retries. The example
uses the standard codec and existing service factory rather than a new adapter.

Seven finite PropertyProducts laws reuse guardedGeneration and lookupFunction:
malformed requests skip source actions; stale preflight, observer exceptions and
post-observation retirement refuses normal publication; lookup errors keep their
cause without a trailing check replacing it; admitted lookup uses
the initially captured row; missing rows cannot be retargeted into known rows;
and an already owned procedure row delegates to the identical operation. Five
top-level examples distinguish changed caller state, unknown rows, skipped throwing
observers, empty rows and false results. Faithful proper-list recognition/shallow
copying, standard rest ownership, source normalization, terminating sequential
actions and lawful payload equality remain premises. No compiler/runtime or
unrestricted concurrent-mutation proof is claimed. This advances future work.

The Rackcheck/Quickcheck map/bind comparison remains the abstraction reference:
retain the same finite value/tree and ownership boundary rather than introduce
another executor. This unit closes our P43 finite-call request boundary, not a
missing Racket feature. The explicit P35 rule that invalid classification symbols
are API errors was audited and retained as a design boundary. Complete checks,
original heaps, natural compiler/test completion and cancellation stay unchanged.

## P85: first-return ownership of Function call declarations

The next audit checked call generation alongside dependency shrinking and replay.
P45 owned declarations before LATER metadata getters, but its read action returned
through inherited source observers before signatures/input/keyword/rest owners
were registered. A supported .set! revision at that exact boundary produced
`changed=#t accepted-current=#t`. A complex optional/keyword CaseFunction probe
then entered an input factory and the target instead of refusing preparation:
`first-status=failed factories=1 properties=2`. This is a declared-source version
hole, not unrestricted inference or an untracked payload-mutation request.

FunctionArguments now performs each metadata capture inside its existing read
action. A complete source row first passes ordinary Object admission, then pure
identity/revision bookkeeping extends the existing ledger before any returning
observer. Required/optional input and clause rows own their copied spines; keyword
capture constructs its owned spine and entry pairs directly with one map, then
registers the Types. Present rest Types use the same action; false remains absence.
There is no speculative child derivation. The early keyword pass and existing
metadata read order, including repeated rest reads, stay intact.

One read operation carries either the captured metadata or its stored preparation
failure using standard multiple values and an explicit refusal Boolean. Raw getter
exceptions remain outside that catch and bypass trailing checks unchanged. Pure
shape/member errors are raised only after the original source gate; observer
causes retain priority, including a thrown false. Whole-row member admission
precedes stamp publication, so invalid later members do not partially publish a
new row. The previous nested snapshot/observer passes in retain! are removed;
the getter boundary now owns those checks. No new registry, record, namespace,
framework, public API or compatibility path is introduced.

Four focused cases cover signatures, inputs, optional, keywords and rest; first
return revision before all factories; exact getter/observer false and object
causes; Object member refusal before later fields; and one shared promised Type
across multiple positional, optional, rest and keyword positions. The existing
signature-service suite adds a complete ordered CaseFunction with optional nested
Function callbacks, keywords, host defaults, layout caching and a shadowed unsupported
input Type. Initial retirement is a stale preparation report with zero factories,
properties, defaults and attempts. Fresh preparation genuinely shrinks the input,
reuses one child factory, never forces the shadowed child, preserves checked target
admission, replays both seed and concrete failure, rejects old owners and retries
a corrected property through FUN. Generic kernel code and its 239-case independent
standard-library suite are unchanged; module registration/entrypoints are reused.

Eight PropertyDiscovery laws model successful pure capture with source rows and
owned payloads, or failed capture with no published new stamps. They prove exact
successful delivery, retirement before publication, delayed member failure,
observer priority over failed and successful capture, known-epoch retention,
prior-stale refusal and suppression of dependent factories/targets. Five top-level
examples distinguish newly revised Types, duplicate identities, false observer
causes, false capture causes and ordinary false rest metadata. Existing
captureSources_cost supplies ledger growth bounds. Object recognition, primitive
revision reads, pure bookkeeping, faithful row copying and terminating sequential
callbacks remain premises; validation of arbitrary redefined fundamental Object
behavior or compiler/runtime semantics is not claimed.

Shape selection and runtime Function admission still use the declared Function
under the existing explicit revision discipline. This does not freeze arbitrary
Type payload mutation without revision, clone the entire call language, infer
opaque callback dependencies or prove callback termination, GC/RSS or latency.
The source-epoch gate is the concrete future-work construction being closed here.

The author/Racket composition reference remains one owned declaration boundary,
then the existing promise, product, LRU and replay algebra. Gerbil using, with-catch,
values and standard hash/list operations implement it; Record/Function and FUN
express the downstream workflow. Complete checks, 2 GiB main/1 GiB isolated guards,
cancellation and authorized natural compiler/test completion remain unchanged.
No upstream edits, versioned JSON, full benchmark artifacts or subagents are added.
