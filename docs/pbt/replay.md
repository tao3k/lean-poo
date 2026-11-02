# Counterexample replay and portable handoff

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Revisions, failures and replay](#revisions-failures-and-replay)
- [Source-consistent policy and product admission](#source-consistent-policy-and-product-admission)
- [Source-consistent portable handoff stages](#source-consistent-portable-handoff-stages)
- [Local portable-handoff authority reaches nested checked actions](#local-portable-handoff-authority-reaches-nested-checked-actions)
- [Portable handoff request admission and physical framing](#portable-handoff-request-admission-and-physical-framing)
- [Stable symbol and keyword identities in portable replay](#stable-symbol-and-keyword-identities-in-portable-replay)
- [Shared Boolean source admission during portable replay](#shared-boolean-source-admission-during-portable-replay)

## Revisions, failures and replay

Specification sources and system-under-test state have different roles:

- Descriptor/model/factory recipes are stable specification dependencies. Their
  mutation makes the PBT result `stale` and refuses old witness/seed replay.
- Per-trial table metadata, pending deltas and collection revisions are fixture
  state. Intentional changes to them are tested operations, not specification
  mutation. Do not register every mutable fixture as a stable PBT dependency.

Retain the existing `passed`, `failed`, `error`, `stale`, `exhausted` and
`unsupported` distinctions. Only valid Boolean-false observations create shrinkable
`failed` witnesses. Zero cases are refused. Unsupported generation, stale
specifications, process limits and unexpected exceptions never mean pass.
An ordinary stale TABLE result may be expected by a command; it must not be
confused with a stale PBT specification.

Reports retain their original and reduced concrete traces, seed, trial, effective
limits and source snapshot through the current property-report mechanism.
Concrete replay checks current sources and trace admission before opening a fresh
fixture; it does not consult the PRNG. Seed replay remains runtime/PRNG dependent.
V1 reports are in-process Scheme values, not portable closure bundles. Data-only
commands may be printed/read with standard Scheme tooling for explicit reproduction;
no versioned JSON, full benchmark datasets or archives are committed. Replaying on
changed code is a new experiment and cannot inherit an old report's authority.

## Source-consistent policy and product admission

Audit finding: shrink admission wrapped the policy precondition and property as
one action. A precondition that returned true after revising a declared source
could therefore enter the property before the outer stale check. Fixed products
similarly checked sources around the aggregate predicate/measure, allowing later
field effects after an earlier field invalidated their captured specification.
Negative controls reproduced all three forbidden downstream calls before repair.
These are sequential source-admission defects, not unrestricted effect inference.

The existing hygienic `with-current` form now brackets shrink eligibility before
property entry, reusing the run's own nonlocal stale exit. Stable exclusion remains
non-falsification and adds no generation coverage. Products reuse that same form
around each field predicate and weight, checking every captured domain source
between callbacks. Gerbil's standard `map-in-order` supplies ordered measurement;
there is no new callback framework, namespace or source cache. Generator, root,
shrink and concrete replay retain their existing owners and reports.

A refusal never installs the in-flight proposal. Its already returned attempt
remains charged, the previous confirmed witness survives, no minimum is certified,
and callback exception identity is retained even if the source also changed.
Fresh execution may capture revised sources; seed replay of stale reports may not.
Already executed callback effects are not rolled back. Observers must be accurate,
pure and terminating; each application must declare its mutable dependencies.

Regressions cover true/false stale eligibility, cross-field recognition and
measurement invalidation, skipped later callbacks, original policy exceptions,
retained witness/attempt accounting, stable exclusions and unchanged coverage.
The FUN/Record example revises shared policy rules during shrinking, rejects the
old report, then prepares a new execution that shrinks and replays successfully.
The isolated generic suite now runs 55 cases without POO modules.

Lean composes the existing guarded state callback model into ordered product
stages and a shrink-policy judgment. Seven laws cover immediate and arbitrary
prefix refusal, original causes, stale Boolean policy returns, stable exclusion
and admitted evaluation. Concrete controls use effect markers for forbidden
later fields/properties. These finite laws require a faithful host interpretation;
they do not prove arbitrary source observers or concurrent atomicity.

With N product fields, successful full recognition/measurement adds two aggregate
source checks per visited callback, each checking up to N domains. This may cost
O(N²) observer calls; arbitrary observers offer no invalidation notification that
would justify caching a once-true result. Host callback and observer costs remain
explicit, and all existing runtime limits and proposal budgets remain unchanged.
No speedup or global effect safety is claimed.

[Rackcheck](https://docs.racket-lang.org/rackcheck/index.html) supplies the lazy
generator/property composition comparison. Revision observers are this protocol's
additional responsibility; this change does not claim Rackcheck implements them.

## Source-consistent portable handoff stages

Audit finding: export reconfirmation and encoding shared one codec boundary. A
property could invalidate codec metadata while leaving its witness domain stable,
then still invoke that stale codec's encoder. Import likewise consumed an envelope
before its first provenance preflight, even when the codec or specification was
already stale. Negative controls reproduced one forbidden encoder invocation and
an unexpectedly consumed input datum before the fix.

The existing `with-codec` now owns distinct confirmation, encoding and delivery
stages. A normally returning confirmation checks both application and codec
provenance before encoding starts. Encoder refusal still precedes every output
prefix. Import preflights both sources before its first read, then checks the
bounded envelope read, trailing-data check, decode and concrete-witness admission
at their existing boundaries. Invalid policy configuration remains first; stale
preflight now precedes input parsing and identity admission. For current sources,
identity and trailing-data errors still precede decoder/property callbacks.

No codec registry, port wrapper, serializer or runner is introduced. Standard
Gerbil ports and the existing explicit data codec retain format identity, payload
budgets and Function reconstruction. An already stale read leaves input untouched;
once I/O has started, consumed/emitted bytes are not rolled back. A port or
callback exception keeps its own cause even if sources also changed. Atomic
publication, arbitrary reader allocation and concurrent source changes between
checks remain outside these finite sequential guarantees.

Acceptance covers confirmation invalidation, zero encoder/output effects, stale
input preflight, original confirmation exceptions, and fresh codec preparation.
The typed FUN example shrinks a Record with a Function field, retires codec
metadata during export reconfirmation, retries using a new codec, rejects the old
codec without consuming input, and reconstructs the checked Function through the
ordinary Record constructor. Generic coverage/decoder/encoder/corpus tests remain
unchanged in scope; the isolated generic kernel inventory stays at 55 cases.

Lean composes existing guarded callbacks into confirmation/encoding/delivery.
Seven laws prove preflight refusal, confirmation source/cause refusal, encoder
source/cause refusal, exact stable payload handoff and original port causes.
Controls distinguish skipped later actions from post-delivery refusal. Faithful
witness confirmation, observer accuracy and callback termination remain premises;
no host I/O rollback or compiler correctness is asserted.

Export adds one constant codec/context boundary between reconfirmation and encoding;
import adds guarded read/trailing-data stages. Existing data-copy node/depth budgets
are unchanged. Observer, serialization and host port costs are not claimed zero,
and no wall-clock speedup is asserted. This preserves the generator/property
separation learned from [Rackcheck](https://docs.racket-lang.org/rackcheck/index.html)
while enforcing this library's additional revision protocol.

## Local portable-handoff authority reaches nested checked actions

A codec encoder could retire its registered source, invoke a nested generator's
mapper once, and only then refuse export. The application correctly received an
error and zero output bytes, but obsolete nested work had already occurred. The
same omission affected decoder/context authority and witness reconfirmation.
This is a reproduced implementation gap in the registered-source protocol, not a
request to interrupt arbitrary Scheme statements or inspect hidden closure state.

The existing `with-codec` stage now installs its existing `check` through
`with-generation-check`, inside the existing inherited `with-sources` scope.
Nested generator, domain and portable actions observe local codec and application
sources before effects and after normal returns. The ordered codec/context error
checks and original thrown causes remain unchanged. Standard dynamic scope owns
unwinding; the checker is never copied to a decoded value, child tree or report.
No new scope representation, runner, stream or per-callback wrapper is added.

Six generic cases cover encode/decode under either local owner, witness
reconfirmation, nested refusal priority and cleanup, exact callback errors,
non-retention and explicit epoch-bound retry. The isolated standard-library test
package now requires all 109 cases. `service-corpus-action` in the existing
generated-products example composes typed property Reader/FUN delivery with
portable export. Strict Records and existing Function contracts own service
validation; caller codecs own data-only reconstruction. One complex case covers
obsolete nested packing on both export and import, no premature consumer/property
call, fresh preparation, named Record output bundles, both replay modes, Function
argument refusal and rejection of the old codec. No runtime dependency on Lean
is introduced.

Two whole-execution laws in `PropertyScopes.lean` prove that merged transient
scopes require both parents at every finite stage, and that an empty child scope
cannot remove the parent's authority. Existing `nestedActions`, `scopedStages` and
`guardedHandoff` refusal/cause laws are reused rather than duplicated. Top-level
examples instantiate nested decoder suppression, joint scope and exact causes.
Premises remain finite terminating serial callbacks, accurate pure total observers,
faithful declared source directories and host dynamic-scope fidelity. These Boolean
model equalities do not license reordering potentially throwing host observers or
claim to prove continuation implementation, arbitrary codec laws, GC or timing.

The pinned [Rackcheck property executor](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/prop.rkt)
uses standard dynamic parameter scope to separate caller and test RNG ownership.
This unit follows that abstraction style through Gerbil's existing parameter-backed
checked action protocol. Portable codec source admission remains our explicit
extension, not a missing Rackcheck guarantee. Encode failure still writes no
prefix before delivery. A port failure may leave partial bytes, and a failed read
may consume input: no transactional I/O or rollback is claimed. Explicit format
identity, data budgets, lazy forcing, random schedules and all existing process,
heap, proposal and recursion limits remain unchanged. Extra observer checks retain
their cost; suppressed callbacks alone are not a wall-clock performance proof.


## Portable handoff request admission and physical framing

The audit found three actual handoff defects: an explicit `#!eof` could hide
pending input (`#!eof 99`) from the second reader call; an invalid property could
consume input and call the decoder before rejection; and a wrong-direction output
port could reconfirm a witness and invoke its encoder before failing. These are
request/framing defects, not a request for a new serialization framework.

The existing generic replay module exposes its standard record recognizer
`codec?`. Generic and typed read/write requests use Gerbil parameter contracts to
reject malformed configuration before source observers, computed POO metadata,
property callbacks or port operations. For valid configuration the existing
codec-before-domain source priority remains. No new Type wrapper, registry or
namespace is introduced, and the version-one envelope is unchanged.

After admitting the envelope, the standard reader and `peek-char` run under
separate existing source boundaries. Reader EOF must also be physical EOF before
decoding. Ordinary whitespace, comments and datum comments retain standard reader
semantics; a terminal `#!eof` at physical end remains accepted. Any pending input
after that terminator is refused. Source retirement during the reader's normal
return precedes physical probing and result interpretation; original callback
exceptions remain exact, including a false exception.

Six independent generic cases cover admission without observers, export without
reconfirmation, hidden suffixes, standard reader trivia/false witnesses, cursor-
observed source retirement and exact decoder causes/fresh retries. The independent
compiled stdlib-only suite now has 191 cases, retaining all earlier 185. Two typed
cases check computed-metadata exclusion and a heterogeneous UInt/Integer/Bool
Record with a wrapped Function. Its consuming product sampler feeds the existing
FUN property action, shrinking, portable export and import. Invalid configuration
can retry on the same untouched port; malformed framing requires explicit fresh
input. Revision retirement rejects old reports/codecs before input consumption;
fresh preparation rejects old identities before decoding and admits the corrected
service. Nested Function contracts survive reconstruction.

`PropertyReplay.admitReplayRequest` and `replayInputEnd` add eleven laws for static
admission, ordered logical/physical EOF, source retirement, exact causes, final
state forwarding and refusal before decoding. Top-level Lean examples include
hidden suffixes, stale sources and false causes. The model assumes faithful host
port observations, pure observers and terminating callbacks. It does not verify
the Scheme reader grammar, allocator, compiler or runtime. Port predicates check
direction/type only: closed ports and later device failures remain host I/O
failures. Consumed input, partial output and callback effects are not rolled back;
`peek-char` may perform underlying I/O. Existing heap/time guards remain necessary.
This continues the RFC's finite future-work protocol, not a claim that the original
paper supplies a portable handoff or host-I/O proof.


## Stable symbol and keyword identities in portable replay

A public probe exported failed witnesses containing an uninterned symbol and an
uninterned keyword. Both envelopes were accepted, but reading either created a
new identity: the same identity-sensitive property then returned true. A fresh
symbol was also accepted as codec identity, although its own written identity
could not round-trip. These are defects in the existing finite portable grammar,
not a request to serialize arbitrary Scheme objects or infer pointer identity.

The existing private copier now uses Gerbil's `interned-symbol?` and
`interned-keyword?`, whose runtime definitions explicitly exclude uninterned
tokens. One boundary serves codec identity construction, encoded payloads and
imported envelopes. Unsupported tokens keep the ordinary `nonportable replay
datum` error and original datum irritant. There is no silent conversion to an
interned spelling: two distinct application handles may have the same spelling.
No new codec format, parser, wrapper, public PBT namespace or registry is added.

A codec identity containing a fresh token refuses at construction. An encoded
payload containing one refuses before entering the write stage; witness
reconfirmation still precedes encoding as before. An imported fresh token refuses
before framing completion, decoding, domain admission or property execution.
Input may already be consumed, and ordinary I/O failures may still leave partial
output; this does not add a port transaction. Existing node/depth credits, source
checks, exception identity and Boolean false data remain unchanged.

Four independent cases cover nested identity rejection, export without output
bytes, import without decoder/domain effects, and exact identity preservation
for interned reader-sensitive spellings (including empty spellings). The existing
copy/budget cases move intact from the near-thousand-line property-scopes example
to the ordinary property-replay example module. Both standard root and isolated
build declarations share that module. No PBT interface module changes namespace;
the isolated library now requires all 212 cases.

The complex Record/Function/FUN service example keeps an uninterned application
handle in memory, shrinks a real failed service, rejects an unsafe raw-handle
codec, and retries with an explicit finite logical ID. Ordinary Type validation
checks the wire Tuple and reconstructs the Record/Function value. Source epochs
refuse old reports/codecs after handle replacement; fresh preparation can export
and replay again. Applications own this logical-ID mapping and its lifetime.

Nine finite Lean laws in PropertyReplay prove token-directory membership,
uninterned refusal, identity/payload conjunction, action suppression, exact valid
and empty admission, preserved callback causes, conditional reader/writer identity,
and preservation of a failed identity-sensitive property. Five top-level examples
instantiate fresh symbol/keyword refusal, false data, false causes and stale
refusal. Faithful finite traversal/copying, the standard interned-token round-trip
law, explicit codec laws, pure source observers and terminating sequential actions
remain premises. Reader allocation, arbitrary handles, compiler/runtime behavior
and wall-clock performance are not certified. This advances the paper's future work.

Rackcheck's pinned `gen:symbol` composes its string generator with
`string->symbol` (base.rkt lines 322-327), consistent with the existing interned
symbol generator here. Portable handoff remains this project's explicit extension;
we do not attribute our codec/source protocol to Racket. Generation, retained
shrink trees and seed splitting are unchanged.

## Shared Boolean source admission during portable replay

The audit reproduced a concrete diagnostic inconsistency: a codec currentness
observer returning the symbol `malformed` raised `stale replay codec`. The generic
and typed generator protocols already distinguish false source retirement from
malformed non-Boolean observations. This is not a request to infer hidden sources
or prove arbitrary codec callbacks: the portable boundary was coercing the same
explicit observer contract differently.

The existing `with-codec` action now calls the core `live?` operation for codec
and context observation. There is no additional wrapper, record, observer registry,
module or port implementation. The same boundary serves export reconfirmation,
encoding and writing, import reading/copying/decoding, and nested checked actions.
Codec-first ordering remains. True permits the next stage; false retains the
existing codec/context stale error; a non-Boolean reply raises the existing core
`source observer must return a boolean` Error. Observer exceptions remain exact,
including a thrown false. An action exception still bypasses its trailing check:
malformed authority discovered after a normal return cannot replace an exception
already raised by that action. A trailing refusal does not roll back effects.

Five generic regression cases cover malformed numeric/symbol/list/vector replies,
zero writes and unconsumed input on preflight refusal, false-versus-exception
identity, malformed replies after encoding/decoding, codec-before-context priority,
and nested generator refusal with dynamic-scope restoration. The isolated
standard-library package now requires 224 cases. Existing codec, corpus, source,
shrinking and replay tests remain unchanged in scope.

The existing Record/Map/Function service example uses its FUN-produced failed
report, retained shrinking and both in-memory replay paths. Malformed codec
observation refuses export without bytes and import without consuming the port.
An explicit correction permits retry on the same input; reconstructed Function
fields retain their contracts. False codec authority remains stale, and later
Type revision rejects the old report before fresh preparation. Typed facade
report/source snapshot ordering stays unchanged; this unit does not move those
observations ahead of or behind generic codec preflight.

The Lean sourceReply definition moves to the already imported PropertyReplay
module so typed preparation and portable authority share one Boolean judgment;
its name, namespace and existing laws remain. Nine new finite laws characterize
ordered codec/context admission, malformed and false replies, exact observer and
action causes, skipped actions, trailing refusal and stable publication. Five
top-level examples include a throwing skipped context, exact false causes,
post-decode malformed authority and fresh false-data recovery. Faithful host
normalization, pure terminating source observers, declared codec round-trip laws,
standard dynamic scope and finite sequential actions remain premises. No port
transaction, arbitrary callback purity, concurrency, runtime or compiler proof is
claimed. This advances the paper's future work.

The pinned Rackcheck core uses Boolean predicate contracts independently of
its map/bind combinators. We retain that separation through Gerbil's existing
module and callback contracts and the project's already shared `live?` judgment;
our revision-bound portable corpus protocol is not attributed to Racket.
Design review kept the change at the existing action owner rather than adding
validation to each reader/writer stage. Complete checks, heap limits, natural
compiler/test completion and cancellation behavior remain unchanged. No timing
improvement is claimed.

