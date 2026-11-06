# Lazy shrinking and interrupted search

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Captured fixed-width product decomposition](#captured-fixed-width-product-decomposition)

- [Checked actions and interrupted shrink receipts](#checked-actions-and-interrupted-shrink-receipts)
- [Dependency-preserving sequence shrinking](#dependency-preserving-sequence-shrinking)
- [Source-owned resumable shrink traversal](#source-owned-resumable-shrink-traversal)
- [Finite POO shrink neighborhoods captured before returning checks](#finite-poo-shrink-neighborhoods-captured-before-returning-checks)
- [Generic data-list candidate capture with contract failure precedence](#generic-data-list-candidate-capture-with-contract-failure-precedence)
- [Shared finite parameter ownership in lazy dependency shrinking](#shared-finite-parameter-ownership-in-lazy-dependency-shrinking)

- [Source-owned Iterable preparation](#source-owned-iterable-preparation)

## Checked actions and interrupted shrink receipts

The execution layer uses one private hygienic `with-current` form around domain
actions. It evaluates an action once and checks its declared sources before and
after it. Admission, strictly decreasing cost and Boolean falsity compose as
short-circuiting judgments. The search driver handles only proposal consumption
and confirmation; it no longer duplicates source checks around each callback or
passes positional progress vectors between nested loops. A single invocation-owned
Gerbil record holds the confirmed witness and counters. POO retains its existing
Record report projection and Reader/FUN report delivery.

Every returned non-EOF proposal is charged before admission, measurement, property
execution or the trailing source check. EOF and an iterator exception return no
proposal and add no attempt. A candidate is confirmed only after all judgments
and freshness checks succeed. Thus an interruption retains the previous confirmed
witness, charged attempts, accepted steps and the original exception. It reports
`error`, `stale` or the caller's explicit refusal classification, never a new
`failed` witness or a minimum. An error in a source observer while classifying an
earlier error cannot replace that original cause. Error/stale reports keep useful
progress but cannot authorize concrete counterexample replay.

This follows the existing FUN/IO style of composing owned actions and the Racket
libraries' separation of lazy shrink trees from property execution. It does not
copy Rackcheck's `pass?` exception-to-falsified policy: our RFC keeps host errors
separate from Boolean false. Gerbil's existing Iterator/in-coroutine protocol
remains the lazy representation. No new stream framework, scheduler, namespace or
POO dependency is added to the generic library. Filtering is not allowed to hide
proposal consumption or introduce unbounded search between budgeted attempts.

The independent example interrupts child creation, iteration, admission,
measurement, properties and observers after a confirmed reduction. It checks
cause identity, original/reduced values, counters, seeded replay and stale replay
refusal. The typed Record example delivers the same receipt once through FUN.
Lean's finite `auditShrinks` distinguishes failed returned proposals from iterator
exceptions. `auditShrinks_budget`, `interrupted_shrink_preserves` and
`callback_error_retains` reuse the established shrink laws to prove accounting,
retained validity/falsity and exclusion of the pending failed proposal. Runtime
callback termination, source-observer accuracy and PRNG behavior remain premises.

## Dependency-preserving sequence shrinking

Reuse the existing runner's admission/descent/falsity/budget loop. Add only trace
candidate construction:

1. Propose deleting one command, and reuse existing coordinate shrinking for
   parameter replacements supplied by `model.shrink`.
2. Replay each proposed sequence from a fresh reference state. Retain a command
   only when it is typed and enabled at its new prefix. Omit commands whose
   producers/prerequisites were removed, then continue replaying the suffix.
3. Never rename a logical handle to another surviving handle, invent a producer,
   regenerate a random suffix or silently turn an expected refusal into success.
   Prescribed reply labels are part of collection commands and their preconditions.
4. Replay/admit the resulting whole trace again before running the actual system.
5. Use `length(trace) + sum(command-measure)` as the natural measure. A parameter
   replacement must reduce the whole measure; deletion plus dependent retirement
   cannot increase it. The existing runner retains only valid, strictly smaller
   traces that still falsify the differential property.

This is semantic dependency retirement, not text deletion or an inferred global
minimal sequence. An independent command survives removal of unrelated producers.
Deleting a producer can retire several dependent consumers; later commands that
remain enabled are preserved in order. A retired mismatch that no longer fails is
rejected by the existing falsity check, retaining the previous valid witness.

The first implementation may replay each candidate in O(n) reference steps and
propose O(n) single deletions, plus finite parameter candidates. It must charge
these costs; the shrink attempt budget does not prove callback execution time,
byte allocation or globally minimal counterexamples. No hidden unbounded search
or replacement scheduler is introduced.

## Source-owned resumable shrink traversal

Audit finding: standard value shrink factories checked their source leaves only
when a coroutine first started. A paused iterator could resume producer effects
after its source changed. Combinators could detect stale results after that extra
pull, while dependent bind reconstruction could omit the originally selected
child's source leaves on a separately retained smaller node. Negative controls
reproduced an unchecked next value, an extra producer effect and a descendant
that incorrectly reported its old origin as current.

One private `for-sources` form now composes the existing `with-sources` boundary
with Gerbil's ordinary Iterator protocol. It guards factory evaluation and every
`next!`, including EOF. Value generation, mapping, bind, filtering, sequence
coordinates and finite-function tables use the same form. No new public DSL,
iterator implementation, coroutine framework, scheduler or source registry is
added. If both owned and inherited source lists are empty, the form lowers to the
standard `for` loop directly; a currently true observer never qualifies for that
fast path merely because of its current truth value.

Bind nodes merge original/parent/selected-child leaves before admission and pass
that flat ownership to parent regeneration and child shrinking. Mapped descendants
retain the enclosing observed leaves. Retained subtrees cannot drop old authority
by selecting a fresh branch, including when lifted through the ordinary typed
`from-generator` bridge into a separate FUN run. Fresh invocation may capture a
new epoch; old retained nodes and old replay remain refused. Unvisited alternative
branches are not scanned or added. Advanced handwritten sample producers still
must declare accurate source leaves on their own nodes.

Regressions cover paused primitive and map/filter/bind/sequence/function traversal,
original iterator causes after source mutation, historical bind ownership and
fresh invocation. The Record/Function/FUN example retains a smaller dependent
subtree, rejects it after the original branch changes, then regenerates, shrinks
and replays under the new epoch. Existing seed checkpoints, parent-before-child
order, zero-fuel behavior, EOF checks, proposal accounting and corpus tests remain
in the full workflow. Independent generic acceptance stays at 55 kernel cases;
additional public workflow and typed cases run under the standard suite.

Lean reuses source unions and guarded callback transitions. Eight laws establish
rebuilt membership/currentness/stale refusal and per-pull preflight, EOF refusal,
exact exception/value preservation and the source-empty fast path. Accurate pure
observers, faithful host callback interpretation and termination remain premises.
This is sequential resume admission, not concurrent linearizability, coroutine
runtime verification or arbitrary closure dependency inference.

Guarded pulls add before/after source walks and reuse the existing inherited
context-sharing fast path. Source identity deduplication retains all distinct
captured epochs, never deduplicating by Boolean truth. Origin lists may grow with
visited reconstruction ancestry; this is not an O(1) source-check or host-heap
bound. Source-free data keep the standard loop; no wall-clock improvement is
claimed. Proposal budgets count returned composed proposals; an interrupted pull
that returns no proposal cannot certify a minimum. Existing heap/deadline guards
still bound arbitrary callback work.

[Rackcheck bind](https://docs.racket-lang.org/rackcheck/index.html) provides the
parent-first lazy tree comparison. Original child seeds and regeneration order
are unchanged; source ownership is our additional explicit protocol.

## Finite POO shrink neighborhoods captured before returning checks

The audit followed finite proposal ownership beyond [Fixed product row and finite expansion ownership](data-generation.md#fixed-product-row-and-finite-expansion-ownership) product rows. A raw UInt
sampler returned `(0)`; a returning inherited observer rewrote that spine to `(1)`
before sampler-children copied it. The reproduced child was `candidate=(1)`.
Products had the same checked-call/copy order, and recursive leaf shrinking had
an independent return path. This changes the actual proposed witness rather than
merely diagnostics, and is a concrete finite-POO-protocol gap.

The existing sampler-children operation now owns invocation, shallow capture and
final admission together. Its local capture action remembers a proper row as a
copy and malformed shape as false. It runs inside the caller's existing checked
action; only after that action's original source/current checks succeed does
false become the existing finite-proper-list error. Thus stale/observer causes
retain priority even for malformed output, original shrinker exceptions still
bypass trailing checks unchanged, and valid empty rows/false payloads are data.
There is one copy for each immediate finite neighborhood, without a second walk
or wrapper record after the returning observer.

Raw bridges use the same default inherited source action. Products supply their
already existing checked action, so current checks, pack ordering and later-child
suppression stay with the product owner. Recursive construction receives the
same finite admission operation as its other supplied scalar capabilities; its
old redundant continuation list validation is removed. This changes an internal
constructor capability, not the public typed generator API. Search, structural,
candidate and strict-rank accounting remain unchanged. No recursive child tree
is traversed eagerly. The independent generic Iterator API and data-list-shrinks
callback contract are not claimed by this finite POO unit; the latter's separate
return-ownership audit remains future acceptance work, not a proved design law.

Four regressions cover bridge/product/recursive paths, replaced/improper/cyclic
post-return spines, empty and malformed neighborhoods, exact false/object causes,
malformed-output stale and observer-exception precedence, and suppression of
packing/later child effects after source retirement. The existing generated-products
suite adds a complete Record/Function service via property-action: the returning
observer substitutes a different service witness but the original zero witness
is retained; real shrinking, Function validation, concrete replay, seed replay
after explicit callback-data repair, old-owner refusal and fresh corrected retry
all use the ordinary runner and FUN. Mutable closure data remains the caller's
source obligation. No new framework, namespace, module registration or cache is
introduced, and the independent standard-library kernel retains all 231 cases.

Seven finite PropertyProducts laws model normalized shape/topology capture before
returning observation while deferring shape errors until the existing guard has
completed. They prove malformed refusal under fresh normal observation, stale
preflight and retirement priority, exact observer causes, original ordered row,
snapshot equivalence and suppression of a dependent consumer on refusal. Five
top-level examples distinguish post-return replacement, malformed/observer-error
priority, retirement, false causes and an empty neighborhood. Host list recognition,
shallow-copy fidelity, accurate source observations and terminating sequential
callbacks remain premises. This is not a deep payload snapshot, callback termination,
concurrent mutation or compiler/runtime proof, nor a performance/GC/RSS claim.

The author's ordered composition and Rackcheck retained-child direction remain
the design reference: keep proposal ownership at one callback owner and reuse the
existing lazy tree, checked packer and replay algebra. Record, FUN and standard
Gerbil list-copy do the concrete work. Complete checks, 2 GiB main/1 GiB isolated
limits and process cancellation are unchanged, as is authorized natural compiler
and test completion. These are finite future-work constructions.

## Generic data-list candidate capture with contract failure precedence

[Finite POO shrink neighborhoods captured before returning checks](shrinking.md#finite-poo-shrink-neighborhoods-captured-before-returning-checks)'s remaining generic finite-list audit reproduced `candidates=((1))` after a
callback returned `(0)` and a returning observer rewrote that spine. The common
data-list-shrinks policy validated the row only after with-sources returned. This
affected coordinate replacement before later coordinates or model repair; input
snapshot ownership alone did not own each returned finite neighborhood.

The same coordinate action now captures a proper returned list with Gerbil
list-copy. For malformed output it uses the original using/proper-list? contract
under with-catch to retain the actual standard exception without raising it yet.
Standard multiple values carry the owned row or stored refusal through the SAME
with-sources action. Only after its returning source checks does the caller raise
the stored contract exception or reconstruct candidates with the existing map.
There is no new record, wrapper, registry, public API or namespace. The input
parameter is named items so it does not shadow Scheme's values primitive.

This preserves stale and observer-exception priority over malformed output. Raw
shrinker exceptions, including false, occur outside the contract-only catch and
retain their original cause without a trailing check replacing it. A post-return
repair of malformed caller data cannot repair its captured admission; replacement,
improper and cyclic edits of a previously proper spine cannot retarget proposals.
Order, multiplicity and payload identity remain, including false payloads and a
legal empty neighborhood. Only spines are owned, never arbitrary mutable payloads,
callback state or external effects.

Four standard-library cases cover those edits, full prefix/suffix substitution,
shared payload identity, stored standard contract errors after observer repair,
source retirement, body/observer false and object causes, and exact later-coordinate
suppression. A genuinely infinite generic Iterator is checked at budgets 0, 1 and
3: only the requested proposals are pulled, the factory remains unused at zero,
and rejected nondecreasing candidates still spend the original counter. Generic
Iterator APIs, list-deletions laziness, structural ordering, rank admission and the
runner's budget/restart machinery are unchanged. data-list-shrinks retains its
existing finite/eager immediate-neighborhood contract; this change does not make
an arbitrary Iterator admissible as a finite coordinate result. Independent
standard-library acceptance increases from 231 to 235 cases, without POO imports.

The existing generated-products TestSuite adds a complete Record/Function batch
via FUN property-action. Structural deletions and data-list coordinate shrinking
reduce a failing two-service batch to the originally returned zero service despite
a returning observer substituting a different service. Function validation,
concrete replay, seed replay after explicit closure-data repair, old-owner refusal
and fresh corrected retry all reuse existing protocols. No second test runner or
module inventory is added.

Seven PropertyProducts laws compose the existing observeFiniteChildren boundary
with ordered prefix/value/suffix reconstruction. They prove refusal suppression,
exact retained row mapping, one result per captured occurrence, complete candidate
width, snapshot equivalence, original cause precedence and an empty neighborhood.
Five top-level examples distinguish retargeting, malformed/observer priority,
retirement, false duplicates and empty output. The normalized invalid cause denotes
the stored standard contract exception; its constructor/backtrace implementation
is not verified. Host shape recognition, faithful shallow copying, accurate source
observers and terminating sequential callbacks remain premises. Candidate-count
laws are not a GC/RSS or latency bound, callback termination proof, concurrent
mutation proof or Gerbil/Gambit/compiler verification. This continues the paper's
finite future-work construction.

The author/Racket composition reference is retained: own finite data at its one
producer boundary, then use existing map, model repair and retained tree algebra.
Gerbil using, with-catch, values/let-values and list-copy implement that boundary;
Record and FUN serve the downstream example. Complete checks, 2 GiB main/1 GiB
isolated guards and cancellation remain unchanged, with authorized natural
compiler and test completion. No performance improvement is claimed.

## Shared finite parameter ownership in lazy dependency shrinking

The audit traced draw/repair/seed replay through the existing model generator.
[Generic data-list candidate capture with contract failure precedence](shrinking.md#generic-data-list-candidate-capture-with-contract-failure-precedence) fixed the eager list policy, but trace-command still copied its returned
parameter list after a returning checked observer. The minimal baseline produced
`trace-neighborhood=(() (1))` from the declared `(0)` parameter. A typed dependent
Record/Function probe retained open/use dependencies but incorrectly minimized its
use amount to 1 instead of 0. These are supported lazy-trace parameter boundaries,
not unrestricted dependency inference or a new replay authority.

The [Generic data-list candidate capture with contract failure precedence](shrinking.md#generic-data-list-candidate-capture-with-contract-failure-precedence) finite admission implementation is now one named generator-module
operation, finite-shrink-children. data-list-shrinks and the model's demanded
trace-command factory call that SAME owner. It preserves one shallow copy per
finite parameter row, original using exceptions, standard multiple values and
source/observer-cause priority. The duplicated lazy-side validation/copy is removed.
This is an ordinary function in the existing module, imported with only-in;
there is no new namespace, module registry, framework or callback record.

The operation still runs only when the existing sequence requests that parameter
neighborhood. Structural proposals precede parameters, repair occurs once per
requested returned trace, and unvisited parameters/repairs stay unvisited. Failed
parameter acquisition has not returned a proposal; previously yielded structural
proposals keep their charges. The runner's domain, strict rank, restart, source
and attempt-budget owners are unchanged. Generic arbitrary Iterator callbacks are
not routed through this explicitly finite boundary. Empty rows, false commands,
ordered duplicates and shared payload identities remain data; mutable command
fields and undeclared callback effects remain caller obligations.

Four independent standard-library cases cover replaced/improper/cyclic caller
spines after first return, false command duplicates, stored contract refusal after
observer repair, preservation of structural progress before malformed refusal,
raw/observer false and object causes, source retirement and exact charges before
parameter failure. Budgets 0/1/2 distinguish no parameter demand, structural-only
demand and one accepted parameter, with exact factory/attempt counts. [Generic data-list candidate capture with contract failure precedence](shrinking.md#generic-data-list-candidate-capture-with-contract-failure-precedence)'s
infinite-Iterator budget controls remain intact. Isolated acceptance increases
from 235 to 239 cases, still without POO imports or another test entrypoint.

The existing generated-traces suite adds a complete open/use service with shared
handle keys, Record command fields and Function wrapping. Its faulty system lives
inside the existing scoped differential fixture. Returning observers substitute a
use amount of 1, while the captured original amount 0 is repaired and accepted as
a strictly smaller failing trace. The open/use dependency survives; Function input
checks, concrete/seed replay, old-owner rejection, fresh corrected retry and equal
fixture open/close counts all use trace-generator, trace-property and FUN.

Eight finite PropertyTraces laws compose observeFiniteChildren with demand and
ordered prefix repair: zero demand suppresses this stage, capture refusal skips
repair, retained rows keep order, completed prefix repair is budget-bounded, pure
repair commutes with prefix selection, malformed errors retain their source gate,
original causes keep priority, and retirement suppresses publication. Five top-level
examples cover zero demand, a retargeted spelling, false causes, retirement and
false duplicates. Existing repairedTracePrefix laws continue to describe actual
finite model repair. The new normalized-return model assumes faithful host list
recognition/copying, pure repair and accurate sequential source observations;
primitive exception construction, arbitrary callback termination, mutable payload
freezing, concurrent mutation and Gerbil/Gambit/compiler verification are outside
its claim. This advances the paper's finite future work, not a latency/GC/RSS proof.

The author's ordered composition and the Racket retained-tree comparison guide
one producer boundary followed by existing sequence/repair/replay operations.
Gerbil using, with-catch, values and list-copy implement it; Record and FUN express
the typed application. Complete checks, 2 GiB main/1 GiB isolated limits and
cancellation remain, with the already authorized natural compiler/test completion.
No full benchmark artifact, versioned JSON or upstream change is introduced.


## Source-owned Iterable preparation

Gerbil's standard `iter` may invoke an application's `Iterable.iter` method.
Child creation and iterator preparation are therefore distinct user actions.
The audit reproduced `status=stale opens=1 nested-effects=1 attempts=0`: conversion
retired the source and then ran a nested generator before the next pull noticed
retirement. The stale final verdict did not undo that already executed effect.

Execution, bounded inspection and the generator algebra now put standard `iter`
inside their existing `with-current` or `with-sources` action scope. The child
factory remains a separate checked action before conversion. This preserves the
old factory-return refusal: moving both operations into one unchecked callback
would let an obsolete factory enter `Iterable.iter`. No alternate Iterator,
conversion API, stream framework, namespace or scheduler is introduced.

The standard Iterator returned by conversion is unchanged. Preparation itself is
not a proposal: zero budget still skips child creation/conversion, and conversion
failure consumes no attempt. Successful `next!` results keep the existing charge
before post-checks; EOF and throws keep their original accounting. Factory and
conversion exceptions retain exact causes, including a thrown false. A failed
conversion cannot replace the last confirmed witness or authorize replay of a
stale/error report. Empty iterators remain valid and can establish exhausted
neighborhoods when EOF is actually requested.

Four independent-library cases cover execution, bounded inspection, direct map/
bind/product child traversal and factory/conversion/EOF/error priorities. They
use a small application Iterable implemented through Gerbil's official interface.
The standalone library now requires 243 cases, still without POO imports. The
Record/FUN collection example retains the real indexed-table trace tree, retires
its owner during conversion, proves zero forbidden nested effects, then freshly
prepares a genuine atomicity fault. Dependency-repaired shrinking, concrete/seed/
portable replay, later owner retirement and corrected fresh retry use the existing
collection model, samplers and scoped fixtures.

`prepareShrinkIterator` reuses `guardedThen` in PropertyPreparation. Eight laws
cover stale preflight, factory retirement/cause, exact handoff, conversion
retirement/cause, exact cursor delivery and suppression of pull/accounting
continuations on refusal. Five top-level examples include empty cursors, thrown
false and inherited-parent refusal; existing `nestedActions` laws supply the
parent/child authority relation. Host dynamic-scope/interface fidelity, accurate
source predicates and terminating serial callbacks remain premises. These laws
do not prove arbitrary callback termination, thread scheduling, GC or latency.

This extends the established lazy-tree and application-owned action design.
Gerbil's `std/iter/iterators.ss` owns dispatch and `std/iter/interface.ss` owns
Iterable/Iterator; POO only retains its source and failure protocol around them.
The additional admission occurs once per conversion, without another draw,
proposal lookahead, cache or witness wrapper. Whole-workflow speedup is not claimed.
Main 2 GiB and isolated 1 GiB bounds, cancellation and complete standard checks
remain; natural compiler/test completion follows the existing authorized policy.


## Captured fixed-width product decomposition

The typed product audit reproduced a weight of 300 instead of 13: an unpacker
returned staging `(4 9)`, then a returning source observer changed it to
`(100 200)` before the product copied the row. The same gap could retarget
value-only coordinate shrinking or repair an originally malformed/wrong-width row.

The existing `unpack-row` now recognizes width and copies the finite spine inside
its existing checked action. Only after returning source checks does it raise the
ordinary invalid-product-row error. Both measurement and coordinate shrinking use
that one boundary. No new wrapper, namespace, cache or core protocol is introduced.
Raw unpack exceptions keep their cause; observer errors/retirement outrank stored
shape refusal. Payloads remain shared under their declared source laws.

Seven `observeProductRow` laws in `PropertyProducts` compose `captureProductRow`
and `observeFiniteChildren`: exact retained row, immutable snapshot equivalence,
wrong-width refusal, consumer suppression, retirement, original observer cause and
stale refusal. Five top-level examples distinguish staging edits, later shape
repair, retirement, false causes and zero-field data. The model starts after a raw
unpacker returns; its original exceptions are handled by the existing guarded
callback laws. Faithful host copying/width recognition, truthful sources and
terminating sequential callbacks remain premises, not runtime/compiler proofs.

Regression tests cover measure/shrink under replacement, improper and cyclic
staging edits, malformed/wrong-width repairs and exact false/object causes. A
Record/Function/FUN workflow forces the value-only path, shrinks to `(0 0)`,
exports/imports its witness, replays seed/concrete evidence, refuses retirement and
performs a fresh corrected retry. Complete checks and resource bounds remain.
