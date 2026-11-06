# Generation control and source scope

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [Retained delayed-construction depth during dependency rebuilding](#retained-delayed-construction-depth-during-dependency-rebuilding)
- [Incoming delay allowance across suspended dependency cursors](#incoming-delay-allowance-across-suspended-dependency-cursors)
- [Compositional delay allowance through sample layers](#compositional-delay-allowance-through-sample-layers)

- [Generation and domain admission](#generation-and-domain-admission)
- [Bounded filter retry ownership](#bounded-filter-retry-ownership)
- [Transient checked-action scope](#transient-checked-action-scope)
- [Size control retains known input ownership](#size-control-retains-known-input-ownership)
- [Mandatory collection ownership under size selection](#mandatory-collection-ownership-under-size-selection)
- [Observed proposal admission before terminal publication](#observed-proposal-admission-before-terminal-publication)
- [Ancestor admission through nested domains, products and replay](#ancestor-admission-through-nested-domains-products-and-replay)
- [Strict Boolean source admission across typed composition](#strict-boolean-source-admission-across-typed-composition)

## Generation and domain admission

1. Admit `command-type`, model hooks, positive descriptor configuration and a
   finite nonnegative step cap. Create one ordinary trace sampler.
2. For each draw, call `initial`; consume the existing run-local random source.
3. Until `min(size, steps)` commands have been drawn, ask `draw` for a command
   enabled in the CURRENT reference state. The adapter chooses from enabled
   alternatives directly, rather than generating arbitrary syntax until it passes.
4. Check the command Type and Boolean `enabled?`, then use `advance` to construct
   the next reference state. A malformed/disabled draw is a generator error;
   it is never silently dropped or retried without a budget.
5. Return an owned finite trace spine. A normal `#f` from `draw` ends a valid
   prefix; it does not prove that the whole domain is exhausted.
6. Sampler admission replays the whole reference trace. A deleted producer or
   changed prerequisite cannot be hidden by accepting each command independently.

A valid empty trace checks initial-state equivalence; it does not demonstrate
command coverage. The collection example must separately assert coverage of its
required lifecycle prefix, with seeded random state-dependent suffixes.

## Bounded filter retry ownership

Rejected dynamic branches retained their leaves for final filtering but did not
pass them into later retry graphs. A later draw could revise an earlier rejected
owner and still enter a mapper/selector before stale refusal. Gerbil now reuses
the existing `with-sources observed` around every retry's generation. The quota,
size, random schedule, accepted tree, tombstones and callback exception identity
remain unchanged. Related cases are grouped in the existing examples directory;
the independent library runs 63 cases without POO, and Record/Function/FUN covers
construction refusal, explicit reprepare, shrinking and both replay paths.

`PropertyFilters.lean` uses the existing PropertyTesting namespace and composes
`guardedGeneration`, `mergeSources` and `guardedStages`. Ten laws establish stale
preflight, draw revision/causes, retained rejected and accepted history, zero quota, a retry's
single token and whole-history handoff, early acceptance, generator-entry count
bounded by local fuel, and suppression within a resumed nested pipeline. The draw
explicitly receives the inherited source list; faithful host scope is a premise.
The cost counts entries into the supplied generator, not physical draws inside
it: nested filter quotas can multiply. It proves neither observer/PRNG/runtime
implementation correctness nor callback termination, GC or wall-clock bounds.
Accurate pure observers, truthful epochs, sequential callbacks and faithful source
directories remain required. Runtime parameter unwinding and exact exception and
replay behavior have separate regression coverage. All prior checks and guards
remain enabled.

## Transient checked-action scope

The audit reproduced a replay mapper executing after its draw retired a source
from a previously rejected shrink branch. Later normal trials and generator
inspection had the same outer-action-only gap. Gerbil now installs a transient
check through the existing `with-current` form and the generator module's standard
parameter-backed `with-generation-check`. Nested draw/map/selection and iterator
boundaries observe it, including when retained source ownership is empty.

Checks run outer-to-inner and unwind through ordinary return, exceptions and the
existing refusal continuation. They never enter sample source metadata: a checker
may read its run's mutable ledger, so retaining it there would introduce recursive
observation; retaining prior replay checkers would accumulate old reports. The
actual producer/node ownership and seed/tree protocols remain unchanged. Generic
and Record/Function/FUN controls cover refusal before reconstruction, fresh retry,
original causes, nested/paused iteration and stable work across twelve replays.

`PropertyScopes.lean`, in the existing PropertyTesting namespace, composes the
existing guarded product/stages with transient source identities and the evolving
new-run ledger. Nine laws prove nested/empty admission, stale stage suppression,
cause preservation, empty/stable observation and exact new-ledger publication
without adding the transient directory. Pure accurate observers, faithful ledgers
and host dynamic scope, sequential callbacks and termination are premises. Runtime
continuations, parameter restoration, aliases, Function wrapping, heap retention
and timing are separate executable obligations, not inferred from the model.
All checks and heap/deadline budgets remain. Active scope checks add work; no
constant-time, universal performance or arbitrary-continuation claim is made.


## Size control retains known input ownership

Audit of Rackcheck's `gen:sized`, `gen:resize` and `gen:scale` confirmed the
existing size algebra. Our revision-aware extension had a distinct implementation
hole: scale delegates to a statically known input but exposed only its explicit
owner. With that input retired, both scale and its enclosing fixed product
reported current; an earlier sibling draw and scale callback each ran once before
refusal. This is not a missing Rackcheck feature or a dynamic selection boundary.

Scale now reuses the exact sized/resize run procedure and merges the known input
leaves at construction, using existing source identity sharing. There is no new
wrapper per retained sample, random draw, size schedule or shrink regeneration.
Resize, map, fixed product, finite Function tables and shrink controls preserve
these leaves. A genuinely open sized selector does not acquire unselected branches.

Four independent generic cases cover all static compositions, explicit and input
owners, normal callback revision, original exception identity, invalid natural
sizes, nested callback order, identical seeds, retained shrinking, and zero-count
inspection. The independent standard-library package now executes 71 cases.
The Record/FUN example combines scaled counts and Function fields, failure
minimization, concrete replay without regeneration, seed replay, and stale refusal
before sibling preparation. Function wrappers remain owned by Record admission.

The eight laws in `PropertySizes.lean` establish pure resize/scale algebra,
exact delegated value/seed, and guarded preflight, revision, cause and admitted
execution. Total natural transformations are the pure algebra's premise; they do
not license fusing effectful Scheme callbacks. Explicit internal resize may exceed
the outer trial size: no new blanket bound is introduced. Existing process,
heap, generation, shrinking and inspection budgets are unchanged. No termination,
host PRNG quality, GC or wall-clock speedup is proved. Existing `mergeSources`
sharing avoids another ownership mechanism. At [Size control retains known input ownership](generator-control.md#size-control-retains-known-input-ownership) construction reused the sized run
closure in a replacement generation descriptor; [Mandatory collection ownership under size selection](generator-control.md#mandatory-collection-ownership-under-size-selection) below consolidates that
metadata into the sized constructor. No timing improvement is claimed.


## Mandatory collection ownership under size selection

The next audit reproduced a cardinality-dependent hole: an element generator
whose owner was already stale could be used to construct a nonempty List producer
that still reported current. Its enclosing fixed product ran an earlier sibling
draw once and used the random source twice before refusing. A positive minimum
always uses the element; this is not the intentional independence of an unselected
branch or empty result.

`generator-sized` now accepts `sources:` through the same observer-list boundary
as `make-generator` and `make-tree-generator`. Common leaves are validated, copied
and identity-deduplicated before selection. Dynamic branches still add only their
selected leaves. `generator-scale` delegates directly to that constructor,
removing [Size control retains known input ownership](generator-control.md#size-control-retains-known-input-ownership)'s replacement generation descriptor. `generator-list` supplies element
leaves exactly when `min-length` is positive. String and Symbol inherit the same
behavior through their existing map composition. No separate carrier validators,
new generator representation, random schedule, namespace or retry system is added.

Size zero still produces the positive minimum, so it still needs those leaves.
With minimum zero, an actual empty result draws no element and acquires no element
owner. If that optional producer selects a nonempty result, its existing dynamic
selection boundary checks the selected element before drawing it. Arbitrary
unselected weighted/delayed branches, handwritten node ownership and mutable
payload aliases keep their documented boundaries.

Four generic cases cover nonempty List/String/Symbol preflight (including an
unstarted product prefix), empty selection, copied/deduplicated explicit source
lists, invalid metadata, identical seeds, retained minimum lengths and shrinking
without element redraw. The independent package runs 75 ordinary std/test cases.
A Record/FUN workflow generates bounded nonempty payloads with a wrapped Function,
shrinks both cardinality and element values, performs concrete/seed replay, refuses
stale work before preparing a sibling handler, and explicitly prepares a fresh
revision while the old sampler/report remain rejected.

Eight additional laws in `PropertySizes.lean` establish the bounded length offset,
positive-minimum participation, size-zero behavior, exact source selection,
conjunctive authority, stale preflight and preservation of an admitted result/state.
Random offsets satisfying their bound, pure accurate source observers and
terminating callbacks are premises. These are not PRNG-quality, host heap/GC,
concurrency or wall-clock proofs. Existing process and search limits are unchanged.
Source lists are captured once; runtime retains the existing flat source checks
and shrinking trees. Removing the replacement descriptor is not a timing claim.

Rackcheck's pinned [base generator implementation](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/base.rkt)
selects a length once, retains element trees and derives mapped carriers from
that list protocol. We reuse that decomposition. Positive minimums and revision
observers are our explicit extension; no cross-language random-seed parity is claimed.


## Observed proposal admission before terminal publication

The shrink-consumer audit reproduced a terminal-budget inconsistency. A returned
filtered tombstone with a newly stale leaf was charged and recorded, but the scan
skipped value classification and published `failed` when its last token ran out.
The report already had `current = false`. Inspection of the same tree correctly
returned `stale`. Handwritten trees had declared accurate node leaves; consumer
admission, not hidden callback inference, was missing.

The scan now admits newly observed leaves through the existing `with-current`
action before classifying any proposal or publishing quota exhaustion. Both live
and pruned nodes share that boundary. No new tree representation, source registry,
runner, namespace or retry policy is added. A returned proposal is charged once
before refusal; EOF and iterator exceptions still produce no proposal to charge.
Zero fuel forces no factory or iterator. Exact exhaustion still performs no EOF
lookahead and does not claim local minimality. Original observer/iterator causes
are preserved, and the in-flight proposal never replaces a confirmed witness.

Four generic cases compare checking with inspection at budgets 0/1/2, verify live
pruning and EOF accounting, strict Boolean source judgments, observer/iterator
cause identity, and several independently owned pruned proposals. The isolated
standard-library package executes 79 cases. The Record/Function/FUN workflow
covers stale evidence, identity-sharing delivery, actual mapping's earlier
refusal, fresh preparation,
retained smaller witnesses and both replay forms. Actual child mapping refuses before
returning its stale child (zero charge); identity sharing and raw delivery return
the tombstone and consume one.
This distinction is preserved rather than hidden by changing the accounting.

Nine laws added to `PropertyFilters.lean` reuse `ShrinkEvent`, `auditShrinks`,
source union and the existing shrinking engine. They establish terminal refusal,
exact cause/charge, live pruning without value admission, unchanged real values,
zero fuel, attempt bounds, preservation of a valid false witness, and refusal of
new stale leaves despite earlier live metadata. `Option.none` is the pruned tag;
`some false` remains an ordinary value. The model covers finite observed events
and accurate pure source observers. It does not prove host callback termination,
iterator/continuation implementation, PRNG quality, global minimality or GC/time.
The runtime adds the existing flat admission checks at the missing consumer
stage; no performance improvement is claimed. All resource and search limits stay.

Rackcheck's pinned [filtering tree implementation](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt)
filters lazy branches. Our already-established bounded protocol keeps charged
tombstones so filtering cannot hide work. Source refusal and terminal accounting
are our extension, not a claim that Rackcheck mandates revision observers.


## Ancestor admission through nested domains, products and replay

The scope audit reproduced late refusal across otherwise valid child protocols:
a typed product's first shrink callback ended its enclosing specification, but
the product still packed two results and invoked the second field shrink before
the outer run reported stale. The fixed control performs zero packs and zero
later shrinks. Parent sources here are explicitly declared; hidden mutation,
universal callback termination and arbitrary carrier-law discovery are not gaps.

The existing `with-current` action form now uses `with-sources` to inherit active
producer leaves and run-local checks before/after each domain action. Product
representation/value-shrink callbacks and portable codec stages reuse that same
boundary. No context objects, callback registries, runner or alternative module
interface are introduced. Existing local currentness, causes and natural budgets
remain. A valid child cannot refresh an obsolete ancestor's authority.

Execution and inspection additionally check normal child report publication
outside their local catch/finish scopes. An early local stale/error report must
unwind its own checker before the ancestor is observed; otherwise that check can
be bypassed or recursively call its own refusal. Child diagnostic reports remain
data: a live ancestor may receive a child's stale diagnostic, while an obsolete
ancestor stops the enclosing action before subsequent user effects. A thrown
action exception retains its exact cause; converting an exception into a child
report does not bypass the parent's normal-return admission.

Five independent cases cover producer-owned product measures, simultaneous
parent/child refusal in checks and inspection with balanced cleanup, reconfirm/
encode/decode refusal before later work or port writes, exact codec exceptions,
and finite fresh nesting with empty products. The independent library runs 97
standard cases. `examples/generated-products.ss` keeps typed product examples
out of the already large batch module: shared Record/Function leaves compose
through FUN, refuse before packing, preserve wrapping, and shrink/replay after
fresh preparation. Separate controls cover unpack, per-field measure and pack.
All use the existing standard TestSuite and modules; no test runner is added.

Eight additional laws in `PropertyScopes.lean` reuse `guardedThen` and
`guardedGeneration`: parent/local preflight, parent/local revision suppression,
original callback causes, exact fresh values/state, ancestor refusal on a child
report return, and parent-valid diagnostic delivery. The last boundary observes
only the ancestor; it does not re-enter the terminated child's checker. These
are serial callback laws under accurate pure observer and faithful scope-unwind
premises. They do not prove host continuations, resource cleanup, callback
termination, GC, arbitrary mutation or concurrent linearizability. Codec I/O is
still nontransactional: failures during a write may leave partial bytes.

Rackcheck's [lazy mapping/filter composition](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt)
remains the structural reference; registered source inheritance is this project's
extension. Active ancestor walks add bounded-by-context checking work; no timing
or zero-cost improvement is claimed. Process and search limits, complete checks
and current-head CI remain unchanged.

## Strict Boolean source admission across typed composition

The audit reproduced a source-judgment inconsistency: an opaque .current? hook
returning a symbol was accepted as truthy while compiling a recursive graph. A
later factory ran, and the returned graph reported current when an additional
participant masked that malformed reply. The generic core already required an
actual Boolean. The frozen public generator probe previously returned accepted /
current and recorded one later factory. This is an admission defect, not a demand
to prove callback purity, discover hidden sources or synthesize arbitrary Types.

Graph participant checks and the typed direct checker now call the EXISTING core
boolean-result primitive. The already cached bound hook in source-guard uses the
core live? operation. There is no new validator, observer wrapper, cache or module.
Every present participant is checked before conjunction can discard its reply;
empty sampler alternatives still own their observer obligations. Captured epoch
refusal precedes hooks, absent hooks remain true, false replies remain stale, and
malformed replies are errors rather than source retirement or property failures.
Original hook exceptions, including thrown false, escape unchanged. Hook purity
with respect to semantic source state and termination remain explicit premises.

Six regression cases cover malformed numeric/symbol/list/object replies before
and during later factory preparation, inhabited and empty leaves, cached guards,
epoch-first short-circuiting, explicit typed sampler failure before draw/property,
false-versus-exception distinctions and scope restoration, and unchanged source-free
seeded generation. The complex shared Record/Function service composes Tuple/List/
Pair through FUN: malformed observation stops before later construction; external
correction permits explicit preparation, decreasing shrinking and concrete/seeded
replay; malformed/false observation and later epoch retirement reject old receipts;
a corrected service passes after fresh preparation. Nested Function wrappers remain
in force. Correcting a reply never rewrites an old error report into a valid witness.

Eight PropertyPreparation laws model strict reply admission and ordered finite
observer conjunction: valid Boolean preservation, empty/missing hooks, stale epoch
priority, original causes, malformed reply refusal, false short-circuiting, true
continuation and equivalence to conjunction over the valid Boolean domain. Top-level
examples show malformed replies at either position, epoch refusal before a throwing
hook and false exceptions distinct from valid false data. Non-Boolean host values
are one explicitly rejected class; they are never cast to a catch-all Type. These
are finite protocol proofs under faithful host dispatch, accurate clocks, pure
observers and terminating callbacks, not compiler/runtime verification. An explicitly supplied prepared recipe retains its existing replayable flag;
invalid current authority still refuses actual replay. Automatic preparation
failure retains its non-replayable report. Normal observer identities, invocation
sites and PRNG schedules are retained. No elapsed-
time claim follows from a Boolean contract check; complete checks and all resource
limits remain unchanged within the RFC's finite future-work scope.



## Retained delayed-construction depth during dependency rebuilding

The audit reproduced a depth-one delayed generator whose original draw used its
only constructor credit, then forced another delayed constructor while shrinking
a parent after the original dynamic scope ended. The old tree returned candidate
zero and performed one extra construction. This evaded the explicit constructor
depth during automatic dependency regeneration, rather than asking for a global
minimum or a universal bound on handwritten callback execution.

Bind now retains the remaining delay allowance beside its existing seed/size/
source/random-checkpoint context. Only parent regeneration restores it with the
standard parameterize form, meeting it with a stricter active caller. Descendants
retain that effective allowance after the caller exits. False is unbounded; zero
is exhausted. Fresh draws still get fresh contexts, and this is a nesting-depth
bound, not a cumulative constructor-count budget for all shrink attempts.

The existing generator-delay shares the same allowance-meet primitive. A normal
unbounded bind does not acquire a parameterization frame. PRNG splitting, stored
checkpoints, proposal order, charged attempts and original source/error priority
remain unchanged. Exhaustion before a yielded proposal charges no attempt and
retains the last confirmed witness without certifying a minimum. Source refusal
still precedes quota exhaustion, and raw constructor causes remain exact.

Five independent-library cases cover exhausted/sufficient retained depth, bounded
inspection and replay, stricter consuming scopes retained across another shrink,
source/false/object-error precedence and scope unwinding, and unbounded roots.
A Record/Function/FUN service example refuses an exhausted raw witness, freshly
prepares a sufficient constructor context, shrinks, seed/concrete/corpus replays,
rejects retired report sources and explicitly prepares a corrected retry.

The focused PropertyDelay module keeps the existing PropertyTesting namespace and
reuses resolveDelayed. Laws cover optional allowance identity, commutativity,
associativity/idempotence, both finite bounds, exhausted callback suppression and
force-count bounds. Top-level examples distinguish zero, sufficient depth,
stricter retained callers and unbounded contexts. Faithful host dynamic scope,
immutable allowance capture and terminating individual callbacks are premises;
these are not PRNG-quality, arbitrary termination, byte-allocation or latency
proofs. Search/shrink limits and process/heap constraints remain unchanged.

## Incoming delay allowance across suspended dependency cursors

The next audit reproduced a separate gap on the *same* retained iterator: pull
candidate 2 without a tighter caller, then resume it in a depth-one delayed
constructor (zero remaining credits). Previously the saved standard coroutine
restored its earlier dynamic context, emitted candidate 0 and forced its delayed
constructor once. Capturing the allowance only when the child factory is created
cannot protect later pulls.

Bind now returns a private standard Iterator delegate carrying one numeric relay.
Its first pull installs the relay in the producer's dynamic scope; every pull
updates that scalar from the incoming caller before resuming the unchanged
`in-coroutine`. Effective depth meets retained, saved and incoming allowances.
Normal returns clear the relay. It captures no additional source observers,
reports or caller continuations; later pulls add no parameterization frame.
The delegate neither prefetches candidates nor moves Iterable conversion or
proposal charging to another stage. Raw exceptions retain the standard coroutine
handler lifetime: catch around the entire traversal, not merely a later pull.
Serial Iterator use remains a premise; this adds no concurrent cursor protocol.

The existing source gate still runs before exhaustion or construction. An
exhausted pull yields no candidate and charges no proposal; constructor exceptions
retain exact identity, including false. This is the existing nesting-depth bound,
not a total count budget across independent branches. Freshly prepared draws may
use their explicitly declared allowance; old trees never renew themselves.

Four independent-library regressions exercise an unbounded or bounded first
pull followed by a stricter resume, sufficient allowance and exact EOF, false/
object causes, and source refusal before exhaustion with fresh-scope recovery.
The Record/Function service example previews a dependency, refuses exhausted
resumption, then freshly prepares, checks through FUN, seed/concrete/portable
replays, rejects retired sources and explicitly retries a corrected property.

PropertyDelay formalizes resumed evaluation as the meet of retained, saved and
incoming optional limits. The flattening law and incoming/saved force bounds
prove that suspension cannot renew credits; incoming zero suppresses the
constructor. Top-level examples cover zero, one sufficient credit and a two-stage
constructor needing more. Faithful host relay transfer and terminating individual
callbacks are premises: these are not proofs of Gerbil continuations, GC, byte
allocation or wall time. The complete checks retain their existing heap/process
and search limits.

Design reflection: Rackcheck's pinned [core bind implementation](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/core.rkt#L98-L107)
composes mapped/joined shrink trees and a reproducible RNG. We retain that algebra;
explicit delayed depth and revision admission are our additional protocols.
Gerbil's standard coroutine continues to own suspension, EOF and exception
routing. A single private Iterator delegate is needed at that suspension boundary;
adding wrappers to each generator operation or replacing the coroutine would
spread the same policy across the algebra. The original prototype fixed-point
construction remains unchanged; bounded PBT construction is an engineering
extension, not an unimplemented requirement of the author's fixed-point section.

## Compositional delay allowance through sample layers

A direct bind cursor is insufficient when another sample coroutine encloses it.
The audit mapped the existing two-candidate dependency: its first pull returned
12; resuming under zero remaining caller credits returned 10 and forced the next
constructor once. The outer map restored its earlier dynamic context before the
inner bind could observe the new caller. This is a reproduced violation of our
explicit delayed-depth protocol, not a demand for unrestricted callback analysis.

The existing private numeric relay is now constructed by one `sample-iterator`
combinator. Value policies, map, bind, filter, retained products and finite Function
sample factories all use that entry before restoring a producer continuation.
Each layer transfers the incoming meet to the next, rather than relying on the
innermost bind to rediscover a lost dynamic binding. There is one delegate per
callback-bearing sample iterator, no additional per-yield wrapper or new public
protocol. Pure structural deletions invoke no user callbacks and retain the
standard coroutine directly. Child factories remain lazy, including zero-budget
checking; PRNG splitting/checkpoints and candidate order are unchanged.

Five generic regression groups cover map/filter/product/Function/value-policy
composition: zero-credit refusal without extra construction, sufficient credit
with exact order and EOF, original false/object causes, source refusal before
exhaustion, and zero-budget demand plus seed/concrete replay. First pulls occur
outside assertion handlers, and the enclosing handler spans the entire standard
coroutine lifetime. The existing Record/Function/FUN service workflow now packs
checked records inside the mapped/filtered dependency before pausing. It covers
exhaustion, explicit sufficient-depth preparation, seed/concrete/portable replay,
source retirement and a freshly prepared corrected property.

PropertyDelay models a finite path of saved optional allowances. Path append and
meet/collapse laws reduce composition to the existing single-resume protocol;
force counts stay below the incoming finite limit and zero suppresses construction.
The interpreter remains resolveDelayed. Three top-level fixtures cover exhausted,
sufficient and regrouped paths. Faithful numeric transfer at every host sample
layer, serial Iterator use and terminating individual callbacks are premises.
These are neither host-continuation/GC proofs nor cumulative force budgets over
independent shrink attempts. Existing source checks and all resource limits remain.

Design reflection: Rackcheck's pinned core bind maps and joins retained shrink
trees rather than adding a second executor. The author's fixed-point appendix
similarly separates eager and delayed construction explicitly. We retain these
compositional boundaries: move the existing numeric transfer to the common sample
constructor instead of patching each higher-level container with its own policy.
Gerbil still owns coroutine suspension, EOF, interface dispatch and exception
handler lifetime. The explicit PBT depth protocol is this project's extension;
no upstream compiler/runtime changes or original-paper completeness claim follow.
