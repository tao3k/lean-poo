# Data generation and retained products

[Design index](../pbt-design-rfc.md)

These sections preserve their recorded implementation and acceptance history.
Case counts and commit identities belong to the named revision; current CI must
be checked separately. The finite laws retain their stated runtime premises.

On this page:

- [P13: declared finite enumeration simplification](#p13-declared-finite-enumeration-simplification)
- [P18: independent product retention](#p18-independent-product-retention)
- [P21: shared typed-product observation](#p21-shared-typed-product-observation)
- [P22: fixed-product source admission](#p22-fixed-product-source-admission)
- [P28: exact bounded model draw configuration](#p28-exact-bounded-model-draw-configuration)
- [P29: finite sequence preparation without prefix salvage](#p29-finite-sequence-preparation-without-prefix-salvage)
- [P47: automatic exact integer carrier profiles](#p47-automatic-exact-integer-carrier-profiles)
- [P48: one spelling protocol for text carriers and keyword call values](#p48-one-spelling-protocol-for-text-carriers-and-keyword-call-values)
- [P55: owned finite sequence preparation](#p55-owned-finite-sequence-preparation)
- [P57: fixed product row and finite expansion ownership](#p57-fixed-product-row-and-finite-expansion-ownership)

## P13: declared finite enumeration simplification

Finite Enum values previously had no shrink candidates and zero measure. A
nested collection could reduce its shape but could not simplify an Enum field.
`generator-elements choices` now maps the existing integer shrink tree through a
captured vector of declared values. It requires a nonempty proper list, draws one
index regardless of size, and never redraws while shrinking. Equal payloads retain
their distinct position preimages. Mutable payloads remain caller-owned; only the
list spine is detached. Existing observer ownership and exact error causes apply.

The POO scalar bridge reuses Enum's existing `.uint<-` and `.<-uint` metadata.
The first equal declaration position is the natural measure. Value-only shrinking
maps smaller indices through the same descriptor; generic tree shrinking retains
its original index preimages. A duplicate proposal with equal canonical rank is
charged and refused by the existing strict-descent gate. Empty Enum remains an
uninhabited leaf and does not invalidate an otherwise inhabited Union. Declaration
order is an explicit simplification policy, not an inferred semantic ordering.

Regression acceptance covers false payloads, equal duplicates, detached spines,
no redraws, stale retained descendants, original callback causes, minimum failing
ranks, concrete/seed replay and a nested List/Tuple/Enum FUN workflow. Changes to
the role descriptor reject old reports. Independent generic acceptance now runs
48 cases. No equality implementation, RNG, shrink runner or namespace is added.

Lean proves selected values belong to the finite domain, out-of-range selection
refuses, first-occurrence rank is no larger than the selected index, and earlier
positions strictly lower canonical rank even with duplicates. Host equality/hash
agreement, stable payloads, truthful observers and terminating callbacks remain
premises. Index generation does not prove PRNG distribution or wall-clock costs.
Preparation copies N positions; each draw selects one index; shrink work and
source checks retain the existing lazy tree and budget costs.

[Rackcheck's finite-choice generator](https://docs.racket-lang.org/rackcheck/index.html)
also supplies shrinking. Its removal-of-previous-choices policy differs from our
explicit declaration-order policy; byte-for-byte tree parity is not claimed.

## P18: independent product retention

Gerbil's independent product implementation used dependent bind during shrinking,
redrawing a suffix after an earlier coordinate changed. A stateful draw control
reproduced `(2 1)` shrinking to `(0 2)`. The implementation now captures original
roots with the unchanged seed schedule and reuses the existing `sample-sequence`
policy at fixed width. Lists and finite-key hashes share root capture directly;
finite Function tables retain unaffected result rows. Explicit dependent bind is
unchanged. Rackcheck's tuple examples and separate bind contract motivate this
distinction; the revision protocol remains project-specific.

`retainedProductStep` and eight laws in `PropertyGenerators.lean` prove width,
selected and sibling preimages, map commutation, independent update commutation,
unchanged external draw state, empty products and sum-measure strict descent.
Scheme controls check twelve seed schedules, draw counts, repeated traversal,
retained source refusal and downstream Record/Function/FUN/replay composition.
They do not prove host callbacks, PRNG quality, physical sharing, allocation or GC.
Each coordinate still packs the full product and checks declared sources; removal
of suffix regeneration is not a constant-time or universal speedup claim.

## P21: shared typed-product observation

Typed product measures duplicated the generic product fold and could invoke a
later field after an earlier source revision. Value-only shrinking could likewise
continue to pack/later children, and an uncopied child directory could diverge
from the already captured draw tree. Gerbil now captures child topology once,
reuses the generic product specification and checked specification-weight, and
shares that currentness with unpack, raw shrinking and retained-tree packing.
A common owner also protects zero-field products; obsolete products cannot acquire
fresh epochs just by opening another core view. Actual payloads remain caller-owned.

`PropertyProducts.lean` uses the existing PropertyTesting namespace and guarded
stages, with eight laws for preflight/field refusal, exact causes, empty ownership,
packing refusal, stable field order and the original natural sum. Regressions and
Record/Function/FUN examples cover directory edits, parent/child revisions, explicit
preparation retry, retained wrappers and both replay paths. The source inventory
and example shard admission include the new module without dropping older checks.

Epoch accuracy, sequential observation, faithful capture and pack/unpack laws are
premises. Host copying, arbitrary aliases, callbacks, concurrency, allocation and
GC are not certified. Joint source walks can remain quadratic in field count;
there is no constant-time or universal performance claim.

## P22: fixed-product source admission

The generic fixed product knew every field but hid its producer leaves until
selected bind stages ran. A stale later field could leave `generator-current?`
true and permit an earlier draw or mapper before refusal. Gerbil now flattens
known field sources with standard `append-map` once, normalizes them with the
existing identity observer boundary, and forwards them through fixed products and
nonempty finite Function result tables. It shares the original bind/map run
procedure, seed schedule, lazy children and typed bridge. Dynamic unselected
branches and empty result domains do not gain unrelated ownership.

Six laws added to `PropertyProducts.lean` prove complete-field conjunction,
preflight suppression from any stale leaf, nested/shared-source equivalence and
empty independence. The existing stable-order/sum laws still apply to the same
guarded evaluator. Topology fidelity, stable identities, pure Boolean observers,
truthful epochs, sequential callbacks and termination are premises. Host observer
exceptions and copying are runtime regressions; they are not inferred from this
finite model. No PRNG, GC, concurrency or wall-time theorem is claimed.

The companion independent suite and Record/Function/FUN workflow cover pre-draw
refusal, exact causes, explicit retry, preserved wrappers, shrinking and both
replays. All checks and resource bounds remain required. Known-source checking
adds necessary observer work; this correctness unit makes no speedup claim.

## P28: exact bounded model draw configuration

The generic trace draw accepted non-natural steps and size directly as iterator
bounds. Before repair, steps `-1` and `1/2` each generated a command and invoked
initialization instead of refusing. Gerbil's standard range iterator intentionally
supports reverse and fractional ranges; it cannot supply this protocol's natural
step contract. Infinite bounds could also bypass the promised finite quota. This
is an implementation admission gap, not unrestricted callback termination.

`draw-trace` now uses Gerbil's existing parameter contracts for model identity,
draw/random procedures and exact natural limits. A shared private `trace-limit?`
serves both dimensions. Invalid configuration refuses before model initialization
or command callbacks. The same for/fold owns state and command order, the original
size is passed unchanged, and at most `min(steps,size)` draws may succeed. No
coercion, fallback limit, new framework, namespace, scheduler or PRNG owner is added.
A valid zero cap retains initialization once, including its original exceptions,
then performs no draw; this preserves the existing model initialization semantics.
Explicit stop still omits its unused payload. Disabled/invalid commands and
non-Boolean continuation judgments remain errors, never silently dropped inputs.

Four generic cases cover negative, fractional, inexact, NaN/infinite and malformed
limits in both dimensions; callable/model admission before effects; exact caps,
large natural limits capped by a small size, original callback size/state order,
false command payloads, early stop and exact initializer/draw causes. The independent
standard-library suite now executes 83 cases. A typed Record command with a wrapped
Function exercises state-dependent open/use generation, invalid size-policy refusal
before initialization, zero command cap, FUN differential fixture cleanup,
dependency-preserving minimization and both replay forms. The same action can retry
with a valid configuration; generation and concrete replay keep their distinct costs.

Nine laws in `PropertyTraces.lean` stage validated limits and initialization over
the existing `drawTrace` engine: invalid admission, original initializer cause,
zero steps/size, unchanged-size delegation, explicit stop, disabled command refusal,
valid prefixes bounded by both limits, and exact enabled payload delivery. The
existing remaining-fuel argument remains a finite observation index, allowing
different random choices at an unchanged logical state while size stays fixed. An
absent validated configuration models refusal; accepted limits are Nat values.
Runtime contract fidelity, normalized/faithful choices and callback termination
remain premises. These laws do not prove Gerbil contracts/compiler/iterators,
PRNG quality, arbitrary callback termination, host GC or wall-clock speedups.
The typed steps ceiling and all process, heap and search limits remain unchanged.

Rackcheck's pinned [generator contract](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/core.rkt)
requires an exact nonnegative generation size. We retain that contract discipline
using Gerbil mechanisms; this project's finite model-trace API is an extension,
not a claim that Rackcheck implements the same state-machine protocol.


## P29: finite sequence preparation without prefix salvage

The audit reproduced two silent truncations. `valid-trace?` rejected a dotted
command spine while `repair-trace` initialized the model and returned its apparent
proper prefix. A parameter shrinker returning `(0 . bad)` likewise contributed a
candidate instead of refusing. A third control revised a declared source in the
first parameter callback: preparation still invoked the second callback before
the enclosing action eventually returned stale. These are observable preparation
defects, not inference of hidden dependencies or arbitrary callback termination.

The existing finite sequence policy now owns one spine boundary. `list-deletions`
uses Gerbil's standard `using`/`list?` contract before length/copy/traversal.
`data-list-shrinks` obtains structural proposals through that boundary once, then
uses the existing `with-sources` around each parameter callback and admits its
returned proper list with `using`. Model shrinking delegates to the same policy;
it adds no second input-spine check. Independent repair validates its own finite
input before folding. Model identity and callback procedure contracts stay with
Gerbil. Valid structural/coordinate ordering and callback invocation counts stay.
No partial candidate batch is delivered when preparation fails; already performed
host effects are not rolled back.

Only finite outer spines are constrained. Invalid trace predicates still return
false, and complete checking refuses before fixture entry. Proper inputs still
retire invalid/disabled commands according to the existing model policy, preserving
false command payloads and dependencies. Cyclic payload graphs are not deep-
traversed by a spine check. General lazy sample shrinkers still accept Iterators,
including infinite neighborhoods consumed under the unchanged proposal budget.
A cyclic cdr chain is malformed list data, not such an Iterator. No global eager
list conversion, compatibility layer, namespace or new shrinking engine is added.

Four generic cases cover improper, cyclic and non-list spines; no initialization
or prefix effects on refusal; malformed callback outputs; exact causes and charges;
source revision before the next coordinate; unchanged finite proposal order; and
bounded lazy Iterator admission. The independent package runs 87 standard cases.
`examples/generated-traces.ss` keeps new typed evidence separate from the large
batch module: Record commands with Function fields reject malformed parameter
batches before candidate repair, retain diagnostic witnesses with zero delivered
attempts, and replay/retry explicitly. A single codec-parametric Record/FUN fixture
covers String/Symbol/Bytes, rejects improper/cyclic outputs, interrupts shared-source
revision before the next parameter, preserves wrapping, and retries/replays valid
shrinking. Typed packing starts only after the complete finite policy returns.

Nine laws in `PropertySequences.lean` reuse the existing source-checked callback,
Except bind and dependency retirement: malformed input refusal, exact proper-input
forwarding, stale preflight, normal revision, original callback cause, malformed
result refusal, ordered proper-result delivery, suppression of later stages, and
valid order-preserving dependency repair. The host shape conversion represents
malformed spines by none; proper empty/false-containing lists remain present data.
Accurate source observers, faithful normalization and terminating callbacks remain
premises. This does not prove Gerbil contracts/list?, arbitrary payload graphs,
callback termination, host GC or wall-clock behavior. All guards and checks stay.
Shape checks add finite spine walks, and each parameter action walks its active
source ledger; no zero-cost or timing improvement is claimed. Existing identity
sharing avoids introducing a separate source wrapper per data carrier.

Rackcheck's pinned [shrink-tree contract](https://github.com/Bogdanp/rackcheck/blob/ffbddb7a9edef6ce1d9e0930adae1bd7033f1db7/rackcheck-lib/gen/shrink-tree.rkt)
requires stream-shaped general shrink results. We preserve that lazy-protocol
separation using Gerbil Iterators while enforcing the narrower proper-list
contract of this project's finite value policy. Revision checks remain our extension.

## P47: automatic exact integer carrier profiles

The concentrated audit reproduced a missing derivation path for existing
`IntegerRange`, `UIntN`, `IntN` and `Z/` descriptors. They required handwritten
`.generator` fields despite exposing exact interval metadata. They now share one
POO-free `generator-integer-range` combinator and one typed preparation path;
custom overrides and Exactly/Enum retain precedence. No additional framework,
namespace, validator chain or upstream change is involved.

The nearest-to-zero admitted integer is the anchor. Size bounds the draw's
distance from that anchor; finite endpoints clip the inclusive window. A primitive
draw has at most `2*size+1` choices, even for a 256-bit carrier. Size zero produces
the anchor, including positive-only and negative-only intervals. Shrinking maps
existing natural-distance candidates back along the original closed segment;
every candidate remains admitted and strictly decreases distance. No rejection
sampling, modulo coercion or Any fallback is used. This follows the compositional
integer/shrink-tree approach of [Rackcheck](https://docs.racket-lang.org/rackcheck/index.html),
while retaining this project's explicit size and source-ownership protocols.

IntegerRange admits omitted endpoints; fixed-width/modular descriptors require
exact finite endpoints. Malformed metadata is a preparation error. Empty finite
intervals, including `Z/ 0`, reuse Enum's uninhabited-leaf exhaustion protocol.
The recursive graph's original source scope checks each bound getter before the
next one; retained samples, diagnostics and reports reject retired ownership.
Only fresh preparation sees changed endpoints. Custom predicates must faithfully
admit their interval or supply an explicit generator. Float/Real/Number remain
outside this exact profile; their absence is not silently repaired.

`examples/property-numbers.ss` exercises the generic combinator, bounded windows,
strict shrinking, seed/concrete/corpus replay and stale ownership. The independent
POO-free package now requires 145 cases. `examples/generated-products.ss` combines
a five-bit balance, signed delta, modular mode and revised port range in a Record
with a wrapped Function and FUN action. It detects wrapping arithmetic versus a
saturating reference, replays the failure through a data-only codec, refuses a
retired port descriptor, and accepts a freshly prepared corrected service.
Regressions cover unbounded/one-sided intervals, large bit widths, empty domains,
malformed endpoints, override precedence and getter ordering after invalidation.

`PropertyNumbers.lean` proves anchor admission, window admission/nonemptiness,
size-zero uniqueness, width bounds, sign/distance reconstruction, strict candidate
descent, interval preservation and terminal anchors. Top-level examples fix both
positive and negative boundaries. The interpretation requires exact arithmetic,
faithful interval metadata, truthful revision clocks, terminating callbacks and
the existing random-source contract. These are finite source/model laws advancing
the paper's future work, not proofs of Scheme execution, PRNG distribution or
wall-clock performance. The width bound is not a constant-time bignum arithmetic
claim. All existing checks and resource limits remain unchanged.

## P48: one spelling protocol for text carriers and keyword call values

The concentrated audit found that the existing Keyword Type had validation and
standard string conversion but no automatic PBT derivation. FunctionArguments
therefore could not derive ordinary Keyword arguments or Keyword-valued declared
parameters. This closes an existing finite data path; it does not infer arbitrary
predicates or synthesize unrestricted callbacks.

The generic module adds `generator-keyword` by mapping the existing string tree
through Gerbil's `string->keyword`. It shares size, alphabet/length bounds, seed
splits, lazy children and source ownership with String/Symbol generation. The
POO data profile selects one representation pair using standard `defvalues` and
`compose`, then uses one character/byte-list generator and shrink policy for
String, Symbol, Keyword, Bytes and fixed BytesN. It allocates no conversion lookup
table and installs no extra validation chain. Representation conversion occurs
once per materialized node; the original list tree retains child provenance.

Empty spellings, whitespace, colons, NUL and Unicode scalars remain data. A Keyword
value does not become an omitted argument or a keyword declaration. Existing
FunctionArguments owns escaping and optional/keyword/rest interpretation; this
unit supplies the missing value generator instead of duplicating its parser.
Shrinking retains the carrier and the existing content rank; equal-length character
shrinks can decrease content, while empty spellings are terminal. Wrong carriers
fail the existing Type/Function boundary. Source checks, callback errors and
stale report refusal retain their existing semantics. Fresh preparation after
revision is explicit. Opaque/refined Types still require explicit generators;
this does not add JSON inference, arbitrary interning policy or an eval mechanism.

Generic controls compare seeded string/keyword spellings, test constrained
alphabets and lengths, sensitive Unicode and empty data, and replay an empty
minimal failure. Independent admission now requires 148 cases. Typed regressions
exercise strict spelling shrink rank and shared Keyword leaves in Tuple/List/Pair/
OrFalse/Sum. `examples/generated-products.ss` exports `keyword-routing-action`:
a Record with Keyword fields and wrapped Function flows through a declared
keyword parameter and FUN. The fault confuses an empty spelling with omission;
the test detects it, preserves wrappers, replays seed/concrete/corpus witnesses,
rejects a retired descriptor and admits a fresh corrected action. A separate
FunctionArguments control composes ordinary/optional/keyword/rest Keyword values.

`PropertySequences.lean` proves six representation laws: spelling recovery in
order, neighborhood cardinality, proposal origin, strict rank descent, declared
domain preservation and terminal neighborhoods. Top-level examples use a distinct
carrier with empty and reader-sensitive spellings. Faithful standard conversion,
terminating callbacks, accurate source clocks and the existing character/list
neighborhood laws remain interpretation premises. These finite model laws do not
prove Gerbil intern tables, the compiler, PRNG distribution or physical memory and
latency. This advances the paper's future-work direction. No upstream code,
module framework, namespace, runner, resource limit or acceptance check changes.

## P55: owned finite sequence preparation

The audit reproduced a split preparation boundary in the existing finite value
policy. With input (4 6), a first parameter callback changing the caller's second
pair caused the next callback to receive 99 and emitted (0 99), although the
structural phase had already captured (4 6). A model initializer could likewise
change the commands that repair/preflight subsequently processed. Truncating or
cycling the caller's spine could make a previously admitted finite input cease
to be the input actually traversed. This is framework-owned spine preparation,
not automatic discovery of mutable payload dependencies or arbitrary termination.

Both finite value policies now use one private deletion algorithm over an owned
spine. list-deletions and data-list-shrinks each admit and copy their input once
with Gerbil using/list? and list-copy. The latter's structural and parameter phases
read that same copy; no additional candidate validation wrappers or strategy
selector is introduced. The common model fold similarly copies before initial,
accept, normalize, enabled or advance callbacks. repair-trace, valid-trace? and
check-trace share that fold, so the actual fixture sees the preflighted commands.
Malformed initial spines still refuse before effects, and malformed parameter
spines still refuse the entire finite neighborhood without salvaging prefixes.

Rackcheck's pinned make-shrink-tree / gen:with-shrink composition retains the
value whose neighborhood is being described; its ordinary immutable Racket list
spines do not have Scheme's pair-edit window. Our existing mutable Scheme input
boundary therefore owns its spine explicitly, while keeping the same generator,
source checks and runner. This follows the project's FUN/IO separation: preparation
owns finite data and composition; the actual fixture owns effectful cleanup.
No new framework, namespace, upstream compiler change or deep-copy mechanism is
needed. Returned candidates may share private snapshot tails, as before; neither
exclusive ownership between candidates nor arbitrary host-heap immutability is
claimed. Command payload identities and declared source obligations are unchanged.

Six independent cases cover value edits, truncation, improper/cyclic caller tails,
paused deletion iterators, all five model preparation hooks, differential checking,
shallow payload identity and source/exception precedence. All 168 earlier generic
cases remain, raising the independently compiled library to 174. A complex typed
example combines Record commands containing checked Function fields, preparation,
finite shrinking, scoped differential fixtures and the existing FUN debug action.
It shrinks to the faulty command, retains Function wrappers, replays seeded and
concrete witnesses, refuses old evidence after owner revision and explicitly
prepares a corrected passing run with balanced cleanup.

PropertySequences.lean adds finiteSequenceParameters using the existing guarded
finiteShrinkStage. Eight laws prove empty behavior, head/tail refusal without
partial publication, exact causes, retirement precedence, malformed refusal,
one batch per captured coordinate and fixed coordinate order despite state
replacement. Top-level examples include ambient list replacement, malformed later
batches, false values/causes and retirement. Accurate standard spine copying,
sequential terminating callbacks, faithful source observers and immutable/shared
payload discipline remain premises. This advances the paper's future work, not
host allocation, concurrent mutation or compiler/runtime verification. The added
model snapshot costs a linear shallow copy per preparation; no wall-time or
allocation improvement is inferred from these correctness controls. Existing
complete checks, watchdogs and heap limits remain unchanged.

## P57: fixed product row and finite expansion ownership

The audit reproduced three defects in the value-level product path. An improper
child neighborhood invoked the packer once before refusing its tail. A two-field
product whose unpacker returned one value measured only that prefix, invoking
one child and returning four instead of refusing the decomposition. A packer
editing its temporary row changed a subsequent child argument from six to 99.
The retained product tree already owned its rows; the finite view did not share
that preparation discipline. These are concrete protocol gaps, not inference of
arbitrary representation inverses or automatic proofs of user callbacks.

The generic product specification now captures one proper row of exactly its
fixed width before admission or measurement callbacks. Gerbil list? establishes
properness before std/list/list's length=n? checks width; that standard helper
alone also treats an improper terminal atom as an end, so it is not a replacement
for list?. Invalid membership remains false, and invalid explicit measurement is
an error before field effects. Empty rows remain valid data at width zero; a
false row is invalid, while a row containing a permitted false payload is valid.

Typed product measurement delegates to that same generic owner. Finite shrinking
admits and copies its unpacked row before child or packer calls. A single private
finite-shrink-children boundary validates/copies every finite POO child spine;
products invoke it after their existing checked child action, and ordinary raw
sampler lifting uses it after the inherited source action. Source refusal and
original causes therefore retain their existing priority. Generic user shrinkers
still accept Iterators; their explicitly budgeted infinite neighborhoods remain
supported. No generic iterator is eagerly converted into a finite list.

Every product packer receives a private complete outer row. The existing reversed
prefix is reconstructed with standard foldl/cons and a copied suffix, avoiding
another reversed-prefix list. Thus consuming a pack argument cannot change the
remaining coordinates. Constructor identity, field order, per-coordinate callback
order, interleaved packing and source gates stay with their original owners.
Malformed child lists cannot publish prefixes; a later error still discards the
returned batch, without rolling back already performed callback effects. A producer
retaining an alias to its returned candidate spine cannot change an already
prepared typed iterator's next candidate. Payloads themselves are not deep-copied;
mutable semantic data and callback dependencies retain their source obligations.

This follows the pinned Rackcheck retained-product/shrink-tree direction and the
author's compositional representation discipline. It reuses the project product,
Type, Record and FUN protocols plus standard Gerbil list operations. No second
product engine, public adapter, runner, namespace or upstream change is introduced.
The pure fixed-width checks occur once at the operation's owning boundary rather
than validating every packed field through another wrapper. Snapshot copying has
linear spine cost; these correctness controls make no wall-time speedup claim.

Four generic cases cover malformed/short/long rows, zero fields, false payloads,
measurement snapshots and exact source/cause refusal. All earlier 181 cases remain,
raising the independent stdlib-only compiled acceptance to 185. Eight typed cases
cover invalid finite child batches before packing, decomposition failure before
any field work, staging-cache and consuming-packer edits, paused producer aliases,
exact causes and source retirement. The complex consuming-product-sampler example
composes UInt, Integer and Bool fields with a Record/Function carrier. Its standard
reverse! packer is valid on private rows. The ordinary finite and retained views
agree on the minimal witness, attempt count and shrink steps through FUN/corpus
export, seeded/concrete/portable replay, old-source refusal and fresh corrected
preparation. Function argument contracts remain checked on each witness.

PropertyProducts.lean reuses PropertySequences.finiteShrinkStage and the existing
guardedStages. Eleven laws establish exact-width row capture, empty/invalid
separation, refusal before consumers, original-row forwarding, coordinate width,
prefix/suffix order and no finite batch after child or packing refusal. Examples
cover unequal widths, false payloads, malformed children and source retirement.
Faithful standard shallow copying, sequential source binding, terminating callbacks
and the application's Type/pack/unpack laws remain premises. These are not host
heap alias proofs, automatic isomorphism discovery, concurrency verification or
compiler/runtime validation. Existing complete checks and resource limits remain.


