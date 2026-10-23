# Interface-passing and receiver-bound collection styles

`table-styles` derives pure, mutable, linear, posh and classy protocols from one existing persistent table,
including a `table-wrapper` representation. It remains part of `clan/poo/table`;
`table/styles.scm` is a standard Gerbil include, not a second public namespace.
This advances the general collection TODO and the proposal's future work, using
the original text's pure-value / mutable-cell / consuming-reference construction.
It does not introduce a static linear type system or destructive tree backend.

## One interface and one admission boundary

```scheme
(def styles (table-styles table))
(def mutable (.@ styles Mutable))
(def linear (.@ styles Linear))
(def current (.call mutable .ap admitted-snapshot))
(def next (.call linear .apply-batch
  (.call mutable .convert current 'linear) ordered-deltas))
(def snapshot (.call linear .convert next 'pure))
```

`Pure`, `Mutable` and `Linear` each reuse FUN `Wrapper`:

| Operation | Contract |
| --- | --- |
| `.admit raw` | Recursively normalize through the original table descriptor, then create a state. |
| `.ap admitted` | Wrap an already admitted persistent snapshot; preserve its exact Function identities. |
| `.unap state` | Nonconsuming snapshot read; retains the current owner. |
| `.bind state consumer` | Existing FUN snapshot observation under the full source metadata guard. |
| `.map transform state` / `.step state transform` | Stage one transformation of an admitted snapshot; require an admitted persistent result. |
| `.apply-delta state delta` | Reuse the original guarded optimistic installer. |
| `.apply-batch state deltas` | Reuse `.compose-deltas` and `.apply-delta`, retaining intermediate conflicts. |
| `.convert state target` | Transfer ownership to `pure`, `mutable` or `linear` without normalizing again. |

The transform returns exactly one admitted snapshot. Existing persistent collection
operations supply such snapshots; constructing arbitrary raw children requires
`.admit` first. A membership recognizer is not evidence that an arbitrary raw
procedure has already received a Function wrapper. Re-admitting previously
captured snapshots can change wrapper identities and invalidate an identity-sensitive
delta, so it is an explicit operation rather than an invisible step in conversion.

## Ownership and observation

| Source | Successful update | Successful conversion to any target |
| --- | --- | --- |
| Pure | Return new snapshot; old snapshot remains usable. | Original snapshot remains usable. |
| Mutable | Install one new head; return the same reference identity. | Retire every old alias; prepare a fresh target before retirement. |
| Linear | Retire every old alias; return a fresh live reference. | Retire every old alias, including same-style conversion. |

All nine source/target combinations retain exactly the same admitted table root.
Nonconsuming `.unap` snapshots are intentionally shareable and remain usable after
retirement. Ownership concerns the update capability, not exclusive physical
ownership of a tree, Function closure, or leaf object. Persistent backend operations,
immutable leaves and stable pure conversion callbacks are explicit premises.

## Failure, concurrency and effects

Foreign factory/style references and consumed references refuse before the callback.
An invalid target refuses before ownership is touched. Metadata revisions invalidate
all older style protocols, including their reads; build a fresh factory to retry.

A callback exception retains its original cause. Type refusal or any early/late
batch conflict installs no staged snapshot and consumes no reference. On an
otherwise unchanged owner, retry can use that same owner. Earlier callback or IO
effects are not rolled back. An IO consumer runs only after conversion/installation;
its failure does not resurrect consumed references or automatically replay effects.

Gerbil's runtime `with-lock` protects short capture/installation critical sections.
User callbacks run outside locks. Descriptor metadata changes must be serialized
with these operations; the head lock protects table ownership, not a global
transaction across mutable descriptors. Installation compares an unforgeable immutable
head identity, so two staged requests have at most one winner. A losing request
refuses without overwriting the winner; retry uses the current mutable owner or
the winner's new linear reference. Returning to an equal snapshot does not bypass
this check. Reentrant updates follow the same rule without deadlocking.

## Proof and acceptance boundary

`LeanPoo/Functional/TableStyle.lean` reuses the existing ordered dictionary carrier,
batch and `Prototype.LinearState.stepValue` model. It proves style-independent
results, exact failure retention, pure snapshot preservation, mutable/linear state
transitions, all conversion observations and consumption, stale/retired/ABA
rejection, and whole-table success/conflict correspondence. Atomic table failure is
the specialization that supplies the original value on error to the existing
lower-level linear state protocol; that lower-level protocol still permits partial
writes when explicitly supplied by its caller.

The generation model assumes authentic captured generations and increments on every
successful owned installation. Scheme implements those generations as private head
identities, checked by pointer identity under the official lock. This is semantic
correspondence, not a proof of Gambit scheduling, mutex implementation, arbitrary
user callbacks, exception-safe foreign resources, or compiler correctness.

`examples/service-collection.ss` composes derived representations, mutable-to-linear
transfer, complete ordered batches and Reader/IO observation. Regression controls
exercise all nine conversions, persistent snapshot aliasing, wrapper retention,
late conflict and retry, reentrant/ABA changes, two real staged workers, stale
metadata, and rejected foreign ownership. No automatic retry or callback replay is
introduced. Costs include admission, conversions and equality; changing styles
alone is not an in-place optimization or a wall-time performance result.

Local full acceptance: 126 modules / 1,219 cases passed in the single-process
linked test program, status 0, wall 62.225 s, CPU 21.384 s and GC CPU 3.813 s.
The unchanged limits are 1 GiB heap and 300 s for the complete suite. These are
acceptance measurements, not matched speedup evidence.

## Posh and classy receiver derivation

The collection proposal [fare/projects#10](https://github.com/fare/projects/issues/10)
uses **posh** for pure object-oriented style and **classy** for impure
object-oriented style, with interface information attached to runtime objects.
This implementation advances that proposal and the original prototype paper's
future work. It does not claim that the paper's Racket code already provides this
collection library.

`Posh` and `Classy` reuse FUN `Wrapper`, the same admitted persistent backend and
the same private capture/installation engine as `Pure`, `Mutable` and `Linear`.
They attach their originating protocol to an ordinary private Gerbil `defstruct`.
Official `defmethod` dispatch supplies receiver calls. The existing `@@method`
escape is explicit because this project's ordinary braces denote POO object
construction. There is no new method expander, public namespace or cache.

```scheme
(import (only-in :clan/poo/brace @@method))
(def styles (table-styles descriptor))
(def posh (.call (.@ styles Posh) .ap admitted-root))
(def newer (@@method posh.acons key admitted-value))
(def classy (@@method newer.convert 'classy))
(@@method classy.apply-batch ordered-deltas)
(def snapshot (@@method classy.snapshot))
```

The receiver methods are `snapshot`, `bind`, `step`, `apply-delta`, `apply-batch`,
`convert`, `ref`, `count`, `list<-`, `acons` and `remove`. Point operations use the
backend's existing argument/default and absent-key semantics. The same operations
are available on the generated FUN protocols (`.snapshot` is spelled `.unap`).
Read methods observe the current head under the original metadata guard; no
computed receiver field caches a mutable snapshot. `step` and point/batch updates
require already admitted results. Use the protocol's explicit `.admit` boundary
to recursively normalize raw Functions once.

| Presentation | Successful update | Successful ownership transfer |
| --- | --- | --- |
| Posh | New receiver; old receiver and snapshot remain usable. | Source remains usable. |
| Classy | Same receiver identity; aliases observe the new head. | All old receiver aliases become consumed. |

Every source can convert to `pure`, `mutable`, `linear`, `posh` or `classy`.
All **25** combinations retain the exact admitted snapshot and Function closures.
Same-style owned conversion still retires the old capability. Posh can produce
multiple independent owned receivers from a shareable pure root, which does not
assert exclusive physical ownership of the tree or its leaves.

Target admission and complete receiver construction happen before retirement of
the source. Invalid targets, foreign protocol receivers, callback/validation
errors and stale-generation conflicts expose no staged result. Prior external
callback effects are not rolled back. A callback can reenter or race another
request: the original immutable-head check still allows at most one installation
from a captured generation. There is no implicit retry, callback replay or
backward-compatibility dispatch path.

`examples/service-collection.ss:revise-ledger-receivers` composes a derived
key/value representation, checked Function leaves, posh-to-classy transfer,
ordered batches, transfer back and Reader/IO. The regression suite covers the
25-way matrix, exact Function retention, inverse recovery, failed batch suppression
of IO, receiver provenance, metadata invalidation, reentrant conflict and retry.
The existing real concurrent staging regression also runs with `Classy`.

The extended `LeanPoo/Functional/TableStyle.lean` proves receiver observation
commutes with the existing engine, posh persistence, classy identity, exact callback
failure, retired-reference refusal, preparation-before-commit failure retention,
the full conversion matrix and representation erasure. Generation-race safety
reuses the existing installation theorem. `Examples/CollectionStyles.lean`
combines checked-callback payloads, revisions, failed preparation, retry and stale
installation. Authentic family provenance, fresh host identities and immutable
persistent payloads are premises; runtime class dispatch, OOM/process termination,
mutex implementation and arbitrary user IO are not formalized. These are semantic
laws, not a speedup or compiler-correctness claim.

## Snapshot-bound observation across every style

Style generation now lifts the existing observation protocol as a whole:
`.iter<-`, `.foldl`, `.foldr`, `.seek<-`, `.seek`, `.range`, `.index-ref/opt` and
`.index-range`. Both `Posh` and `Classy` implement Gerbil's standard `Iterable`;
ordinary `iter` / `for` work on receivers. Their corresponding explicit methods
use the existing `@@method` syntax, with the receiver first; protocol folds retain
`methods.table`'s `(callback seed state)` signature. For example:

```scheme
(def cursor (iter classy))
(def total (@@method classy.foldl (lambda (_ value acc) (+ value acc)) 0))
(def window (@@method classy.range (some lower) (some upper) #t #f))
(def positioned (@@method classy.seek<- (some lower)))
(def priority (@@method classy.index-range 'priority #f #f))
```

An operation captures exactly one admitted persistent root before its backend
callback. Reentrant updates during a fold do not change that fold's remaining
snapshot. A delayed cursor retains the root captured at creation: later updates,
ownership transfer or retirement do not splice another generation into it.
New cursor issuance from a retired owner still refuses. This is nonconsuming
snapshot observation, just as `.unap` already returns a shareable pure root.

Every delayed pull, including repeated EOF, checks the captured descriptor
revisions through `iterator-map` and the original source guard. No ownership lock
is held across iteration or arbitrary callbacks. Descriptor revisions invalidate
old cursors; rebuilding the factory and creating a new cursor is explicit retry.
A backend pull that raises is not automatically replayed: whether its internal
cursor has already advanced remains the backend's own exception semantics.
External callback effects are not rolled back.

Ordered and indexed queries forward the original comparator, inclusive/exclusive
bounds, Option/missing-key convention, branch order and failure cause. A missing
backend method raises `unsupported table observation`; a style never invents an
ordering, index or seek algorithm. These methods are callable on every generated
protocol, but the protocol's field presence does not certify source capability.
`source` remains the authority for capabilities. Construction guards the dynamic
slot lookup through the existing `.slot?` protocol.

Positioned traversal calls the existing backend once, then wraps its iterator in
the original metadata guard. It does not restore seek by full enumeration or
sorting. Generic `.iter<-` retains its backend's existing cost (the default table
implementation materializes `.list<-`); no general lazy-tree or constant-time
claim is made. Fold callbacks/results keep backend traversal and return semantics.
The wrapper adds guards and ordinary interface dispatch, not a performance theorem.

`observe-indexed-receiver` in the existing service example composes one
snapshot-bound FUN observation with correlated range selection, checked Function
invocation and outer Reader/IO consumption. A callback refusal suppresses the IO
consumer; previous callback effects remain. Regressions cover all five styles,
standard Iterable dispatch, fold directions and reentrant publication, source
invalidation at EOF, retained cursors after transfer, positioned traversal with a
scan-forbidden backend, atomic index publication, inverse and explicit retry.

`LeanPoo/Functional/TableObservation.lean` reuses `TableOrder`'s guarded finite
cursor. It proves exact delegation/failure causes, unsupported and consumed
refusal, stale-origin precedence, stream/payload preservation, single-pull/zero-pull
admission, EOF validation and separation between a changed classy head and its
captured snapshot. The existing top-level `Examples/CollectionStyles.lean` covers
opaque callback payloads, revision, retirement, delayed stale rejection and
unsupported queries. These proofs assume immutable admitted roots, authentic
origin versions, lawful finite enumeration and backend behavior; they do not
verify the runtime Iterator implementation, GC, scheduling or arbitrary IO.
