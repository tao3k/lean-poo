# Collection style correspondence

`table-styles` derives all three protocols from one existing persistent table,
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
