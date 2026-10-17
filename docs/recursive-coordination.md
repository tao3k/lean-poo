# Named recursive coordinators and completion boundary

This completes the scoped recursive coordinator lifecycle, not every original
POO TODO. It extends generalized MOP future work: the Racket essay's Future Work
and Appendix B motivate protocols, lenses and metadata, but do not specify this
multi-coordinator policy. Existing graph closure, FUN observers, admission and
`bind-evidence` are reused; there is one publication engine and one shared owner.

## One protocol across exit and recovery

`recursive-coordination.coordination owner` creates a private per-name registry.
`call-with-coordinator registry name coordinate on-exit: handler` supplies
`(generation prepare! enqueue! advance! pending?)` to the coordinator. Names are
symbols and only one incarnation of each name may be active. Different names can
keep separate submission scopes live while calls on the shared owner serialize.

`prepare!` accepts an existing staging Reader `(owner -> guarded-request)`.
It binds the returned request to this private incarnation without replacing its
snapshot, source or approval guards. On exit both queue operations and incarnation
close before `on-exit` receives the existing outcome thunk. Recovery creates a new
incarnation and requires explicit staging. Saved old factories/requests reject
before construction, even if NO publication or approval mutation intervened.
A same-name replacement cannot be closed by cleanup of an older incarnation.
Malformed callbacks/staging results and duplicate live names refuse explicitly.

The fence applies to requests prepared through this protocol. Ordinary unowned
requests retain their existing semantics; arbitrary user procedures are not made
safe by wrapping them. Factories must use the existing checked staging constructs,
register all dependencies and obey the serialized/pure callback discipline.
This is lifecycle isolation, not security against trusted raw access.

## Integrated acceptance workflow

One survivor stays live across eight actual graph rounds. Two other names each
have three incarnations per round: initial failure with pending work; nested,
interleaved recovery followed by failure; fresh competition followed by another
exit. Proposed and installed approval ABA invalidates BOTH live competitors.
Explicit fresh requests compete, alternate winners, preserve installation after
late effect refusal and subsequent coordinator failure, then retry with a fresh
refinement/evidence observation. A local-success/joint-budget refusal is distinct
from coordinator, approval and head staleness.

The 49 exits (24/24/1 incarnations) retain 120 externally saved requests. There
are 1112 actual attempts: eight installations, 1024 generation refusals, 56 approval
refusals, 16 joint-admission refusals and eight head refusals. No sleeps, timing
winner choice or hidden retries occur. Shared provider removal/reintroduction and
migration, SCC merge/split, computed reader/body changes, old dirty reference
rejection, exact idle reference reuse and three contexts (3/3/2) are all checked.
Focused controls prove the new host behavior empirically: same-head/stamp rejection
without invoking the old request body; duplicate-name refusal and independent
survivor progress; same-name replacement after cleanup; exact false exception and
handler-error behavior; malformed staging rejection before enqueue.

Lean `Functional.RecursiveCoordination` gives twelve universal finite laws for
busy/idle start, prefix-preserving stop, other-name isolation, old-cleanup refusal,
closed/generation rejection, step/trace generation monotonicity, step/trace graph
revision monotonicity and permanent historical incarnation refusal. The actual
finite fixture matches all 1112 attempts over the existing checked SCC/evidence
construction. Host scope unwinding, exception identity and multiple values remain
Scheme controls; queue cleanup also reuses `RecursiveRecovery`'s explicit scope
boundary. This is not a proof of Gerbil, GC, a compiler or a runtime.

Complete guards, exact identity correspondence, immutable-in-use metadata,
terminating pure formal callbacks and serialized owner access remain premises.
Forced asynchronous death, concurrent CAS, distributed durability and atomic
external-effect rollback remain outside this scoped protocol. No performance gain
is claimed. Scheme has no dependency on the Lean checkout.
