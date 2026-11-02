# Shared approval metadata across publication endpoints

This advances finite generalized-prototype future work by composing the original
Racket Appendix B lens/wrapper construction with existing component closure,
registered source guards and independent publication heads. The original
`$lens-gen` (source pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines
2108–2133) does not specify a concurrent shared-metadata transaction algorithm.

## Explicit shared serialization domain

`component-publication.approval-domain` creates a private standard native lock.
`publication` accepts an explicit `domain:`; omitting it creates an independent
domain as before. All endpoints sharing approval objects must use the SAME domain.
Their current heads and staged request ownership remain independent. Existing
`revise-approval!`, current-head reads and final guard/head installation checks use
that domain lock. No additional metadata representation, global epoch, invalidation
broadcast, manual request list or serialized proof constants are introduced.

A policy edit through either endpoint changes its existing native object revision.
All old requests whose registered guards observe that object refuse, even if its
values return. Local-only policy edits invalidate only observers, despite sharing
the same lock. Publication at one endpoint does not stale another endpoint's
unchanged head. The domain serializes metadata edits with each installation;
it does not publish several graph heads atomically or roll back arbitrary effects.

Related edits to shared and local approval objects are individual serialized slot
updates. Requests may observe intervening revisions and must pass current complete
joint approval at installation. No multi-object atomic update is claimed. Writes
through another domain, raw mutation and reentrant custom mutation hooks remain
outside this protocol. Complete dependency registration, faithful native revision
increments and lock behavior are implementation premises. Shared component
metadata/callbacks retain the existing immutable, pure, locally total discipline.

## Practical native alignment

`examples/shared-approvals.start` creates one domain and maps the existing service
constructor over independent local policies, pairing each with the exact same
shared object. It reuses all source recipes, fixed lenses, bounded whole-SCC closure,
FUN staging and current-policy restaging. No service-specific copy of shared
approval metadata is manufactured.

Four native scenarios cover:

- A shared revision makes two owners' pending requests stale before builders. A
  third independent domain's request still succeeds. Fresh requests at both owners
  install independently; the first owner does not invalidate the second's head.
- One local policy edit through a sibling endpoint invalidates only its observer.
  The other request, staged under the same domain, remains valid.
- Workers at two owners pause after approval. Shared approval is revoked and one
  local service limit tightened. Both old workers refuse. Restoring shared approval
  lets the unaffected local service publish; the other still refuses until its own
  current policy is restored and it explicitly restages.
- Owners have different topologies (merged versus compact). Shared change-back
  invalidates both pending requests; each then restages the correct local phase,
  producing split settlement=16 and merged settlement=24 independently. An unchanged
  feedback group's exact receipt is retained.

Standard channels/joins retain fixed five-second bounds inside the existing
90-second focused gate. These are bounded native schedules, not exhaustive SMP
or arbitrary mutable-object correctness proofs. Current approved snapshots remain
historical values; policy edits invalidate pending work rather than retroactively
revoking already installed snapshots.

## Lean correspondence

`Functional.SharedPublication` models a family of independent heads and reuses
`installChecked` at one selected endpoint. Generic laws prove sibling head framing,
no head changes on observed revision drift, observed-vector change for ANY changed
registered shared policy, equality when all registered dependencies are unchanged,
and propagated refusal at every observing endpoint. The observed vectors are
formed from actual declared dependency lists, not a global invalidation flag.

`Examples/SharedApprovals` closes real merge recipes for two services (settlements
24/30), checks shared invalidation without head advancement, fresh independent
installation, local-only revision selectivity and current-topology split=16.
Existing `ComponentExecution` supplies actual resolver equations and universal lens
laws. Identity/version numbers are local Lean fixtures and are never read by Gerbil.
Abstract serialized decisions do not prove runtime locking or automatically infer
metadata dependencies hidden in arbitrary callbacks.

The range remains accepted finite graphs, fixed lawful lenses, correct declared
reads, faithful builders and immutable/extensional component metadata. General
convergence/leastness, hidden dependencies and cycle-interior skipping remain open.
No compiler/runtime verification or performance claim. No new versioned JSON,
full benchmark data or archives are committed.

[joint-publication.md](joint-publication.md) adds a distinct authoritative bundle
interface for atomic policy replacements and consistent multi-endpoint publication.
The independent-head API described above keeps its original semantics.
