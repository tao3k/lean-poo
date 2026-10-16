# Native concurrent installation of approved joint receipts

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper supplies composable lens-based construction, not this transaction or
thread scheduling protocol. Existing FUN revisions, native policies, SCC closure,
opaque approval receipts and the owner installation mutex remain reused.

## Bounded standard-library thread composition

`examples/joint-concurrency.install-concurrently` starts real Gerbil worker threads
for receipts whose local and joint approvals have already returned. Each announces
readiness through a standard `:std/sync/channel`, then waits for a release token.
Only after ALL workers announce readiness does the caller run `before-release` and
release the workers. There is no scheduling sleep, forced winning thread or joint
callback pretending to have returned.

Every worker invokes the existing `install!`; no concurrent approval, implicit
retry or rebase occurs. Outcomes are `(snapshot . failure)` pairs in COMPLETION
order. The owner mutex serializes each whole-bundle installation; the helper does
not add a global transaction or modify the owner's lock. Errors outside ordinary
installation outcomes are transported by thunks and re-raised in the caller.
Receives and successful joins have fixed five-second bounds. Handles are retained
immediately and a `finally` terminates retained workers, including on coordination
failure. The `before-release` callback must return locally and production installed
metadata remains immutable.

This establishes real native thread interleavings on this Gerbil host. It does not
establish simultaneous multi-core execution, fairness or a formal runtime-mutex
implementation proof.

## Six lifecycle rounds with genuinely competing receipts

`t/joint-concurrency-test.ss` executes merge / replace / restore TWICE at both
services, using the existing phase/source declarations. In each round:

1. Two approved receipts share one proposed shared policy. Two others independently
   approve different policy objects with total budgets B and B+2 (B=48/32/24).
2. Five workers receive the two shared receipts, the two independent receipts and
   a duplicate of one independent receipt. All five become ready before release.
3. While they wait, only the UNINSTALLED shared policy changes B -> B+1 -> B.
   All three values still admit the candidate settlements. The two shared receipts
   are stale by revision, independently of which valid worker wins.
4. After release, exactly one outcome succeeds. Its policy must be one of the two
   independent policy objects; its entire snapshot must equal the actual owner
   winner. Failed outcomes may capture the old bundle or the winner, depending on
   when their failure/current read occurs. No mixed bundle is allowed.
5. All prior-round receipts are resubmitted on real threads against that current
   topology and all fail. The next round explicitly stages and approves new edits.

Both independent feedback receipts retain exact identity. Deleted B/D lack current
receipts after replacement; restored compact support removes E/F receipts and
code/base providers. After six rounds a fresh policy-only publication restores
exact original ceiling/budget values without any constructor work. All 24 retained
receipts race again and remain obsolete.

Another control races three workers on the SAME approved receipt and requires
exactly one success. A coordination-failure control raises the original exception
before any release, verifies no installation, then races the still-current receipt
successfully. Worker cleanup runs on that failure path as well.

## Formal lock-order laws

`Functional.JointPublication.installSequence_winner` proves that the first current,
guard-valid receipt wins over any finite tail staged at the old head, assuming its
installed identity is fresh. `competing_orders` proves BOTH possible orders for two
valid receipts, without picking a scheduler winner. `receipt_replay_refused` proves
the second checked decision reports refusal after a fresh installation, even for
the same receipt with unchanged guards. Existing validity, stale-batch and drifted-
attempt elimination laws compose with them for longer histories.

`Examples/JointCompetition` checks all six serialized orders of two valid receipts
and one drifted receipt at EVERY step of six actual component topology rounds.
Candidates retain typed sources, discovered supported SCC graphs and successful
resolver-equation receipts; admission certificates check actual local and joint
predicates. The shared certification fixture is reused by earlier receipt controls.

The formal bridge assumes native whole-bundle installations linearize under the
owner mutex, registered revisions faithfully cover dependencies, installed metadata
is immutable and identities are fresh. It proves properties of those serialized
orders; native tests independently execute threads, admission and pointer checks.
Finite declared components, lawful lenses and faithful pure locally total builders
remain premises. No arbitrary concurrent internal writes, global convergence,
distributed/durable atomicity or performance claim is made.
