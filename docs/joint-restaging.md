# Restaging while older installation workers remain pending

See [joint-coordination.md](joint-coordination.md) for independent coordinators
concurrently constructing, retrying and publishing through shared owner state.

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper supplies composable lens-based construction, not this installation
scheduler. Existing FUN revisions, lawful lenses, supported SCC closure, native
policies, opaque receipts and the guarded owner installation remain reused.

## Scoped coordinator IO

`examples/joint-workers.call-with-installations` passes `start` and `receive` to a
single coordinator callback. `start` creates one real worker, waits for its ready
acknowledgement and returns a one-shot release procedure. `receive` observes one
completed installation. The coordinator can build/approve/start new receipts while
older workers still wait for release, using the actual current whole snapshot.
There is no implicit rebasing or automatic retry of old receipts.

Standard channels, thread creation/join and `call-with-values` implement the scope.
A pure `report:` preserves receipt provenance outside the owner lock. Receives,
held-worker waits and successful joins retain five-second bounds. Each handle is
retained immediately; `finally` closes the scope and terminates retained workers.
A successful exit requires ALL started results to have been observed, then joins
the workers. Escaped coordinator/release procedures refuse after closure; release
is one-shot. Multiple return values from the coordinator are preserved.

The earlier `install-concurrently` is now a small composition of this scope:
start all receipts, run `before-release`, release them and receive all results.
This shares worker/error/cleanup code with the continuing pipeline. The owner mutex
and `install!` are unchanged. Already installed winners are not rolled back if the
coordinator later fails. Coordination is single-caller; callbacks must return
locally and held workers must be released within the existing bounded window.

## Continuous six-phase native workflow

`t/joint-restaging-test.ss` first approves two merge candidates and starts two
workers. One installs; the other remains waiting. The coordinator then executes
replace / restore / merge / replace / restore in the SAME worker scope:

1. From the new current topology, approve two next-phase receipts sharing a fresh
   uninstalled policy. Start them plus a historical initial receipt while the
   previous round's worker is STILL pending.
2. Change that proposed budget B -> B+1 -> B. Both values still admit the candidate.
   Release the historical worker and the two shared-policy workers; all refuse
   and return the exact pre-phase whole snapshot. The previous-round held worker
   has not been released or observed.
3. Explicitly stage and approve the SAME edits again, capturing current source
   and the proposal's new revision. Start a fresh primary and a fresh late sibling
   while the older worker still waits.
4. Release the older worker and the fresh primary; receive their two distinctly
   attributed outcomes in either order. Only the fresh primary succeeds. The new
   late sibling stays pending while the NEXT source phase is prepared.

Thus approval/restaging for later rounds happens inside the lifetime of pending
older workers, not after a batch has been drained. Head values follow 24,16,12
TWICE at both services. Independent feedback receipts retain exact identity;
removed B/D lack receipts after replacement, and restored-away E/F have neither
receipts nor code/base providers. The final held sibling is released/refused before
scope completion. The original historical receipt is repeatedly interleaved with
nearer generations throughout the workflow.

Lifecycle controls also reject a coordinator returning with unobserved work,
verify the whole current bundle survives that unreleased-worker failure, reject
escaped start operations and duplicate release, and preserve multiple return values
on a fully observed successful scope. Previous coordination-failure/real-race
controls continue through the refactored one-shot interface.

## Formal observed-prefix preparation

`Functional.JointPublication.restageAfter` evaluates a successful pure preparation
factory against EXACTLY the whole bundle after an observed installation prefix.
The factory returns a candidate with a validity proof; native construction and
actual admission establish that premise on successful preparations. Old receipts
are not rebound. `restageAfter_expected` proves the new receipt captures that
observed head. `restageAfter_late` proves new work can publish with arbitrary old
attempts still pending, assuming each late attempt is refused against the NEW
candidate by head identity or its own guard revision.

`Examples/JointRestaging` uses actual typed source/SCC/closure heads for six phases
in three consecutive pairs. Each pair publishes the first phase, rejects drifted
next-phase metadata, explicitly prepares the next phase from the observed head,
then checks older attempts before/after the fresh receipt and replays history.
Actual local/joint admission certificates remain inside the shared fixture.

The bridge assumes owner-lock linearization, fresh installed identities, complete
registered guards, immutable installed metadata, correct explicit dependencies,
lawful lenses and faithful pure locally total construction/admission. The model
covers successful factory results; it does not assert arbitrary factories always
terminate or succeed. Native scope/worker execution and formal serialized-order
properties remain separate evidence. No arbitrary internal writes, global recursive
convergence, distributed/durable transaction, runtime implementation or speed claim.
