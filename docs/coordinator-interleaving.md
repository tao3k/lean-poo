# Interleaved recovery of multiple coordinators

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2087–2133).
The underlying lens/cooking constructions, FUN revisions, graph/SCC closure and
guarded whole-owner publication remain reused. The paper does not supply this
concurrent recovery supervisor.

## Named recovery composition

`examples/coordinator-rejoining.call-with-rejoining-coordinators` composes the
existing supervisor's two hooks into one `recover(name, outcome)` callback. The
callback handles the original outcome and returns an operation to run as a new
instance, or `#f` to leave that name stopped. A private native eq-hash table routes
replacement decisions by name; live supervision consumes each decision once.
No global last-failure flag or cross-name replacement slot is required.

This is supervisor-only IO. Standard channels carry worker observations; old
children are cleaned and the old parent joined before recovery runs. Each new
instance retains its own group, inbox, reply lifecycle and installation scope.
Callbacks and malformed replacement values propagate to whole-scope cleanup.
Even final-join callbacks validate their result; final joins never launch work.
The callback must decide how to handle its outcome. Returning a replacement does
not itself certify admission, and the adapter adds no retry or publication power.

## Two failed names, five recoveries, six source phases

`t/coordinator-interleaving-test.ss` reuses the continuing service-revision
operation and all shared six-round whole-state assertions. a/b remain alive.
The active sets and failures are:

| Round | SCC phase | Active names before failure | Failure | New instances joining |
| --- | --- | --- | --- | --- |
| 1 | merge | a/b/c/d | c | none |
| 2 | replace | a/b/c/d | d | c |
| 3 | restore | a/b/c/d | none | d |
| 4 | merge | a/b/c/d | c and d | none |
| 5 | replace | a/b/c | c | c |
| 6 | restore | a/b/c/d | none | c and d |

Both fourth-round exit orders are tested. Replacement d waits across the fifth
round while c rejoins, fails again, and creates another replacement. Sixth-round
ready acknowledgements may arrive in either order; publication winners are never
chosen by the fixture. Each callback verifies its name's original error, actual
saved worker termination and exact unchanged authoritative bundle before allowing
remaining names to compete.

Every phase includes a shared proposed-policy B -> B+1 -> B revision trip,
refusal, independent fresh preparation and exactly one successful primary.
Historical siblings cannot overwrite current winners. On rejoining, each name
explicitly replays its archived receipts against the installed previous-round
winner before preparing anything new; every refusal must preserve that whole head.
The fixture also checks 24/16/12 settlements twice, component/code/base erasure,
independent dependency receipt reuse and all saved parent/child handles terminated.
Each exit is counted: c has three failures/restarts plus a normal exit, d two plus
a normal exit. A separate control makes d's recovery handler fail after c's new
instance and child are already alive; root cleanup must terminate those actual
saved threads and propagate d's original recovery error. Another control rejects
a malformed recovery value even when observed only during final joins.

## Formal recovery waves

`Functional.JointPublication.lifecycleOnly` classifies only stop/rejoin events.
`coordinatorAttempts_lifecycle` erases any finite such wave, across arbitrary names
and orders; actual installation events are never classified as lifecycle-only.
`installCoordinated_recoveryWave` preserves a committed prefix and the surviving
attempt order around a wave. `recoveryWave_refused` preserves the exact current
bundle under arbitrary mixed head/guard-stale historical attempts after recovery.
`restageAfter_recoveryWave` proves explicit fresh factories still observe that
actual whole winner. Projection embedding/concatenation laws retain attempt order.

`Examples/JointCoordination` uses actual certified heads, discovered SCC support,
closure equations and joint admission. In each of six phases, two lifecycle orders
and four rotations of current competing receipts check all four possible first
winners, with mixed prior-generation/shared-guard refusals before and after them.

Refusal requires an obsolete head or registered guard drift; recovery alone does
not revoke a still-current receipt. Native cleanup controls cover waiting children.
The bridge retains valid total factories, correct dependency/lens laws, complete
guards, immutable installed policies, fresh owner identities and lock-linearization
premises. No asynchronous critical-section interruption, thread-runtime proof,
fairness, arbitrary convergence, durable/distributed atomicity or performance
improvement is claimed. Scope and local wait/harness bounds remain unchanged.

Recovery preparation can now fail before the service continuation, then retry
through the same supervisor. See [coordinator-retry.md](coordinator-retry.md) for
four preparation failures interleaved with persistent publication and formal errors.
