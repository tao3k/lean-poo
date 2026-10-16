# Multiple approved receipts across topology rounds

This advances generalized-prototype future work from original Racket Appendix B
`$lens-gen` (pin `9affa8fbbb4f12cbd98cb97f8b8b84474fc39429`, lines 2108–2133).
The paper supplies composable lens-based construction, not this multi-service
transaction protocol. Existing graph revisions, supported SCC closure, native POO
policies, FUN actions and checked whole-bundle installation remain reused.

## Ordered installation with complete outcomes

`joint-publication.install-sequence!` uses standard-library `foldl` to attempt every
input in order, returning an equally ordered list of `(snapshot . failure)` pairs.
It retains failures and continues to later independent receipts; it does not rebase,
reapprove or silently retry. Each attempt calls the existing `install!` and takes
its own short lock. Other publishers can interleave; the entire sequence is NOT
one atomic transaction. Each individual candidate is still a whole atomic joint
revision. Invalid/foreign receipts produce their ordinary failure outcomes. An
improper input list refuses before the sequence starts; an empty list does nothing.

`examples/joint-receipts.approve-revisions` prepares alternative endpoint `Change.`
lists against one explicitly captured bundle, all sharing one native proposed
policy object. It maps the existing declared phase/input streams into `stage-at`
and `approve`, without installing. A failure raises to the caller with no helper
installation; it cannot silently attach remaining alternatives to a newer source.
Independent policies require a separate explicit approval call. No candidate
receipt constructors, alternate graph representation or proof serialization appear.

## Six native rounds

The two services execute merge / replace / restore TWICE. Their settlements are
24/24, 16/16, 12/12 in each cycle; ceilings are 24,16,12 and total budgets 48,32,24.
Each round:

1. Two complete candidates share the same proposed shared approval object. A third
   candidate independently passes all approvals with a separate policy object.
   All three approval calls return before any installation.
2. The uninstalled shared policy's budget increases by one. Both values still
   admit the candidates, so refusing both receipts isolates revision freshness.
   The whole current snapshot remains exactly the pre-round object.
3. Its budget returns to the original value. The sequence attempts a shared
   receipt, the independent receipt, the other shared receipt and the winner again.
   Failure flags must be `(#t #f #t #t)`. The first outcome is the old whole bundle;
   every later outcome is the exact independent winner, including failed attempts.
4. All receipts retained from earlier rounds are replayed. None can revive old
   policies, support or SCCs. Explicit fresh approval precedes the next round.

The final replay covers all 18 receipts after numerical approval/support values
return to their original compact form. Both independent feedback receipts retain
exact native identity; deleted E/F have neither current receipts nor code/base
providers. Diagnostic joint-admission counts do not increase during installation
or replay: existing approval results are used, not rerun. Diagnostic mutation is
confined to test counters and UNINSTALLED proposed policies.

A separate control mixes invalid values and a foreign receipt before a valid
sibling, then repeats the winner. The valid sibling still installs, output order
and cardinality remain intact, and the foreign receipt remains usable by its owner.

## Lean laws and actual certified carriers

`Functional.JointPublication.Approved Valid` retains expected identity, candidate,
staged guard revision and a proof of a caller-specified candidate validity predicate.
`Installation Valid` adds the environment's revision observed at EACH attempt.
It is not a client-supplied bypass in native code: native `install!` reads its own
guards. `installSequence` folds the existing checked whole-bundle decision.

- `installSequence_valid` preserves validity for arbitrary finite receipt orders
  and guard changes, assuming valid current state and admitted candidates.
- `installSequence_stale` preserves the exact current bundle for any entirely
  obsolete batch, independent of candidate values, metadata changes or order.
- `installSequence_drift_between` removes a drifted attempt at ANY trace position
  without changing the final result, including after a prefix of SCC revisions.

`Examples/JointReceipts` instantiates validity with the ACTUAL local and joint
predicates, certifies every submitted candidate and executes six rounds. Every
head retains the actual source, discovered supported SCC graph and successful
resolver-equation receipt. Its final history replay retains the last identity and
component erasure. Native outcome lists and exact object identity controls remain
separate evidence from these semantic whole-bundle laws.

Premises remain finite declared components, lawful lenses, correct explicit
dependencies, fresh snapshot identities, faithful pure locally total callbacks and
immutable installed metadata. The abstract revision must faithfully represent all
registered native guards. This does not prove arbitrary concurrent object writes,
rollback of arbitrary effects, global convergence, distributed/durable transactions
or runtime/compiler correctness. No performance claim or benchmark data is added.
