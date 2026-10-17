# Rechecking prepared recovery

This advances the generalized-prototype future work in Appendix B of the Racket
source. The source supplies the inheritance/lens/cooking and method-combination
constructions; it does not supply this concurrent coordination protocol.

`prepareRejoining` constructs a valid candidate against an explicit whole bundle.
`checkRejoining` and `resumeRejoining` retain that exact receipt only while its
captured head identity and registered approval revision still match. A competing
publication or revision drift rejects it before a pure continuation is evaluated.
An explicit retry must run the factory against the actual current bundle.

The Gerbil `check-approved` uses the same private owner/receipt/guard checks and
short lock as `install!`, without construction, approval callbacks or writes.
`rejoin-checked` composes existing `rejoin-after` with a validator and continuation;
exceptions retain their identity and follow the supervisor's existing recovery
path. All prepared values are preserved. A validator may rendezvous after successful
preparation and then raise the refusal returned by `check-approved`.

A successful observation does **not** reserve the head. `install!` must check again;
`checkRejoining_install_stale` proves that a later competitor or metadata change
retains the actual winner. Head identities must not be recycled; the model's
revision values represent the registered native lens guards. Hidden callback
state, arbitrary asynchronous interruption inside installation, process crashes,
fairness, eventual recovery and a Scheme memory-model proof remain outside these
finite serialized-trace theorems.

`Examples/JointCoordination.lean` checks both recovering receipts against competing
winners, independent guard changes, fresh retries and a race after successful
observation across six certified SCC merge/delete/split/restore rounds.
Gerbil `t/coordinator-prepared-test.ss` runs two live recovering names, releases
successful preparation in both orders, forces head and same-value guard drift,
retries both names, races final installation and refuses archived receipts across
all six rounds. Handshakes impose checkpoints, not a timing-based winner.
