# Typed table key focuses

This is a concrete collection-library future-work unit. It reuses the existing
Gerbil POO Lens, `using`, table deltas, persistent backends and FUN/IO. The standard
include `table/focus.scm` stays inside `clan/poo/table`; it is not a public module.

## Complete key protocol

`methods.table` now constructs both `.lens key` and `.lens/opt key` with the
existing `lens-of-get-set`. Both setters take **value before state**, matching
`Lens.set`, `Lens.modify` and `Lens.compose`. The required getter preserves the
backend's missing-key refusal. The optional getter distinguishes `#f` (absent)
from `(some #f)` (stored false); its setter also supports insertion and deletion.
Keys and optional payloads are recognized without normalization. Invalid keys,
invalid Option shells and incompatible values refuse; raw procedures must be
admitted explicitly at the normal Function boundary. Existing checked Functions
retain their exact identity.

The retained raw-root focus captures the table, child Type and declared origin
revisions. Both accessors refuse after supported metadata changes, even on an
empty table. Update discovery, callback and installation share the existing
construction guard. `.update/opt` now reuses `.delta/opt` plus `.apply-delta`, then
recognizes the complete result; `.update` retains its existing default thunk
convention. No-op raw updates return the original root. Callback and custom
whole-table recognition failures expose no partial root and preserve exact causes.
Delta Option shells are copied by the existing protocol. Mutable leaf stability,
valid persistent backend laws and terminating callbacks remain caller premises.

All five style protocols expose `.ref/opt`, `.update/opt`, `.update`, `.delta/opt`,
`.lens` and `.lens/opt`. Receivers expose the corresponding Gerbil methods. The
captured FUN protocol authenticates owners; foreign, consumed and stale metadata
refuse. Discovery captures a delta without consuming its owner. Installation uses
one existing `step`: pure/posh keep the predecessor, mutable/classy retain identity,
and linear consumes it once, including observational no-ops. A focus can operate
on multiple live compatible owners; it is not authority to revive a retired one.
Set membership still has its separate Boolean lens; table key focuses on a set
style observe its backing Unit-valued map.

## Atomic modification and composition

A generic get/transform/set sequence is unsafe for an owned focus: the transform
can reenter and publish a winner before set captures its generation. Table focuses
therefore supply `.modify`; `Lens.modify` delegates to that declared capability,
otherwise deriving modification from the ordinary getter/setter protocol.
`Lens.compose` retains modification delegation at every composition level. The
whole focused modifier consequently runs inside one captured generation; a later
head comparison rejects an older result rather than overwriting a winner.

This guarantees one table owner installation. It does not make two different
mutable owners atomic, roll back callback side effects, or roll back an already
completed nested update if an external outer setter later refuses. Ordinary pure
composition laws require lawful pure outer setters. `revise-focused-ledger`
composes the existing immutable service-slot lens with a linear key focus and
Reader/FUN map: successful complete admission precedes IO; refusal suppresses IO;
explicit retry starts from the retained persistent base, without replaying effects.

## Laws, costs and acceptance

`TableFocus.lean` reuses optional replacement's three lens laws and `styleStep`.
It proves the focused observation, unrelated-key frame, refusal/consumption,
required-absence failure, observational no-op with linear retirement, service frame
and stale-generation rejection. It is a semantic model of the protected protocol,
not a proof of the Gerbil compiler or mutex implementation. Raw persistent lens
laws use extensional views; mutable and linear laws concern the returned successor
observation, not identity of retired/updated references. Whole-table refinements
may reject a well-typed replacement; unrestricted total lens laws are not asserted
for such a partial focus.

Regressions cover both RationalDict and Trie, all five styles, stored false,
value-before-state order, invalid input, metadata invalidation, foreign owners,
late refinement failure and retry, exact Function identity, nonconsuming delta
capture, and a composed reentrant winner. Ninety finite style/key/replacement
combinations exercise get-put, put-get and put-put as observation laws.

No new tree, lock, scheduler or cache is introduced. The checked update path pays
for full recognition at discovery and postcondition, one old-value lookup and at
most one persistent write (no write for a no-op delta). A focus is prepared once
and may be reused. No constant-time admission, destructive storage or host GC
latency claim follows from these laws.
