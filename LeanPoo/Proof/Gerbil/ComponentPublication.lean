import Std

namespace ComponentPublication

structure Snapshot (Graph Metadata : Type) where
  graph : Graph
  metadata : Metadata

structure State (Graph Metadata : Type) where
  owner : Nat
  epoch : Nat
  head : Snapshot Graph Metadata
  version : Nat → Nat

structure Ticket where
  owner : Nat
  epoch : Nat
  family : Nat
  version : Nat

variable {G M : Type}

def issue (s : State G M) (family : Nat) : Ticket :=
  ⟨s.owner, s.epoch, family, s.version family⟩

def Current (s : State G M) (t : Ticket) : Prop :=
  t.owner = s.owner ∧ t.epoch = s.epoch ∧ t.version = s.version t.family

instance (s : State G M) (t : Ticket) : Decidable (Current s t) := by
  unfold Current
  infer_instance

theorem issue_current (s : State G M) (family : Nat) : Current s (issue s family) :=
  ⟨rfl, rfl, rfl⟩

-- After authenticated restage the predecessor cannot regain its version,
-- even if later preparation or approval refuses the replacement.
def advance (s : State G M) (family : Nat) : State G M :=
  { s with version := fun f => if f = family then s.version f + 1 else s.version f }

theorem advance_retires (s : State G M) (t : Ticket) (live : Current s t) :
    ¬ Current (advance s t.family) t := by
  intro renewed
  have version := renewed.2.2
  simp [advance, live.2.2] at version

theorem advance_keeps_sibling (s : State G M) (t : Ticket) (family : Nat)
    (separate : t.family ≠ family) (live : Current s t) :
    Current (advance s family) t := by
  exact ⟨live.1, live.2.1, by simpa [advance, separate] using live.2.2⟩

-- The flag stands for the actual independent final guard/currentness
-- decisions inside the lock, not the verdict from the author callback.
def commit (s : State G M) (t : Ticket) (candidate : Snapshot G M) (approved : Bool) :
    State G M :=
  if Current s t ∧ approved = true then {s with epoch := s.epoch + 1, head := candidate} else s

theorem reject_unchanged (s : State G M) (t : Ticket) (candidate : Snapshot G M) (approved : Bool)
    (reject : ¬ (Current s t ∧ approved = true)) : commit s t candidate approved = s := by
  simp [commit, reject]

theorem install_whole (s : State G M) (t : Ticket) (candidate : Snapshot G M)
    (live : Current s t) : (commit s t candidate true).head = candidate := by
  simp [commit, live]

theorem old_epoch_rejected (s : State G M) (winner rival : Ticket) (candidate : Snapshot G M)
    (liveWinner : Current s winner) (liveRival : Current s rival) :
    ¬ Current (commit s winner candidate true) rival := by
  intro stale
  have epoch := stale.2.1
  simp [commit, liveWinner, liveRival.2.1] at epoch

theorem failed_replacement_cannot_restore (s : State G M) (old : Ticket)
    (newCandidate oldCandidate : Snapshot G M) (live : Current s old) :
    let advanced := advance s old.family
    let denied := commit advanced (issue advanced old.family) newCandidate false
    denied.head = s.head ∧ commit denied old oldCandidate true = denied := by
  dsimp only
  rw [reject_unchanged (reject := by simp)]
  exact ⟨rfl, reject_unchanged _ _ _ _ (fun h => advance_retires s old live h.1)⟩

-- The real fault is plausible: restage leaves both owner and installed epoch
-- unchanged. Consequently a final check of only those fields accepts `old`.
theorem head_only_misses_restage (s : State G M) (old : Ticket) (live : Current s old) :
    let advanced := advance s old.family
    old.owner = advanced.owner ∧ old.epoch = advanced.epoch ∧ ¬ Current advanced old :=
  ⟨live.1, live.2.1, advance_retires s old live⟩

-- Live read revalidation has no family ticket. It still rejects a changed
-- publication identity or independent source/approval evidence failure.
def release (s : State G M) (owner epoch : Nat) (guards : Bool) (result : A) : Option A :=
  if owner = s.owner ∧ epoch = s.epoch ∧ guards = true then some result else none

theorem reader_after_commit_rejects (s : State G M) (t : Ticket) (next : Snapshot G M)
    (live : Current s t) (guards : Bool) (result : A) :
    release (commit s t next true) s.owner s.epoch guards result = none := by
  simp [release, commit, live]

theorem reader_with_revoked_guards_rejects (s : State G M) (result : A) :
    release s s.owner s.epoch false result = none := by simp [release]

#print axioms failed_replacement_cannot_restore
#print axioms head_only_misses_restage
#print axioms install_whole
#print axioms old_epoch_rejected
#print axioms reader_after_commit_rejects

end ComponentPublication
