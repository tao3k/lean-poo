import LeanPoo.Functional.ComponentRevision

/-! Abstract serialized installation after candidate construction and joint
approval. It models head selection, not runtime mutex or callback verification. -/
namespace LeanPoo.Functional.ComponentPublication
variable {Snapshot : Type} [DecidableEq Snapshot]
/-- One successful installation or refusal preserves the actual authoritative head. -/
structure Result (Snapshot : Type) where
  head : Snapshot
  accepted : Bool
/-- Installation rechecks the expected head after off-lock construction. Candidate
freshness and approval accuracy are caller premises, independent of this decision. -/
def install (expected current candidate : Snapshot) (approved : Bool) : Result Snapshot :=
  if current = expected ∧ approved = true then ⟨candidate,true⟩ else ⟨current,false⟩
/-- A competing successful publication cannot be overwritten by a stale candidate. -/
theorem stale (expected current candidate : Snapshot) (approved : Bool) (different : current ≠ expected) :
    install expected current candidate approved = ⟨current,false⟩ := by simp [install,different]
/-- Joint refusal retains CURRENT state, which need not be the request's old head. -/
theorem refused (expected current candidate : Snapshot) :
    install expected current candidate false = ⟨current,false⟩ := by simp [install]
/-- Accepted installation selects exactly the candidate and implies both checks. -/
theorem accepted (expected current candidate : Snapshot) (approved : Bool)
    (success : (install expected current candidate approved).accepted = true) :
    (install expected current candidate approved).head = candidate ∧ current = expected ∧ approved = true := by
  unfold install at success ⊢
  split at success
  · rename_i valid; simp [valid]
  · contradiction
/-- The first accepted fresh publication makes a sibling request staged against
its predecessor stale. No claim of automatic rebasing or merging is hidden here. -/
theorem competing (expected first second : Snapshot) (fresh : first ≠ expected) :
    install expected (install expected expected first true).head second true = ⟨first,false⟩ := by
  simp [install,fresh]
/-- Refusal permits retry on the same head after fresh policy preparation, provided
no rival has advanced it. Approval changes alone do not install an old candidate. -/
theorem retry (expected candidate : Snapshot) :
    install expected (install expected expected candidate false).head candidate true = ⟨candidate,true⟩ := by
  simp [install]
end LeanPoo.Functional.ComponentPublication
