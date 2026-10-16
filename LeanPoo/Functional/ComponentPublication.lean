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
/-- Revalidate approval revision identity at the serialized installation point.
Native uses existing object revisions for all registered guards; the abstract
revision type may describe several heterogeneous services together. -/
def installChecked {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool) : Result Snapshot :=
  install expected current candidate (approved && decide (staged = live))
/-- Approval metadata drift refuses even when the publication head is unchanged
and the earlier candidate passed every approval predicate. -/
theorem metadata_stale {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool) (drift : staged ≠ live) :
    installChecked expected current candidate staged live approved = ⟨current,false⟩ := by
  simp [installChecked,drift,refused]
/-- Successful installation requires BOTH current head and the exact registered
approval revision, as well as the original candidate's true joint approval. -/
theorem checked_accepted {Revision : Type} [DecidableEq Revision]
    (expected current candidate : Snapshot) (staged live : Revision) (approved : Bool)
    (success : (installChecked expected current candidate staged live approved).accepted = true) :
    (installChecked expected current candidate staged live approved).head = candidate ∧
      current = expected ∧ approved = true ∧ staged = live := by
  have valid := accepted expected current candidate _ success
  simpa only [installChecked,Bool.and_eq_true,decide_eq_true_eq, and_assoc] using valid
/-- A fresh metadata capture can retry on an unchanged publication. A request
captured before the update remains refused; approval is never silently refreshed. -/
theorem metadata_retry {Revision : Type} [DecidableEq Revision]
    (expected candidate : Snapshot) (old live : Revision) (drift : old ≠ live) :
    installChecked expected
      (installChecked expected expected candidate old live true).head candidate live live true = ⟨candidate,true⟩ := by
  rw [metadata_stale expected expected candidate old live true drift]
  simp [installChecked,install]
/-- Any number of candidates captured at an obsolete approval revision leaves
current publication unchanged, irrespective of their candidate values or order. -/
theorem metadata_batch {Revision : Type} [DecidableEq Revision]
    (expected current : Snapshot) (staged live : Revision) (approved : Bool)
    (candidates : List Snapshot) (drift : staged ≠ live) :
    candidates.foldl (fun head candidate =>
      (installChecked expected head candidate staged live approved).head) current = current := by
  induction candidates generalizing current with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [List.foldl_cons, metadata_stale expected current candidate staged live approved drift]
    exact ih current
end LeanPoo.Functional.ComponentPublication
