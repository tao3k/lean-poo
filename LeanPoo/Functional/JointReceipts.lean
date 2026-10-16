import LeanPoo.Functional.JointInstallation

/-! Finite sequences of already admitted whole bundles recheck guards on EACH
installation. Native opaque receipts implement the certified-candidate premise. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
/-- An admitted candidate with its captured source and registered guard revision.
The proof expresses a caller-specified validity predicate, not a native proof token. -/
structure Approved (Valid : Bundle Id Endpoint Policy Head Metadata → Prop) where
  expected : Id
  candidate : Bundle Id Endpoint Policy Head Metadata
  staged : Revision
  valid : Valid candidate
/-- The environment supplies the guard revision observed at this installation;
it can differ for each receipt even when several share the same proposed policy. -/
structure Installation (Valid : Bundle Id Endpoint Policy Head Metadata → Prop) where
  receipt : Approved (Revision := Revision) Valid
  live : Revision
variable [DecidableEq Id] [DecidableEq Revision]
/-- Fold the existing checked whole-bundle decision in explicit attempt order.
This models a serialized trace, not atomicity across the whole sequence. -/
def installSequence {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (attempts : List (Installation (Revision := Revision) Valid)) :=
  attempts.foldl (fun state attempt => installChecked attempt.receipt.expected state
    attempt.receipt.candidate attempt.receipt.staged attempt.live true) current
/-- Whole-bundle validity survives arbitrary receipt ordering and guard changes;
each candidate's earlier validity and the current bundle's validity are premises. -/
theorem installSequence_valid {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (attempts : List (Installation (Revision := Revision) Valid))
    (old : Valid current) : Valid (installSequence current attempts) := by
  induction attempts generalizing current with
  | nil => exact old
  | cons attempt rest ih =>
    apply ih
    change Valid (installChecked attempt.receipt.expected current attempt.receipt.candidate
      attempt.receipt.staged attempt.live true)
    rcases checked_whole attempt.receipt.expected current attempt.receipt.candidate
      attempt.receipt.staged attempt.live true with selected | retained
    · rw [selected]; exact attempt.receipt.valid
    · rw [retained]; exact old
/-- Arbitrarily many receipts captured at older heads retain the exact current
bundle, independent of shared guard drift, candidate values or ordering. -/
theorem installSequence_stale {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (attempts : List (Installation (Revision := Revision) Valid))
    (obsolete : ∀ attempt ∈ attempts, current.id ≠ attempt.receipt.expected) :
    installSequence current attempts = current := by
  induction attempts with
  | nil => rfl
  | cons attempt rest ih =>
    simp only [installSequence,List.foldl_cons]
    rw [checked_stale attempt.receipt.expected current attempt.receipt.candidate
      attempt.receipt.staged attempt.live true (obsolete attempt (by simp))]
    exact ih (fun next member => obsolete next (by simp [member]))
/-- Refused guard checks leave later independently approved siblings fresh; this
also holds after any prefix that changed SCCs or current shared metadata. -/
theorem installSequence_drift_between {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (before after : List (Installation (Revision := Revision) Valid))
    (attempt : Installation (Revision := Revision) Valid) (drift : attempt.receipt.staged ≠ attempt.live) :
    installSequence current (before ++ attempt :: after) = installSequence current (before ++ after) := by
  simp only [installSequence,List.foldl_append,List.foldl_cons]
  rw [metadata_stale attempt.receipt.expected _ attempt.receipt.candidate attempt.receipt.staged attempt.live true drift]
end LeanPoo.Functional.JointPublication
