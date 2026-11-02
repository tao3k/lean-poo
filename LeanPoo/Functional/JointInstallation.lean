import LeanPoo.Functional.JointPublication

/-! Recheck registered approval revisions after joint admission and before
whole-bundle installation. Native revision accuracy remains a premise. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- Reuse the component installation decision for one whole heterogeneous bundle;
the revision carrier can encode all old/proposed policies and source guards. -/
def installChecked (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (staged live : Revision) (approved : Bool) :=
  if (ComponentPublication.installChecked expected current.id candidate.id staged live approved).accepted
    then candidate else current
/-- The reused acceptance decision requires the expected head, earlier true
approval and unchanged complete registered revision; bundle equality alone does
not imply acceptance when a candidate happens to equal the current bundle. -/
theorem checked_requirements (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (staged live : Revision) (approved : Bool)
    (success : (ComponentPublication.installChecked expected current.id candidate.id staged live approved).accepted = true) :
    current.id = expected ∧ approved = true ∧ staged = live := by
  exact (ComponentPublication.checked_accepted expected current.id candidate.id staged live approved success).2
/-- Every outcome retains a whole bundle, including when approval drifts. -/
theorem checked_whole (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (staged live : Revision) (approved : Bool) :
    installChecked expected current candidate staged live approved = candidate ∨
    installChecked expected current candidate staged live approved = current := by
  unfold installChecked; split <;> simp
/-- Earlier successful joint approval cannot authorize changed registered metadata. -/
theorem metadata_stale (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (staged live : Revision) (approved : Bool) (drift : staged ≠ live) :
    installChecked expected current candidate staged live approved = current := by
  simp [installChecked,ComponentPublication.metadata_stale expected current.id candidate.id staged live approved drift]
/-- A rival publication wins even if the late candidate's metadata is still current. -/
theorem checked_stale (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (staged live : Revision) (approved : Bool) (different : current.id ≠ expected) :
    installChecked expected current candidate staged live approved = current := by
  simp [installChecked,ComponentPublication.installChecked,
    ComponentPublication.stale expected current.id candidate.id _ different]
/-- Exact head, exact guards and earlier joint approval install the entire candidate. -/
theorem checked_commit (current candidate : Bundle Id Endpoint Policy Head Metadata) (live : Revision) :
    installChecked current.id current candidate live live true = candidate := by
  simp [installChecked,ComponentPublication.installChecked,ComponentPublication.install]
/-- Fresh staging after drift can publish from the unchanged current head;
the old receipt itself stays invalid and is never silently refreshed. -/
theorem metadata_retry (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (old live : Revision) (drift : old ≠ live) :
    installChecked current.id (installChecked current.id current candidate old live true)
      candidate live live true = candidate := by
  rw [metadata_stale current.id current candidate old live true drift]
  exact checked_commit current candidate live
end LeanPoo.Functional.JointPublication
