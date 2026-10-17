import LeanPoo.Functional.JointRestaging

/-! Independent successful factories may observe equal or different prefixes.
The laws use whole snapshots and existing checked installation, not a scheduler. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- Two coordinators preparing from the same observed prefix both capture that
head. Either serialized lock order selects exactly its first complete candidate. -/
theorem restageAfter_competing {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts : List (Installation (Revision := Revision) Valid))
    (a b : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (ra rb : Revision)
    (fa : (a (installSequence current prefixAttempts)).val.id ≠ (installSequence current prefixAttempts).id)
    (fb : (b (installSequence current prefixAttempts)).val.id ≠ (installSequence current prefixAttempts).id) :
    let x : Installation (Revision := Revision) Valid := ⟨restageAfter current prefixAttempts a ra,ra⟩
    let y : Installation (Revision := Revision) Valid := ⟨restageAfter current prefixAttempts b rb,rb⟩
    installSequence (installSequence current prefixAttempts) [x,y] = x.receipt.candidate ∧
    installSequence (installSequence current prefixAttempts) [y,x] = y.receipt.candidate := by
  exact competing_orders _ _ _ rfl rfl rfl rfl fa fb
/-- A coordinator whose capture is superseded must not install its old candidate,
even if its local/joint checks and registered revisions are still true/current. -/
theorem restageAfter_superseded {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (oldPrefix newPrefix : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (staged live : Revision)
    (advanced : (installSequence current newPrefix).id ≠ (installSequence current oldPrefix).id) :
    installChecked (restageAfter current oldPrefix prepare staged).expected (installSequence current newPrefix)
      (restageAfter current oldPrefix prepare staged).candidate staged live true = installSequence current newPrefix := by
  exact checked_stale _ _ _ _ _ _ advanced
/-- Shared approval failures do not change the captured preparation source;
explicit NEW preparation after such failures observes the same whole current head. -/
theorem restageAfter_refused {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts denied : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision)
    (refused : ∀ attempt ∈ denied, (installSequence current prefixAttempts).id ≠ attempt.receipt.expected ∨
      attempt.receipt.staged ≠ attempt.live) :
    restageAfter current (prefixAttempts ++ denied) prepare revision = restageAfter current prefixAttempts prepare revision := by
  have same : installSequence current (prefixAttempts ++ denied) = installSequence current prefixAttempts := by
    rw [installSequence_append,installSequence_inert _ denied refused]
  exact congrArg (fun observed =>
    (⟨observed.id,(prepare observed).val,revision,(prepare observed).property⟩ : Approved (Revision := Revision) Valid)) same
end LeanPoo.Functional.JointPublication
