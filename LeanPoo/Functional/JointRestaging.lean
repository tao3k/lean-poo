import LeanPoo.Functional.JointGenerations

/-! Explicit successful preparation after an observed installation prefix.
Pending older attempts remain separate; no old receipt is silently rebound. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- A successful pure preparation factory sees exactly the current whole bundle
after the observed prefix. Native construction/admission establishes Valid. -/
def restageAfter {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate})
    (revision : Revision) : Approved (Revision := Revision) Valid :=
  let observed := installSequence current prefixAttempts
  let candidate := prepare observed
  ⟨observed.id,candidate.val,revision,candidate.property⟩
/-- New preparation captures the observed head, not the original request's head. -/
theorem restageAfter_expected {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision) :
    (restageAfter current prefixAttempts prepare revision).expected = (installSequence current prefixAttempts).id := rfl
/-- Newly approved work can install while arbitrary old attempts remain pending,
provided each late attempt is stale against the NEW winner or its own guards. -/
theorem restageAfter_late {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (prefixAttempts late : List (Installation (Revision := Revision) Valid))
    (prepare : (state : Bundle Id Endpoint Policy Head Metadata) → {candidate // Valid candidate}) (revision : Revision)
    (obsolete : ∀ attempt ∈ late,
      (prepare (installSequence current prefixAttempts)).val.id ≠ attempt.receipt.expected ∨
      attempt.receipt.staged ≠ attempt.live) :
    installSequence current (prefixAttempts ++ ⟨restageAfter current prefixAttempts prepare revision,revision⟩ :: late) =
      (prepare (installSequence current prefixAttempts)).val := by
  rw [installSequence_append]
  apply installSequence_mixed_winner (installSequence current prefixAttempts)
    (⟨restageAfter current prefixAttempts prepare revision,revision⟩) [] late rfl rfl
  · simp
  · exact obsolete
end LeanPoo.Functional.JointPublication
