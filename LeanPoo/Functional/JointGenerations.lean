import LeanPoo.Functional.JointCompetition

/-! Mixed generations may be obsolete by head OR by guard revision.
The laws describe owner-lock order, with native linearization as a premise. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- Concatenation composes complete installation traces without changing attempts. -/
theorem installSequence_append {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (before after : List (Installation (Revision := Revision) Valid)) :
    installSequence current (before ++ after) = installSequence (installSequence current before) after := by
  simp only [installSequence,List.foldl_append]
/-- A finite mixture of head-stale and guard-stale attempts preserves the exact
current bundle; their expected identities need not agree with each other. -/
theorem installSequence_inert {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (attempts : List (Installation (Revision := Revision) Valid))
    (refused : ∀ attempt ∈ attempts, current.id ≠ attempt.receipt.expected ∨ attempt.receipt.staged ≠ attempt.live) :
    installSequence current attempts = current := by
  induction attempts with
  | nil => rfl
  | cons attempt rest ih =>
    have held : installChecked attempt.receipt.expected current attempt.receipt.candidate
        attempt.receipt.staged attempt.live true = current := by
      rcases refused attempt (by simp) with old | drift
      · exact checked_stale _ _ _ _ _ _ old
      · exact metadata_stale _ _ _ _ _ _ drift
    simp only [installSequence,List.foldl_cons]
    rw [held]
    exact ih (fun next member => refused next (by simp [member]))
/-- A current valid receipt can win between arbitrary mixed-generation refused
prefix/tail attempts. Tail refusal is checked against the NEW whole bundle, so
fresh installed identities must avoid every historical expected identity. -/
theorem installSequence_mixed_winner {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (winner : Installation (Revision := Revision) Valid)
    (before after : List (Installation (Revision := Revision) Valid))
    (expected : winner.receipt.expected = current.id) (guards : winner.receipt.staged = winner.live)
    (beforeRefused : ∀ attempt ∈ before, current.id ≠ attempt.receipt.expected ∨ attempt.receipt.staged ≠ attempt.live)
    (afterRefused : ∀ attempt ∈ after, winner.receipt.candidate.id ≠ attempt.receipt.expected ∨ attempt.receipt.staged ≠ attempt.live) :
    installSequence current (before ++ winner :: after) = winner.receipt.candidate := by
  rw [installSequence_append]
  rw [installSequence_inert current before beforeRefused]
  simp only [installSequence,List.foldl_cons]
  change installSequence (installChecked winner.receipt.expected current winner.receipt.candidate
    winner.receipt.staged winner.live true) after = winner.receipt.candidate
  rw [expected,guards,checked_commit]
  exact installSequence_inert winner.receipt.candidate after afterRefused
end LeanPoo.Functional.JointPublication
