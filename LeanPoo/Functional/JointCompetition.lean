import LeanPoo.Functional.JointReceipts

/-! Concurrent native installations reduce to a serialized owner-lock order.
These laws cover that order; the mutex/runtime implementation is a premise. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy Revision : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
  [DecidableEq Id] [DecidableEq Revision]
/-- The first current, guard-valid receipt wins over ANY finite tail captured at
its predecessor. A winner must have a fresh installed identity. -/
theorem installSequence_winner {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (first : Installation (Revision := Revision) Valid)
    (rest : List (Installation (Revision := Revision) Valid))
    (expected : first.receipt.expected = current.id) (guards : first.receipt.staged = first.live)
    (fresh : first.receipt.candidate.id ≠ current.id)
    (siblings : ∀ attempt ∈ rest, attempt.receipt.expected = current.id) :
    installSequence current (first :: rest) = first.receipt.candidate := by
  simp only [installSequence,List.foldl_cons]
  change installSequence (installChecked first.receipt.expected current first.receipt.candidate
    first.receipt.staged first.live true) rest = first.receipt.candidate
  rw [expected,guards,checked_commit]
  exact installSequence_stale first.receipt.candidate rest (fun attempt member => by
    simpa [siblings attempt member] using fresh)
/-- Either possible two-worker lock order retains exactly its first whole winner;
this does not choose a scheduler order or assume deterministic winner identity. -/
theorem competing_orders {Valid : Bundle Id Endpoint Policy Head Metadata → Prop}
    (current : Bundle Id Endpoint Policy Head Metadata) (a b : Installation (Revision := Revision) Valid)
    (ea : a.receipt.expected = current.id) (eb : b.receipt.expected = current.id)
    (ga : a.receipt.staged = a.live) (gb : b.receipt.staged = b.live)
    (fa : a.receipt.candidate.id ≠ current.id) (fb : b.receipt.candidate.id ≠ current.id) :
    installSequence current [a,b] = a.receipt.candidate ∧
    installSequence current [b,a] = b.receipt.candidate := by
  constructor
  · exact installSequence_winner current a [b] ea ga fa
      (by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact eb)
  · exact installSequence_winner current b [a] eb gb fb
      (by intro x hx; simp only [List.mem_singleton] at hx; subst x; exact ea)
/-- The same approved receipt cannot be accepted twice after a fresh installation:
the second serialized decision reports refusal even with unchanged guard values. -/
theorem receipt_replay_refused (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (live : Revision) (fresh : candidate.id ≠ current.id) :
    (ComponentPublication.installChecked current.id candidate.id candidate.id live live true).accepted = false := by
  simp [ComponentPublication.installChecked,ComponentPublication.stale _ _ _ _ fresh]
end LeanPoo.Functional.JointPublication
