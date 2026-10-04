import LeanPoo.C4.AuditedResolver
import LeanPoo.C4.ValidationInvariant

namespace LeanPoo.C4

/-- A retained failure of the actual audited compilation. The diagnostic is
runtime data; the execution equality is an erased proof. -/
structure RejectedOrder (graph : Graph) (root : String) where
  error : Error
  rejected : linearizeAudited graph root = .error error

/-- Both accepted and rejected outcomes retain their contracts. This executes
the audited compiler once and preserves its original diagnostic on failure. -/
def diagnoseAudited (graph : Graph) (root : String) :
    Except (RejectedOrder graph root) (VerifiedOrder graph root) :=
  match execution : linearizeAudited graph root with
  | .error error => .error ⟨error, execution⟩
  | .ok output => .ok ⟨output, linearizeAudited_accepts_mode execution true,
      linearizeAudited_graph_sound execution⟩

/-- Forgetting proofs recovers the exact audited result, including errors. -/
theorem diagnoseAudited_projection :
    ((diagnoseAudited graph root).mapError (·.error)).map (·.output) =
      linearizeAudited graph root := by
  unfold diagnoseAudited
  split <;> simp_all [Except.mapError, Except.map]

/-- A rejected audited execution excludes every successful verified order,
without assuming declaration uniqueness or equating diagnostics. -/
theorem RejectedOrder.noVerified (receipt : RejectedOrder graph root) :
    ¬ Nonempty (VerifiedOrder graph root) := by
  rintro ⟨order⟩
  have accepted := linearizeAudited_checked_complete order.accepted
  rw [receipt.rejected] at accepted
  cases accepted

/-- Checked compilation also rejects, but its diagnostic may differ. -/
theorem RejectedOrder.checkedRejected (receipt : RejectedOrder graph root) :
    ∃ error, linearizeChecked graph root = .error error := by
  cases execution : linearizeChecked graph root with
  | error error => exact ⟨error, rfl⟩
  | ok output =>
    have accepted := linearizeAudited_checked_complete execution
    rw [receipt.rejected] at accepted
    cases accepted

/-- Reachable declaration uniqueness closes the validation boundary between
finite graph evidence and actual audited successful execution. -/
theorem linearizeAudited_graph_iff (unique : LinearizeState.ReachableUnique graph root) :
    linearizeAudited graph root = .ok output ↔ ∃ tail, GraphTrace graph root output tail := by
  constructor
  · exact linearizeAudited_graph_sound
  · rintro ⟨tail, trace⟩
    exact linearizeAudited_checked_complete (linearizeChecked_unique_complete trace unique)

/-- With reachable uniqueness, an actual failure rules out every original
finite graph derivation. The premise is needed for validation failures. -/
theorem RejectedOrder.noGraphTrace (receipt : RejectedOrder graph root)
    (unique : LinearizeState.ReachableUnique graph root) :
    ¬ ∃ output tail, GraphTrace graph root output tail := by
  rintro ⟨output, tail, trace⟩
  have accepted := (linearizeAudited_graph_iff unique).mpr ⟨tail, trace⟩
  rw [receipt.rejected] at accepted
  cases accepted

/-- Exact semantic rejection under reachable uniqueness. No claim about the
particular error constructor or the checked compiler's error payload follows. -/
theorem linearizeAudited_rejection_iff (unique : LinearizeState.ReachableUnique graph root) :
    (∃ error, linearizeAudited graph root = .error error) ↔
      ¬ ∃ output tail, GraphTrace graph root output tail := by
  constructor
  · rintro ⟨error, rejected⟩
    exact (RejectedOrder.noGraphTrace ⟨error, rejected⟩ unique)
  · intro absent
    cases execution : linearizeAudited graph root with
    | error error => exact ⟨error, rfl⟩
    | ok output =>
      obtain ⟨tail, trace⟩ := linearizeAudited_graph_sound execution
      exact False.elim (absent ⟨output, tail, trace⟩)

end LeanPoo.C4
