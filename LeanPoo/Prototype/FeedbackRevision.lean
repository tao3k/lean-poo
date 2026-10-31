import LeanPoo.Prototype.FeedbackClosure

/-! A previous raw value seeds a NEW feedback closure and current joint approval.
Source guards and opaque exceptions remain separate native controls. -/
namespace LeanPoo.Prototype.Generalized
variable {Raw Cooked : Type}
/-- Old raw is only a seed. Recompute revised equations before strict Boolean
joint approval; neither old fixedness nor old approval is assumed reusable. -/
def reviseFeedback [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool) :
    Except String (BoundedClosed (fragmentProtocol cook) parts base) :=
  match closeFeedback parts cook base previous budget with
  | .error message => .error message
  | .ok candidate => if admit previous candidate.closed.raw then .ok candidate
      else .error "joint feedback approval refused"
/-- Admission preserves the actual NEW closure from the previous raw seed. -/
theorem reviseFeedback_closed [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool)
    (candidate : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : reviseFeedback parts cook base previous budget admit = .ok candidate) :
    closeFeedback parts cook base previous budget = .ok candidate := by
  unfold reviseFeedback at accepted
  cases found : closeFeedback parts cook base previous budget with
  | error message => simp [found] at accepted
  | ok next =>
    simp only [found] at accepted
    split at accepted
    · cases accepted; rfl
    · contradiction
/-- Every accepted revision satisfies current joint approval on that exact raw. -/
theorem reviseFeedback_approved [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool)
    (candidate : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : reviseFeedback parts cook base previous budget admit = .ok candidate) :
    admit previous candidate.closed.raw = true := by
  unfold reviseFeedback at accepted
  cases found : closeFeedback parts cook base previous budget with
  | error message => simp [found] at accepted
  | ok next =>
    simp only [found] at accepted
    split at accepted
    · rename_i approved
      cases accepted; exact approved
    · contradiction
/-- Revised component equations are established by new admission, not old metadata. -/
theorem reviseFeedback_equations [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool)
    (candidate : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : reviseFeedback parts cook base previous budget admit = .ok candidate)
    (part : Fragment Raw Cooked) (member : part ∈ parts) : part.feedbackEquation cook base candidate.closed.raw :=
  closeFeedback_equations _ _ _ _ _ _ (reviseFeedback_closed _ _ _ _ _ _ _ accepted) part member
/-- The new raw comes from actual unfolding of the PREVIOUS raw under revised equations. -/
theorem reviseFeedback_reached [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool)
    (candidate : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : reviseFeedback parts cook base previous budget admit = .ok candidate) :
    ∃ depth, candidate.steps = depth+1 ∧
      (fragmentProtocol cook).approximate parts base previous depth = candidate.closed.raw :=
  closeFeedback_reached _ _ _ _ _ _ (reviseFeedback_closed _ _ _ _ _ _ _ accepted)
/-- Warm starting never removes the fresh raw-transition budget bound. -/
theorem reviseFeedback_bound [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base previous : Raw) (budget : Nat) (admit : Raw → Raw → Bool)
    (candidate : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : reviseFeedback parts cook base previous budget admit = .ok candidate) : candidate.steps ≤ budget :=
  closeFeedback_bound _ _ _ _ _ _ (reviseFeedback_closed _ _ _ _ _ _ _ accepted)
end LeanPoo.Prototype.Generalized
