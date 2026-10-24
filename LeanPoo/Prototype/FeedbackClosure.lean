import LeanPoo.Prototype.GeneralizedClosure

/-! Controlled cyclic component equations. One actual wider-raw fixed point and
every component residual are required; no unrestricted convergence is asserted. -/
namespace LeanPoo.Prototype.Generalized
variable {Raw Cooked : Type}
/-- A complete component equation uses the same cooked final self and ORIGINAL
base. Normalize unrelated fields through the same lens instead of comparing a
heterogeneous focus with an invented equality oracle. -/
def Fragment.feedbackEquation (part : Fragment Raw Cooked) (cook : Raw → Cooked) (base raw : Raw) : Prop :=
  part.compile (Thunk.mk fun _ => cook raw) (Thunk.mk fun _ => base) =
    part.focus.modify (fun _ => part.focus.view raw) base
/-- Component residuals use only the existing decidable raw equality. -/
instance Fragment.feedbackEquationDecidable [DecidableEq Raw] (part : Fragment Raw Cooked)
    (cook : Raw → Cooked) (base raw : Raw) : Decidable (part.feedbackEquation cook base raw) := by
  unfold Fragment.feedbackEquation
  infer_instance
/-- With the lens's actual replacement-view law, normalized residual equality
implies the component's produced value equals the final projected value. -/
theorem Fragment.feedbackEquation_view (part : Fragment Raw Cooked) (cook : Raw → Cooked) (base raw : Raw)
    (law : ∀ source value, part.focus.view (part.focus.modify (fun _ => value) source) = value)
    (equation : part.feedbackEquation cook base raw) :
    part.focus.view (part.compile (Thunk.mk fun _ => cook raw) (Thunk.mk fun _ => base)) = part.focus.view raw :=
  (congrArg part.focus.view equation).trans (law base _)
/-- Decidable whole-raw equality checks every component, including overlaps that
could cancel in the complete assembled transition. -/
def feedbackValid [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base raw : Raw) : Bool := parts.all (fun part => decide (part.feedbackEquation cook base raw))
/-- Successful residual checking establishes each declared component equation. -/
theorem feedbackValid_sound [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base raw : Raw) (accepted : feedbackValid parts cook base raw = true)
    (part : Fragment Raw Cooked) (member : part ∈ parts) : part.feedbackEquation cook base raw := by
  exact of_decide_eq_true ((List.all_eq_true.mp accepted) part member)
/-- Reuse bounded actual-raw search, then reject any unsatisfied component equation.
This is a conservative admission procedure, not a solver for all recursive knots. -/
def closeFeedback [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) : Except String (BoundedClosed (fragmentProtocol cook) parts base) :=
  match closeWithin (fragmentProtocol cook) parts base seed budget with
  | .error message => .error message
  | .ok result => if feedbackValid parts cook base result.closed.raw then .ok result
      else .error "feedback component equation refused"
/-- Feedback admission preserves the original search receipt and seed provenance. -/
theorem closeFeedback_search [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : closeFeedback parts cook base seed budget = .ok result) :
    closeWithin (fragmentProtocol cook) parts base seed budget = .ok result := by
  unfold closeFeedback at accepted
  cases found : closeWithin (fragmentProtocol cook) parts base seed budget with
  | error message => simp [found] at accepted
  | ok previous =>
    simp only [found] at accepted
    split at accepted
    · cases accepted; rfl
    · contradiction
/-- Every component, not only the assembled program, holds at an accepted result. -/
theorem closeFeedback_equations [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : closeFeedback parts cook base seed budget = .ok result)
    (part : Fragment Raw Cooked) (member : part ∈ parts) : part.feedbackEquation cook base result.closed.raw := by
  unfold closeFeedback at accepted
  cases found : closeWithin (fragmentProtocol cook) parts base seed budget with
  | error message => simp [found] at accepted
  | ok previous =>
    simp only [found] at accepted
    split at accepted
    · rename_i valid
      cases accepted
      exact feedbackValid_sound parts cook base result.closed.raw valid part member
    · contradiction
/-- The returned wider raw equation is the actual fixed-point equation. -/
theorem closeFeedback_fixed (result : BoundedClosed (fragmentProtocol cook) parts base) :
    (fragmentProtocol cook).step parts result.closed.raw base = result.closed.raw := result.closed.fixed
/-- Accepted feedback closure stays within its raw search transition budget. -/
theorem closeFeedback_bound [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : closeFeedback parts cook base seed budget = .ok result) : result.steps ≤ budget :=
  closeWithin_bound _ _ _ _ _ _ (closeFeedback_search parts cook base seed budget result accepted)
/-- An accepted raw result lies on the actual original-seed unfolding. -/
theorem closeFeedback_reached [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : closeFeedback parts cook base seed budget = .ok result) :
    ∃ depth, result.steps = depth+1 ∧ (fragmentProtocol cook).approximate parts base seed depth = result.closed.raw :=
  closeWithin_reached _ _ _ _ _ _ (closeFeedback_search parts cook base seed budget result accepted)
/-- Every later original-seed unfolding remains at the accepted feedback state. -/
theorem closeFeedback_forever [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (budget : Nat) (result : BoundedClosed (fragmentProtocol cook) parts base)
    (accepted : closeFeedback parts cook base seed budget = .ok result) (extra : Nat) :
    ∃ depth, result.steps = depth+1 ∧ (fragmentProtocol cook).approximate parts base seed (depth+extra) = result.closed.raw :=
  closeWithin_forever _ _ _ _ _ _ (closeFeedback_search parts cook base seed budget result accepted) extra
/-- Conditional completeness requires BOTH finite convergence and every final
component equation. Cancellation in assembled inheritance alone is insufficient. -/
theorem closeFeedback_complete [DecidableEq Raw] (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked)
    (base seed : Raw) (depth : Nat)
    (stable : (fragmentProtocol cook).step parts ((fragmentProtocol cook).approximate parts base seed depth) base =
      (fragmentProtocol cook).approximate parts base seed depth)
    (valid : feedbackValid parts cook base ((fragmentProtocol cook).approximate parts base seed depth) = true) :
    ∃ result, closeFeedback parts cook base seed (depth+1) = .ok result := by
  obtain ⟨result,found⟩ := closeWithin_complete (fragmentProtocol cook) parts base seed depth stable
  obtain ⟨before,count,reached⟩ := closeWithin_reached _ _ _ _ _ _ found
  have bound := closeWithin_bound _ _ _ _ _ _ found
  rw [count] at bound
  have before_le : before ≤ depth := Nat.le_of_add_le_add_right bound
  have adjacent : (fragmentProtocol cook).approximate parts base seed before =
      (fragmentProtocol cook).approximate parts base seed (before+1) := by
    rw [Protocol.approximate_succ,reached,result.closed.fixed]
  have later := (fragmentProtocol cook).stable parts base seed before adjacent (depth-before)
  rw [Nat.add_sub_of_le before_le, reached] at later
  rw [later] at valid
  exact ⟨result, by simp [closeFeedback,found,valid]⟩
/-- Explicit component frame laws preserve the original base audit at a fixed point. -/
theorem feedback_frame (parts : List (Fragment Raw Cooked)) (cook : Raw → Cooked) (frame : Raw → Frame)
    (law : ∀ part ∈ parts, ∀ raw value, frame (part.focus.modify (fun _ => value) raw) = frame raw)
    (base : Raw) (result : BoundedClosed (fragmentProtocol cook) parts base) :
    frame result.closed.raw = frame base := by
  rw [← result.closed.fixed]
  exact fragments_frame parts cook frame law _ _
end LeanPoo.Prototype.Generalized
