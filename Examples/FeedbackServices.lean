import LeanPoo.Prototype.CappedFeedback

/-! Executable capped-ring controls reuse the shared construction and its laws. -/
namespace LeanPoo.Examples.FeedbackServices
open Prototype Prototype.Generalized Object.MethodCombination
open Prototype.Generalized.CappedFeedback
/-- Explicit frame laws retain the base audit for ANY accepted ring fixed point. -/
theorem audit_preserved (cap : Nat) (result : BoundedClosed (fragmentProtocol cook) (parts cap) base) :
    result.closed.raw.2.2 = base.2.2 := by
  apply feedback_frame (parts cap) cook (fun raw => raw.2.2)
  intro part member raw value
  simp only [parts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl
/-- Finite convergence AND component residuals guarantee bounded admission from
EVERY typed seed for this ring, not merely a hand-picked execution trace. -/
theorem closes (seed : Raw) : ∃ result, closeFeedback (parts 3) cook base seed 5 = .ok result := by
  apply closeFeedback_complete (parts 3) cook base seed 4
  · rw [settles]; rfl
  · rw [settles]; rfl
/-- Five raw steps include the final equality verification and joint approval lag. -/
example : (closeFeedback (parts 3) cook base base 5).map (fun result => (result.steps,result.closed.raw)) =
    .ok (5,((3,3,3),true,"audit")) := rfl
/-- Method policy consumes the actually accepted cyclic result. -/
example : (closeFeedback (parts 3) cook base base 5).map (fun result => result.closed.interface.charge 2) =
    .ok (.ok 36) := rfl
/-- A fresh cap revision recomputes the feedback ring with its own adequate budget. -/
example : (closeFeedback (parts 4) cook base base 6).map (fun result => result.closed.interface.charge 2) =
    .ok (.ok 48) := rfl
/-- Allocations alone settle before joint approval; early consumption still refuses. -/
example : ((fragmentProtocol cook).observe (parts 3) base base 3).charge 2 = .error "approval pending" := rfl
/-- An insufficient budget retains the exact old publication, not a partial ring. -/
example (old : Raw) : publishClosed old ((closeFeedback (parts 3) cook base base 4).map (fun r => r.closed.raw)) = old := rfl
/-- Two overlapping incremental contributions can cancel in the assembled program. -/
def cancelling : List (Generalized.Fragment Int Int) :=
  [⟨Int,Int,MonoLens.ofGetSet id (fun v _ => v),fun amount _ parent => amount+parent.get,1⟩,
   ⟨Int,Int,MonoLens.ofGetSet id (fun v _ => v),fun amount _ parent => amount+parent.get,-1⟩]
/-- Whole assembled equality alone would accept the cancelling contributions. -/
example : (closeWithin (fragmentProtocol id) cancelling 0 0 1).map (fun r => r.closed.raw) = .ok 0 := rfl
/-- Neither independent component equation holds, so feedback admission rejects. -/
example : (closeFeedback cancelling id 0 0 1).map (fun r => r.closed.raw) =
    .error "feedback component equation refused" := rfl
/-- A Boolean oscillator is not certified by finite repetition or budget exhaustion. -/
example : (closeFeedback [⟨Bool,Unit,MonoLens.ofGetSet id (fun v _ => v),fun _ self _ => !self.get,()⟩]
    id false false 6).map (fun r => r.closed.raw) = .error "closure budget exhausted" := rfl
#print axioms settles
#print axioms lawsA
#print axioms lawsB
#print axioms lawsC
#print axioms lawsReady
#print axioms closeFeedback_search
#print axioms closeFeedback_equations
#print axioms closeFeedback_bound
#print axioms closeFeedback_reached
#print axioms feedback_frame
#print axioms audit_preserved
#print axioms Fragment.feedbackEquation_view
#print axioms closeFeedback_forever
#print axioms closeWithin_complete
#print axioms closeFeedback_complete
#print axioms closes
end LeanPoo.Examples.FeedbackServices
