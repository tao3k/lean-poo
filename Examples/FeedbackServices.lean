import LeanPoo.Prototype.FeedbackClosure
import LeanPoo.Object.MethodCombination
import Lean.Elab.Tactic.Omega

/-! A capped service-feedback ring, joint approval and existing method policy.
Products correspond to immutable native vectors; no runtime proof is imported. -/
namespace LeanPoo.Examples.FeedbackServices
open Prototype Prototype.Generalized Object.MethodCombination
/-- Three natural allocations, a Boolean joint approval and a shared audit frame. -/
abbrev Raw := (Nat × Nat × Nat) × Bool × String
/-- Current arguments for the existing effective method interpreter. -/
abbrev Row := Nat × Nat × Nat × Nat × Bool
/-- Cooked self exposes the global state and an actual callable method. -/
structure View where
  a : Nat
  b : Nat
  c : Nat
  ready : Bool
  charge : Nat → Except String Nat
/-- Approval gates the primary allocation charge through the existing around policy. -/
def methods : Methods Row (Except String) Nat :=
  {primary := [fun _ row => .ok (row.1 * (row.2.1 + row.2.2.1 + row.2.2.2.1))],
   around := [fun next row => if row.2.2.2.2 then do return 2 * (← next ())
     else .error "approval pending"]}
/-- Raw data stays comparable; callable assembly remains at the cooking boundary. -/
def cook (raw : Raw) : View := ⟨raw.1.1,raw.1.2.1,raw.1.2.2,raw.2.1,fun units =>
  effective methods (fun _ => .error "no primary method") (units,raw.1.1,raw.1.2.1,raw.1.2.2,raw.2.1)⟩
/-- Persistent first allocation replacement preserves siblings, approval and audit. -/
def putA (value : Nat) (raw : Raw) : Raw := ((value,raw.1.2),raw.2)
/-- Persistent second allocation replacement preserves every other component. -/
def putB (value : Nat) (raw : Raw) : Raw := ((raw.1.1,value,raw.1.2.2),raw.2)
/-- Persistent third allocation replacement closes the dependency ring. -/
def putC (value : Nat) (raw : Raw) : Raw := ((raw.1.1,raw.1.2.1,value),raw.2)
/-- Approval is an independently typed focus on the same wider raw carrier. -/
def putReady (value : Bool) (raw : Raw) : Raw := (raw.1,value,raw.2.2)
/-- The first custom lens satisfies all three laws universally. -/
theorem lawsA : LensLaws (fun raw : Raw => raw.1.1) putA := by
  constructor
  · intro raw; rcases raw with ⟨⟨a,b,c⟩,ready,audit⟩; rfl
  · intro raw value; rfl
  · intro raw first second; rfl
/-- The second custom lens is universally lawful. -/
theorem lawsB : LensLaws (fun raw : Raw => raw.1.2.1) putB := by
  constructor
  · intro raw; rcases raw with ⟨⟨a,b,c⟩,ready,audit⟩; rfl
  · intro raw value; rfl
  · intro raw first second; rfl
/-- The third custom lens is universally lawful. -/
theorem lawsC : LensLaws (fun raw : Raw => raw.1.2.2) putC := by
  constructor
  · intro raw; rcases raw with ⟨⟨a,b,c⟩,ready,audit⟩; rfl
  · intro raw value; rfl
  · intro raw first second; rfl
/-- Approval replacement also obeys get-put, put-get and put-put. -/
theorem lawsReady : LensLaws (fun raw : Raw => raw.2.1) putReady := by
  constructor
  · intro raw; rcases raw with ⟨alloc,ready,audit⟩; rfl
  · intro raw value; rfl
  · intro raw first second; rfl
/-- Four COMPLETE component equations read the same preceding cooked global self. -/
def parts (cap : Nat) : List (Generalized.Fragment Raw View) :=
  [⟨Nat,Nat,MonoLens.ofGetSet (fun raw => raw.1.1) putA,fun cap self _ => min cap (1+self.get.b),cap⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet (fun raw => raw.1.2.1) putB,fun cap self _ => min cap (1+self.get.c),cap⟩,
   ⟨Nat,Nat,MonoLens.ofGetSet (fun raw => raw.1.2.2) putC,fun cap self _ => min cap (1+self.get.a),cap⟩,
   ⟨Bool,Nat,MonoLens.ofGetSet (fun raw => raw.2.1) putReady,fun cap self _ =>
      decide (self.get.a = cap ∧ self.get.b = cap ∧ self.get.c = cap),cap⟩]
/-- Zero allocation begins the actual cyclic request. -/
def base : Raw := ((0,0,0),false,"audit")
/-- Exact simultaneous semantics follow from the EXISTING generalized lens compiler. -/
theorem step_eq (cap : Nat) (raw parent : Raw) :
    (fragmentProtocol cook).step (parts cap) raw parent =
    ((min cap (1+raw.1.2.1),min cap (1+raw.1.2.2),min cap (1+raw.1.1)),
     decide (raw.1.1 = cap ∧ raw.1.2.1 = cap ∧ raw.1.2.2 = cap),parent.2.2) := rfl
/-- Three capped rises reach three from ANY natural starting allocation. -/
theorem rise_three (value : Nat) : min 3 (1 + min 3 (1 + min 3 (1+value))) = 3 := by omega
/-- This concrete capped ring settles from ANY typed seed, including approval.
The base controls the independent frame; this is not generic convergence. -/
theorem settles (seed : Raw) : (fragmentProtocol cook).approximate (parts 3) base seed 4 =
    ((3,3,3),true,"audit") := by
  simp only [Protocol.approximate, FiniteFix.iterate, step_eq]
  simp [rise_three, base]
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
