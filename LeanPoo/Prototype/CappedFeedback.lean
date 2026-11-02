import LeanPoo.Prototype.FeedbackClosure
import LeanPoo.Object.MethodCombination
import Lean.Elab.Tactic.Omega

/-! Reusable capped feedback ring with immutable raw storage and callable cooking.
The finite cap-three convergence theorem is separate from generic admission. -/
namespace LeanPoo.Prototype.Generalized.CappedFeedback
open LeanPoo.Prototype LeanPoo.Prototype.Generalized LeanPoo.Object.MethodCombination
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
end LeanPoo.Prototype.Generalized.CappedFeedback
