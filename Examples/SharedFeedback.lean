import LeanPoo.Prototype.FeedbackRevision
import LeanPoo.Object.MethodCombination

/-! Shared quota, two cyclic service branches, warm revision and joint approval.
Products correspond to immutable vectors; native source guards are separate controls. -/
namespace LeanPoo.Examples.SharedFeedback
open Prototype Prototype.Generalized Object.MethodCombination
/-- One shared dependency, two service pairs, readiness and an independent audit. -/
abbrev Raw := Nat × (Nat × Nat) × (Nat × Nat) × Bool × String
/-- Existing method arguments keep units/allocation/factor/readiness explicit. -/
abbrev Row := Nat × Nat × Nat × Bool
/-- Cooked global self carries dependency fields and heterogeneous service methods. -/
structure View where
  quota : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  ready : Bool
  left : Nat → Except String Nat
  right : Nat → Except String Nat
/-- Standard primary/around policy gates fresh charges on joint readiness. -/
def methods : Methods Row (Except String) Nat :=
  {primary := [fun _ row => .ok (row.1 * row.2.1)],
   around := [fun next row => if row.2.2.2 then do return row.2.2.1 * (← next ())
     else .error "joint approval pending"]}
/-- One common policy binds current units, allocation and per-service factor. -/
def charge (units allocation factor : Nat) (ready : Bool) : Except String Nat :=
  effective methods (fun _ => .error "no primary method") (units,allocation,factor,ready)
/-- Both callable services consume the same immutable cooked global state. -/
def cook (raw : Raw) : View :=
  ⟨raw.1,raw.2.1.1,raw.2.1.2,raw.2.2.1.1,raw.2.2.1.2,raw.2.2.2.1,
   fun units => charge units (raw.2.1.1+raw.2.1.2) 2 raw.2.2.2.1,
   fun units => charge units (raw.2.2.1.1+raw.2.2.1.2) 3 raw.2.2.2.1⟩
/-- Persistent shared quota replacement preserves both service branches. -/
def putQuota (value : Nat) (raw : Raw) : Raw := (value,raw.2)
/-- Persistent left-first replacement retains the shared dependency and other branch. -/
def putA (value : Nat) (raw : Raw) : Raw := (raw.1,(value,raw.2.1.2),raw.2.2)
/-- Persistent left-second replacement carries one edge across the service boundary. -/
def putB (value : Nat) (raw : Raw) : Raw := (raw.1,(raw.2.1.1,value),raw.2.2)
/-- Persistent right-first replacement keeps sibling and frame intact. -/
def putC (value : Nat) (raw : Raw) : Raw := (raw.1,raw.2.1,(value,raw.2.2.1.2),raw.2.2.2)
/-- Persistent right-second replacement completes the cross-service ring. -/
def putD (value : Nat) (raw : Raw) : Raw := (raw.1,raw.2.1,(raw.2.2.1.1,value),raw.2.2.2)
/-- Joint readiness is a Boolean focus over the complete service family. -/
def putReady (value : Bool) (raw : Raw) : Raw := (raw.1,raw.2.1,raw.2.2.1,value,raw.2.2.2.2)
/-- Reusable product laws prove the shared node lawful for every source/replacement. -/
theorem quotaLaws : LensLaws (fun raw : Raw => raw.1) putQuota := LensLaws.productFirst
/-- Nested left focus laws follow by composition, without repeating law proofs. -/
theorem aLaws : LensLaws (fun raw : Raw => raw.2.1.1) putA :=
  (LensLaws.productSecond.compose LensLaws.productFirst).compose LensLaws.productFirst
/-- The other left focus is also universally lawful. -/
theorem bLaws : LensLaws (fun raw : Raw => raw.2.1.2) putB :=
  (LensLaws.productSecond.compose LensLaws.productFirst).compose LensLaws.productSecond
/-- A deeper right focus reuses the same product law chain. -/
theorem cLaws : LensLaws (fun raw : Raw => raw.2.2.1.1) putC :=
  ((LensLaws.productSecond.compose LensLaws.productSecond).compose LensLaws.productFirst).compose LensLaws.productFirst
/-- The final allocation focus has the same universal persistent replacement laws. -/
theorem dLaws : LensLaws (fun raw : Raw => raw.2.2.1.2) putD :=
  ((LensLaws.productSecond.compose LensLaws.productSecond).compose LensLaws.productFirst).compose LensLaws.productSecond
/-- Readiness laws compose through the remaining product branch. -/
theorem readyLaws : LensLaws (fun raw : Raw => raw.2.2.2.1) putReady :=
  ((LensLaws.productSecond.compose LensLaws.productSecond).compose LensLaws.productSecond).compose LensLaws.productFirst
/-- Complete shared-node and cross-service equations read one preceding global self. -/
def parts (quota : Nat) : List (Generalized.Fragment Raw View) :=
  [⟨Nat,Nat,MonoLens.ofGetSet (fun raw => raw.1) putQuota,fun value _ _ => value,quota⟩,
   ⟨Nat,Unit,MonoLens.ofGetSet (fun raw => raw.2.1.1) putA,fun _ self _ => min self.get.quota (1+self.get.b),()⟩,
   ⟨Nat,Unit,MonoLens.ofGetSet (fun raw => raw.2.1.2) putB,fun _ self _ => min self.get.quota (1+self.get.c),()⟩,
   ⟨Nat,Unit,MonoLens.ofGetSet (fun raw => raw.2.2.1.1) putC,fun _ self _ => min self.get.quota (1+self.get.d),()⟩,
   ⟨Nat,Unit,MonoLens.ofGetSet (fun raw => raw.2.2.1.2) putD,fun _ self _ => min self.get.quota (1+self.get.a),()⟩,
   ⟨Bool,Unit,MonoLens.ofGetSet (fun raw => raw.2.2.2.1) putReady,fun _ self _ =>
     decide (self.get.a = self.get.quota ∧ self.get.b = self.get.quota ∧
       self.get.c = self.get.quota ∧ self.get.d = self.get.quota),()⟩]
/-- Cold base contains no allocated methods or cached approval result. -/
def base : Raw := (0,(0,0),(0,0),false,"audit")
/-- A closed shared-quota state is comparable data, suitable only as a revised seed. -/
def settled (quota : Nat) : Raw := (quota,(quota,quota),(quota,quota),true,"audit")
/-- Current joint approval checks permission, quota coherence and total commitment. -/
def admit (quota limit : Nat) (allowed : Bool) (_previous candidate : Raw) : Bool :=
  allowed && candidate.2.2.2.1 && decide (candidate.1 = quota ∧
    candidate.2.1.1+candidate.2.1.2+candidate.2.2.1.1+candidate.2.2.1.2 ≤ limit)
/-- Both services and their sum are observed from the same accepted candidate. -/
def report (raw : Raw) (units : Nat) : Except String (Nat × Nat × Nat × Nat × Bool × String) := do
  let left ← (cook raw).left units
  let right ← (cook raw).right units
  return (raw.1,left,right,left+right,raw.2.2.2.1,raw.2.2.2.2)
/-- ANY accepted revision has current permission, joint readiness, coherent shared
quota and a total commitment within the CURRENT cross-service budget. -/
theorem admitted_joint (quota limit : Nat) (allowed : Bool) (previous : Raw) (budget : Nat)
    (candidate : BoundedClosed (fragmentProtocol cook) (parts quota) base)
    (accepted : reviseFeedback (parts quota) cook base previous budget (admit quota limit allowed) = .ok candidate) :
    allowed = true ∧ candidate.closed.raw.2.2.2.1 = true ∧ candidate.closed.raw.1 = quota ∧
      candidate.closed.raw.2.1.1+candidate.closed.raw.2.1.2+
        candidate.closed.raw.2.2.1.1+candidate.closed.raw.2.2.1.2 ≤ limit := by
  have approved := reviseFeedback_approved _ _ _ _ _ _ _ accepted
  simpa only [admit,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using approved
/-- Cold shared dependency propagation precedes the ring and approval lag. -/
example : (reviseFeedback (parts 3) cook base base 6 (admit 3 12 true)).map
    (fun r => (r.steps,r.closed.raw)) = .ok (6,settled 3) := rfl
/-- Complex cooked service observations align with native primary/around methods. -/
example : (reviseFeedback (parts 3) cook base base 6 (admit 3 12 true)).map
    (fun r => report r.closed.raw 2) = .ok (.ok (3,24,36,60,true,"audit")) := rfl
/-- Growing the shared node re-closes BOTH branches from the old raw in four calls. -/
example : (reviseFeedback (parts 4) cook base (settled 3) 4 (admit 4 16 true)).map
    (fun r => (r.steps,report r.closed.raw 2)) = .ok (4,.ok (4,32,48,80,true,"audit")) := rfl
/-- Decreasing shared quota also recomputes both branches; no monotone reuse premise. -/
example : (reviseFeedback (parts 1) cook base (settled 4) 4 (admit 1 4 true)).map
    (fun r => report r.closed.raw 2) = .ok (.ok (1,8,12,20,true,"audit")) := rfl
/-- A valid new fixed point can still violate the joint cross-service budget. -/
example : (reviseFeedback (parts 4) cook base (settled 3) 4 (admit 4 12 true)).map
    (fun r => r.closed.raw) = .error "joint feedback approval refused" := rfl
/-- Publication retains an arbitrary exact old value on joint approval refusal. -/
example (old : Raw) : publishClosed old ((reviseFeedback (parts 4) cook base (settled 3) 4
    (admit 4 12 true)).map (fun r => r.closed.raw)) = old := rfl
/-- Unchanged raw state still receives current permission; old approval is not reused. -/
example : (reviseFeedback (parts 3) cook base (settled 3) 1 (admit 3 12 false)).map
    (fun r => r.closed.raw) = .error "joint feedback approval refused" := rfl
/-- An insufficient warm budget does not expose a partially revised family. -/
example : (reviseFeedback (parts 1) cook base (settled 3) 3 (admit 1 4 true)).map
    (fun r => r.closed.raw) = .error "closure budget exhausted" := rfl
/-- Every actual complete component preserves the original shared audit frame. -/
theorem audit_preserved (quota : Nat) (result : BoundedClosed (fragmentProtocol cook) (parts quota) base) :
    result.closed.raw.2.2.2.2 = base.2.2.2.2 := by
  apply feedback_frame (parts quota) cook (fun raw => raw.2.2.2.2)
  intro part member raw value
  simp only [parts,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
#print axioms quotaLaws
#print axioms aLaws
#print axioms bLaws
#print axioms cLaws
#print axioms dLaws
#print axioms readyLaws
#print axioms audit_preserved
#print axioms reviseFeedback_closed
#print axioms reviseFeedback_approved
#print axioms reviseFeedback_equations
#print axioms reviseFeedback_reached
#print axioms reviseFeedback_bound
#print axioms admitted_joint
end LeanPoo.Examples.SharedFeedback
