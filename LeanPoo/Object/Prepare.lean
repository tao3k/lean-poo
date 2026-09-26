import Std
import LeanPoo.Object.Resolve

namespace LeanPoo.Object

universe u v

/-- A preassembled slot function carries its agreement with the one
authoritative resolver. -/
structure SlotProgram {Key : Type u} {Value : Key → Type v}
    (plan : Plan Key Value) (key : Key) where
  run : Self Key Value → Option (Value key)
  sound : ∀ self, run self = plan.resolve key self

/-- A heterogeneous cache of assembled methods for requested keys. -/
structure Prepared (Key : Type u) (Value : Key → Type v)
    [BEq Key] [Hashable Key] where
  plan : Plan Key Value
  slots : Std.DHashMap Key (SlotProgram plan)

/-- Assemble methods once for the chosen keys. Other keys remain available
through the same resolver without changing their semantics. -/
def Plan.prepare [BEq Key] [Hashable Key] (plan : Plan Key Value)
    (keys : List Key) : Prepared Key Value :=
  { plan
    slots := keys.foldl (fun table key =>
      table.insert key ⟨plan.compileSlot key, by intro self; rfl⟩) {} }

def Prepared.resolve [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prepared : Prepared Key Value) (key : Key)
    (self : Self Key Value) : Option (Value key) :=
  match prepared.slots.get? key with
  | some program => program.run self
  | none => prepared.plan.resolve key self

theorem Prepared.resolve_sound [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prepared : Prepared Key Value) (key : Key)
    (self : Self Key Value) :
    prepared.resolve key self = prepared.plan.resolve key self := by
  unfold Prepared.resolve
  split
  · rename_i program condition
    exact program.sound self
  · rfl

def Prepared.ref [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prepared : Prepared Key Value) (key : Key)
    (self : Self Key Value) : Except (LookupError Key) (Value key) :=
  match prepared.resolve key self with
  | some value => .ok value
  | none => .error (.noApplicableMethod key)

theorem Prepared.ref_sound [BEq Key] [LawfulBEq Key] [Hashable Key]
    (prepared : Prepared Key Value) (key : Key)
    (self : Self Key Value) :
    prepared.ref key self = prepared.plan.ref key self := by
  simp [Prepared.ref, Plan.ref, prepared.resolve_sound key self]
  rfl

end LeanPoo.Object
