import LeanPoo.Prototype.Object

namespace LeanPoo.Examples.FirstClassRecord

open LeanPoo.Prototype

inductive Key where
  | x | doubled
  deriving DecidableEq

abbrev Value : Key → Type := fun _ => Nat

def setX (value : Nat) :
    DelayedProto (Record Key Value) (Record Key Value) (Record Key Value) :=
  Object.recordSlotGen .x (fun _ _ => some value)

def computedDouble :
    DelayedProto (Record Key Value) (Record Key Value) (Record Key Value) :=
  Object.recordSlotGen .doubled (fun self _ =>
    (self.get.lookup .x).map (2 * ·))

unsafe def base : Object (Record Key Value) (Record Key Value) :=
  Object.ofPrototype (setX 3) (Thunk.pure Record.empty)

unsafe def computed : Object (Record Key Value) (Record Key Value) :=
  base.extend computedDouble

/-- Recomposition gives `computedDouble` the new final self, including x=4. -/
unsafe def overridden : Object (Record Key Value) (Record Key Value) :=
  computed.extend (setX 4)

#eval (base.value.lookup .x, computed.value.lookup .doubled)
#eval (overridden.value.lookup .x, overridden.value.lookup .doubled)

end LeanPoo.Examples.FirstClassRecord
