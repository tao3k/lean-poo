import LeanPoo.Object.Schema

namespace LeanPoo.Examples.TypedSlots

/-- A class interface is a Lean family of value types indexed by slot keys. -/
inductive Key where
  | active
  | retries
  deriving DecidableEq

def Value : Key → Type
  | .active => Bool
  | .retries => Nat

example : Value .retries = Nat := rfl

/-- The inherited retries value is delayed; the final self supplies active. -/
def declaration : Object.Declaration Key Value :=
  (Object.Declaration.empty : Object.Declaration Key Value)
    |>.withValue .active true
    |>.withSlot .retries (.computed fun self inherited =>
        let inheritedRetries : Nat := (inherited ()).getD (0 : Nat)
        let isActive : Bool := (self .active).getD false
        some (inheritedRetries + if isActive == true then 1 else 0))

/-- The key determines the value type without a runtime type descriptor. -/
def setRetries (value : Nat) : Object.Declaration Key Value :=
  declaration.withValue .retries value

end LeanPoo.Examples.TypedSlots
