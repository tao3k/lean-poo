import LeanPoo.Object.Debug

namespace DebugObjectExample

open LeanPoo.Object.Debug

inductive Key where
  | a
  | b
  deriving DecidableEq, Repr

abbrev Value (_ : Key) : Type := Nat

/-- An agent-authored unproductive pair of self references. -/
def cyclic : Program Key Value :=
  ((Program.empty : Program Key Value)
    |>.withSlot .a (fun read => read .b))
    |>.withSlot .b (fun read => read .a)

/-- A productive dependency chain. -/
def finite : Program Key Value :=
  ((Program.empty : Program Key Value)
    |>.withSlot .a (fun read => read .b))
    |>.withSlot .b (fun _ => pure (some 42))

#eval cyclic.runTrace 8 .a
#eval finite.runTrace 8 .a
#eval finite.runTrace 1 .a

end DebugObjectExample
