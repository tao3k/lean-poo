import LeanPoo.Object.Debug

namespace DebugObjectExample

open LeanPoo.Object.Debug

inductive Key where
  | a
  | b
  | c
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

/-- Two sibling reads must share the same budget. -/
def branching : Program Key Value :=
  (((Program.empty : Program Key Value)
    |>.withSlot .a (fun read => do
      let _ ← read .b
      read .c))
    |>.withSlot .b (fun _ => pure (some 1)))
    |>.withSlot .c (fun _ => pure (some 2))

#guard match (cyclic.runTrace 8 .a).result with
  | .error (.cycle [.a, .b, .a]) => true
  | _ => false
#guard match (finite.runTrace 2 .a).result with
  | .ok (some 42) => true
  | _ => false
#guard match (branching.runTrace 2 .a).result with
  | .error (.fuelExhausted [.a, .c]) => true
  | _ => false
#guard match (branching.runTrace 3 .a).result with
  | .ok (some 2) => true
  | _ => false
#guard match (branching.runTrace 2 .a).events with
  | [.enter .a, .enter .b, .resolved .b, .exhausted [.a, .c]] => true
  | _ => false
#guard (branching.runTrace 2 .a).stepsUsed == 2
#guard (branching.runTrace 3 .a).stepsUsed == 3

#eval cyclic.runTrace 8 .a
#eval finite.runTrace 8 .a
#eval finite.runTrace 1 .a

end DebugObjectExample
