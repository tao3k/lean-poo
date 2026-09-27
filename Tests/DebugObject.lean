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

private def diagnosticsHold : Bool :=
  (match (cyclic.runTrace 8 .a).result with
    | .error (.cycle [.a, .b, .a]) => true
    | _ => false) &&
  (match (finite.runTrace 2 .a).result with
    | .ok (some 42) => true
    | _ => false) &&
  (match (branching.runTrace 2 .a).result with
    | .error (.fuelExhausted [.a, .c]) => true
    | _ => false) &&
  (match (branching.runTrace 3 .a).result with
    | .ok (some 2) => true
    | _ => false) &&
  (match (branching.runTrace 2 .a).events with
    | [.enter .a, .enter .b, .resolved .b, .exhausted [.a, .c]] => true
    | _ => false) &&
  (branching.runTrace 2 .a).stepsUsed == 2 &&
  (branching.runTrace 3 .a).stepsUsed == 3

example : diagnosticsHold = true := by native_decide

#eval (do
  if (← IO.getEnv "LEANPOO_VERBOSE") == some "1" then
    IO.println (repr (cyclic.runTrace 8 .a,
      finite.runTrace 8 .a, finite.runTrace 1 .a)) : IO Unit)

end DebugObjectExample
