import LeanPoo.Object.Debug

/-! Inspect an agent-authored dependency while developing an object. The
diagnostic program shares one read budget and reports the path of a cycle. -/

namespace LeanPoo.Examples.DebugTrace

open LeanPoo.Object.Debug

inductive Key where
  | summary
  | source
  deriving DecidableEq, Repr

abbrev Value (_ : Key) := Nat

def working : Program Key Value :=
  (Program.empty : Program Key Value)
    |>.withSlot .summary (fun read => do
      let source ← read .source
      pure (source.map (· + 1)))
    |>.withSlot .source (fun _ => pure (some 41))

def recursive : Program Key Value :=
  (Program.empty : Program Key Value)
    |>.withSlot .summary (fun read => read .source)
    |>.withSlot .source (fun read => read .summary)

#eval working.runTrace 4 .summary
#eval recursive.runTrace 4 .summary

end LeanPoo.Examples.DebugTrace
