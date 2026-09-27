import LeanPoo.Object.Debug

namespace DebugUnboundedBodyExample

open LeanPoo.Object.Debug

inductive Key where
  | a
  deriving DecidableEq, Repr

abbrev Value (_ : Key) : Type := Nat

/-- An opaque user callback can block without making another guarded read. -/
unsafe def blockedValue : Nat := unsafeBaseIO do
  IO.sleep 60000
  pure 1

unsafe def blocked : Program Key Value :=
  (Program.empty : Program Key Value).withSlot .a
    (fun _ => pure (some blockedValue))

#eval (blocked.runTrace 1 .a).result

end DebugUnboundedBodyExample
