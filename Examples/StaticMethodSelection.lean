import LeanPoo.Object.StaticDispatch

/-! A caller preselects one C4 method shape for a stable interface while
the generic remains independently extensible. A guard still sees each call's
current value. -/

namespace LeanPoo.Examples.StaticMethodSelection

private def generic : Object.Multimethod (String × Nat) Nat Nat :=
  { arity := 1
    precedence := fun call =>
      [if call.1 == "Child" then ["Child", "Base"] else ["Base"]]
    combine := fun methods call => methods.foldl Nat.add call.2 }

def run : Except String (Nat × Nat × Nat × Bool) := do
  let base ← (generic.register [.prototype "Base"] 1).mapError
    (fun _ => "invalid base method")
  let child ← (base.register [.prototype "Child"] 10).mapError
    (fun _ => "invalid child method")
  let guarded ← (child.registerWhen [.prototype "Child"]
    (fun call => call.2 > 5) 100).mapError
    (fun _ => "invalid guarded method")
  let selected ← (guarded.compile ("Child", 2)).mapError
    (fun _ => "invalid call shape")
  let initial := selected.call selected.witness rfl
  let laterValue ← (selected.callChecked ("Child", 7)).mapError
    (fun _ => "unexpected call shape")
  let extended ← (guarded.register [.prototype "Child"] 20).mapError
    (fun _ => "invalid extension")
  let (newValue, _) ← (extended.call ("Child", 2)).mapError
    (fun _ => "invalid extended call")
  let rejected := match selected.callChecked ("Base", 2) with
    | .error (.shapeMismatch _ _) => true
    | _ => false
  return (initial, laterValue, newValue, rejected)

#eval run

end LeanPoo.Examples.StaticMethodSelection
