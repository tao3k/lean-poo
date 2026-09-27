import LeanPoo.Object.Mutable

namespace LeanPoo.Tests.MutableObject

def run : IO (Except LeanPoo.C4.Error (Option Nat × Option Nat)) := do
  let empty : LeanPoo.Object.Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let direct : LeanPoo.Object.Declaration String (fun _ => Nat) :=
    LeanPoo.Object.Declaration.empty |>.withValue "count" 2
  match LeanPoo.mix empty "Base" [] direct with
  | .error error => return .error error
  | .ok plan =>
    let mutableObject ← LeanPoo.Object.Mutable.new plan.memoize
    let before ← mutableObject.read "count"
    let changed ← mutableObject.reviseDeclaration "Base"
      (fun declaration => declaration.withValue "count" 5)
    match changed with
    | .error error => return .error error
    | .ok _ => return .ok (before, ← mutableObject.read "count")

#eval run

/-- Ordered base and child edits reuse one validated C4 order and install a
single new lazy instance. A later bad name rolls back the entire batch. -/
private def batchRun : IO Bool := do
  let empty : LeanPoo.Object.Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base : LeanPoo.Object.Declaration String (fun _ => Nat) :=
    LeanPoo.Object.Declaration.empty |>.withValue "count" 2
  let some basePlan := (LeanPoo.mix empty "Base" [] base).toOption
    | return false
  let child : LeanPoo.Object.Declaration String (fun _ => Nat) :=
    LeanPoo.Object.Declaration.empty |>.withSlot "derived"
      (.self fun self => (self "count").map (· + 1))
  let some childPlan :=
      (LeanPoo.extend basePlan.schema "Child" "Base" child).toOption
    | return false
  let mutableObject ← LeanPoo.Object.Mutable.new childPlan.memoize
  let snapshot ← mutableObject.snapshot
  let before := (snapshot.read "count", snapshot.read "derived")
  let failed ← mutableObject.reviseDeclarations
    [("Base", fun declaration => declaration.withValue "count" 9),
      ("Unknown", id)]
  let afterFailure ← mutableObject.snapshot
  let succeeded ← mutableObject.reviseDeclarations
    [("Base", fun declaration => declaration.withValue "count" 5),
      ("Child", fun declaration => declaration.withSlot "derived"
        (.self fun self => (self "count").map (· + 2)))]
  let revised ← mutableObject.snapshot
  return failed.toOption.isNone && succeeded.toOption.isSome &&
    before == (some 2, some 3) &&
    (afterFailure.read "count", afterFailure.read "derived") == before &&
    (revised.read "count", revised.read "derived") == (some 5, some 7) &&
    revised.plan.precedence == snapshot.plan.precedence &&
    (snapshot.read "count", snapshot.read "derived") == before

#eval (do
  unless ← batchRun do
    throw (IO.userError "batched mutable prototype revision failed") : IO Unit)

end LeanPoo.Tests.MutableObject
