import LeanPoo.Object.Mutable

namespace LeanPoo.Examples.MutableObject

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

end LeanPoo.Examples.MutableObject
