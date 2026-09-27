import LeanPoo.Object.Mutable

/-! A live configuration object: a child computes a derived value from a
base declaration. A revision installs a new snapshot without mutating the old
one. -/

namespace LeanPoo.Examples.LiveRevision

open LeanPoo

def usage : IO (Except C4.Error ((Option Nat × Option Nat) ×
    (Option Nat × Option Nat))) := do
  let empty : Object.Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base := (Object.Declaration.empty : Object.Declaration String (fun _ => Nat))
    |>.withValue "base" 2
  let child := (Object.Declaration.empty : Object.Declaration String (fun _ => Nat))
    |>.withSlot "derived" (.self fun self => (self "base").map (· * 3))
  match LeanPoo.mix empty "Base" [] base with
  | .error error => return .error error
  | .ok basePlan =>
    match LeanPoo.extend basePlan.schema "Child" "Base" child with
    | .error error => return .error error
    | .ok childPlan =>
      let live ← Object.Mutable.new childPlan.memoize
      let old ← live.snapshot
      match ← live.reviseDeclaration "Base"
          (fun declaration => declaration.withValue "base" 5) with
      | .error error => return .error error
      | .ok _ =>
        let current ← live.snapshot
        return .ok ((old.read "base", old.read "derived"),
          (current.read "base", current.read "derived"))

#eval usage

end LeanPoo.Examples.LiveRevision
