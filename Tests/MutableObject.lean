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

/-- Compare all policies under every resolver: fresh dependent targets,
versioned handles across two updates, and transactional errors. -/
private def policyRun (mode : Object.ResolutionMode)
    (policy : Object.UpdatePolicy) : IO Bool := do
  let empty : Object.Schema String (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let declaration : Object.Declaration String (fun _ => Nat) :=
    Object.Declaration.empty |>.withValue "count" 2
      |>.withSlot "derived" (.self fun self => (self "count").map (· + 1))
  let some plan := (LeanPoo.mix empty "Base" [] declaration).toOption
    | return false
  let object ← Object.Mutable.new (plan.memoizeUsing mode)
  let old ← object.snapshot
  -- Keep derived unforced in the old version until after revision.
  let count := old.read "count"
  let .ok first ← object.reviseWithPolicy policy
      [("Base", fun d => d.withValue "count" 5)] | return false
  let .ok second ← object.reviseWithPolicy policy
      [("Base", fun d => d.withValue "count" 8)] | return false
  let failed ← object.reviseWithPolicy policy
      [("Base", fun d => d.withValue "count" 100), ("Unknown", id)]
  let installed ← object.snapshot
  let versions := match policy, first.previous, second.previous with
    | .versioned, some v1, some v2 =>
      v1.read "derived" == some 3 && v2.read "derived" == some 6
    | .eager, none, none | .lazy, none, none => true
    | _, _, _ => false
  -- A declared target returning none distinguishes eager pre-install forcing
  -- from successful lazy/versioned installation with a missing read later.
  let missing ← object.reviseWithPolicy policy
      [("Base", fun d => d.withSlot "derived" (.constant none))]
  let afterMissing ← object.snapshot
  let missingCorrect := match policy, missing with
    | .eager, .error (.target (.noApplicableMethod "derived")) =>
      afterMissing.read "derived" == some 9
    | .lazy, .ok receipt | .versioned, .ok receipt =>
      receipt.current.read "derived" == none && afterMissing.read "derived" == none
    | _, _ => false
  return count == some 2 && old.read "derived" == some 3 &&
    first.current.read "derived" == some 6 &&
    second.current.read "derived" == some 9 &&
    (← object.read "count") == some 8 &&
    installed.read "derived" == some 9 && failed.toOption.isNone &&
    first.current.mode == mode && second.current.mode == mode &&
    versions && missingCorrect

#eval (do
  for mode in [Object.ResolutionMode.onDemand, .compiled, .indexed] do
    for policy in [Object.UpdatePolicy.eager, .lazy, .versioned] do
      unless ← policyRun mode policy do
        throw (IO.userError s!"update policy failed: {repr mode}/{repr policy}") : IO Unit)

end LeanPoo.Tests.MutableObject
