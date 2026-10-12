import LeanPoo.Object.SharedRecursive

open LeanPoo
open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.Recursive.Shared
namespace LeanPoo.Tests.SharedRecursive

example (plan : Object.Recursive.Plan)
    (runtime : Runtime (MutableRecord.generator plan.storage)) (key : String)
    (receipt : Cached.Receipt (MutableRecord.generator plan.storage)
      (MutableRecord.generator plan.storage key)) (accepted : runtime.read key = .ok receipt)
    (order : List String) (derived : C3.GraphDerivation plan.schema.graph plan.root order) :
    ∃ depth, MutableRecord.readPure
      ((plan.schema.specification order).transition plan.schema.base).1 depth key =
        (runtime.executor key).result := plan.shared_derivation runtime key receipt accepted order derived

example (plan : Object.Callable.Plan Argument) (runtime : Runtime plan.program)
    (input : CallableRecord.Request Argument) (receipt : Cached.Receipt plan.program (plan.program input))
    (accepted : runtime.read input = .ok receipt) :
    ∃ depth, plan.call depth input = (runtime.executor input).result :=
  plan.shared_observed runtime input receipt accepted

private def graph : C3.Graph :=
  [("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["A", "B"]), ("D", ["C"])]

private def fields (name : String) : MutableRecord.Specification :=
  match name with
  | "O" => .compose (.slot "x" (MutableRecord.constant (.integer 1)))
      (.slot "y" (MutableRecord.constant (.integer 2)))
  | "B" => .slot "x" (MutableRecord.constant (.integer 3))
  | "A" => .slot "x" (MutableRecord.modify fun value => match value with
      | .integer n => .integer (2 * n) | _ => value)
  | "C" => .compose (.slot "z" (MutableRecord.compute fun self =>
      (self "x").bind fun x => (self "y").map fun y => .list [x, y]))
      (.slot "unused" (MutableRecord.compute fun self => self "unused"))
  | "D" => .slot "x" (MutableRecord.constant (.integer 10))
  | _ => .identity

private def methods (name : String) : CallableRecord.Specification Nat :=
  match name with
  | "O" => composeAll [
      CallableRecord.method "factor" (CallableRecord.constant (.integer 2)),
      CallableRecord.method "trace" (CallableRecord.constant (.list [.text "O"])),
      CallableRecord.method "scale" (CallableRecord.compute fun self argument =>
        (self ⟨"factor", 0⟩).map fun value => match value with
          | .integer n => .integer (n * argument) | _ => value),
      CallableRecord.method "sum" (CallableRecord.compute fun self argument =>
        if argument == 0 then .value (.integer 0) else
          (self ⟨"sum", argument - 1⟩).map fun value => match value with
            | .integer n => .integer (n + argument) | _ => value),
      CallableRecord.method "loop" (CallableRecord.compute fun self argument => self ⟨"loop", argument⟩),
      CallableRecord.method "spiral" (CallableRecord.compute fun self argument => self ⟨"spiral", argument + 1⟩),
      CallableRecord.method "broken" (fun _ _ _ => .error "method-source-error")]
  | "C" => composeAll [CallableRecord.method "factor" (CallableRecord.constant (.integer 5)),
      CallableRecord.method "trace" (CallableRecord.modify fun _ value => match value with
        | .list values => .list (.text "C" :: values) | _ => value)]
  | "A" | "B" => CallableRecord.method "trace" (CallableRecord.modify fun _ value => match value with
      | .list values => .list (.text name :: values) | _ => value)
  | "D" => CallableRecord.method "factor" (CallableRecord.constant (.integer 11))
  | _ => identity

private unsafe def checks : IO Unit := do
  let mut fieldReads := 0
  let mut boundedFields := 0
  let mut methodReads := 0
  for root in ["C", "D"] do
    let plan ← IO.ofExcept ((Object.Recursive.compile ⟨graph, fields, {}⟩ root).mapError reprStr)
    let runtime := plan.sharedRuntime
    for key in ["x", "y", "z", "missing"] do
      match runtime.read key with
      | .ok receipt =>
        unless receipt.result.observation == plan.read 12 key do
          throw (IO.userError "native C3 field read changed composition or source error")
      | _ => throw (IO.userError "completed native C3 field refused")
      fieldReads := fieldReads + 1
    for depth in List.range 5 do
      let limited := plan.boundedSharedRuntime depth
      for key in ["x", "y", "z", "missing"] do
        match plan.read depth key, limited.read key with
        | .pending, .error .unfinished => pure ()
        | .value value, .ok receipt =>
          unless receipt.result.observation == .value value do throw (IO.userError "bounded C3 field value")
        | .error message, .ok receipt =>
          unless receipt.result.observation == .error message do throw (IO.userError "bounded C3 field error")
        | _, _ => throw (IO.userError "bounded C3 field outcome")
        boundedFields := boundedFields + 1
    unless (plan.boundedSharedRuntime 10).read "unused" matches .error .unfinished do
      throw (IO.userError "cold recursive field classified as completed")
    let callable ← IO.ofExcept ((Object.Callable.compile ⟨graph, methods, {}⟩ root).mapError reprStr)
    let shared := callable.sharedRuntime
    for argument in List.range 11 do
      for name in ["factor", "scale", "sum", "trace", "broken", "missing"] do
        let input : CallableRecord.Request Nat := ⟨name, argument⟩
        match shared.read input with
        | .ok receipt =>
          unless receipt.result.observation == callable.call 14 input do
            throw (IO.userError "native C3 method argument/self/inherited outcome")
          if name == "scale" then
            let factor : Nat := if root == "C" then 5 else 11
            unless receipt.result.observation == .value (.integer (factor * argument)) do
              throw (IO.userError "final self override scalar")
          if name == "sum" then
            unless receipt.result.observation == .value (.integer (argument * (argument + 1) / 2)) do
              throw (IO.userError "changing argument scalar")
          if name == "trace" then
            unless receipt.result.observation == .value (.list [.text "C", .text "A", .text "B", .text "O"]) do
              throw (IO.userError "diamond inherited order")
        | _ => throw (IO.userError "completed native C3 method refused")
        methodReads := methodReads + 1
    for name in ["loop", "spiral"] do
      unless (callable.boundedSharedRuntime 12).read ⟨name, 7⟩ matches .error .unfinished do
        throw (IO.userError "method loop or changing request classified as completed")
  let old ← IO.ofExcept ((Object.Recursive.compile ⟨graph, fields, {}⟩ "C").mapError reprStr)
  let revised := fun name => if name == "C" then
      MutableRecord.Specification.compose (.slot "x" (MutableRecord.constant (.integer 19))) (fields name)
    else fields name
  let next ← IO.ofExcept ((Object.Recursive.compile ⟨graph, revised, {}⟩ "C").mapError reprStr)
  let retained := old.sharedRuntime
  let current := next.sharedRuntime
  let stale : Runtime (MutableRecord.generator next.storage) := ⟨retained.executor⟩
  match retained.read "z", current.read "z", stale.read "z" with
  | .ok oldReceipt, .ok newReceipt, .error .invalidTrace =>
    unless oldReceipt.result.observation == .value (.list [.integer 6, .integer 2]) &&
        newReceipt.result.observation == .value (.list [.integer 19, .integer 2]) do
      throw (IO.userError "retained immutable program or revised native value")
  | _, _, _ => throw (IO.userError "native executor ignored current program admission")
  unless fieldReads == 8 && boundedFields == 40 && methodReads == 132 do
    throw (IO.userError "shared C3 control denominator")
  IO.println "POOF-SHARED-RECURSIVE-OK fields=8 boundedFields=40 methods=132 unfinished=6 staleExecutor=refused retainedSnapshots=true diamond=true"

#eval checks
#print axioms Object.Recursive.Plan.shared_observed
#print axioms Object.Recursive.Plan.shared_derivation
#print axioms Object.Callable.Plan.shared_observed
#print axioms Object.Callable.Plan.shared_derivation
end LeanPoo.Tests.SharedRecursive
