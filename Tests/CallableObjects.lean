import LeanPoo.Object.Callable

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.CallableRecord
namespace LeanPoo.Tests.CallableObjects

private def integer (value : Dynamic.Value) (next : Int → Interaction (Request Int) Dynamic.Value Dynamic.Value) :
    Interaction (Request Int) Dynamic.Value Dynamic.Value :=
  match value with
  | .integer value => next value
  | _ => .error "integer result required"

private def fibonacci : Layer Int := compute fun self input =>
  if input < 0 then .error "negative fibonacci argument"
  else if input ≤ 1 then .value (.integer input)
  else (self ⟨"fib", input - 1⟩).bind fun left => integer left fun left =>
    (self ⟨"fib", input - 2⟩).bind fun right => integer right fun right =>
      .value (.integer (left + right))

private def declaration (name : String) : Specification Int :=
  match name with
  | "C" => Prototype.composeAll [method "factor" (constant (.integer 5)),
      method "trace" (modify fun _ value => match value with
        | .list values => .list (.text "C" :: values) | _ => value)]
  | "A" | "B" => method "trace" (modify fun _ value => match value with
      | .list values => .list (.text name :: values) | _ => value)
  | "O" => Prototype.composeAll [method "factor" (constant (.integer 2)),
      method "trace" (constant (.list [.text "O"])), method "fib" fibonacci,
      method "scale" (compute fun self argument =>
        (self ⟨"factor", 0⟩).bind fun value => integer value fun factor => .value (.integer (argument * factor))),
      method "loop" (compute fun self argument => self ⟨"loop", argument⟩),
      method "spiral" (compute fun self argument => self ⟨"spiral", argument + 1⟩),
      method "broken" (fun _ _ _ => .error "source failure")]
  | _ => Prototype.identity

private def schema : LeanPoo.Object.Callable.Schema Int :=
  ⟨[("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["A", "B"])], declaration, {}⟩

private def oracle (input : Nat) : Int :=
  Int.ofNat (((List.range input).foldl (fun (a, b) _ => (b, a + b)) (0, 1)).1)

example (plan : LeanPoo.Object.Recursive.Plan) (fieldArgument : Argument)
    (depth : Nat) (input : Request Argument) :
    (LeanPoo.Object.Callable.Plan.fromFields plan fieldArgument).call depth input =
      plan.read depth input.name :=
  LeanPoo.Object.Callable.Plan.call_fromFields plan fieldArgument depth input

private def checks : IO Unit := do
  let plan ← IO.ofExcept ((LeanPoo.Object.Callable.compile schema "C").mapError reprStr)
  unless plan.precedence == ["C", "A", "B", "O"] do throw (IO.userError "C3 method order")
  let instanceValue ← plan.instantiate
  unless (← instanceValue.cachedRequests).isEmpty && instanceValue.methodNames.length == 7 do
    throw (IO.userError "method construction forced a cold method")
  let alias := instanceValue
  let first ← IO.ofExcept ((← alias.call 250 ⟨"fib", 40⟩).mapError reprStr)
  let before ← instanceValue.statistics
  unless first.result == .value (.integer (oracle 40)) && before.misses == 41 &&
      (← instanceValue.cachedRequests).length == 41 do
    throw (IO.userError "parameterized recursive sharing or fibonacci oracle")
  let hot ← IO.ofExcept ((← instanceValue.call 1 ⟨"fib", 40⟩).mapError reprStr)
  let after ← instanceValue.statistics
  unless hot.result == first.result && after.misses == before.misses && after.steps == before.steps &&
      after.hits == before.hits + 1 do
    throw (IO.userError "hot method call recomputed or lost alias sharing")
  for input in List.range 11 do
    let answer ← IO.ofExcept ((← instanceValue.call 100 ⟨"fib", Int.ofNat input⟩).mapError reprStr)
    unless answer.result.observation == plan.call 12 ⟨"fib", Int.ofNat input⟩ do
      throw (IO.userError "call/source observation parity")
  let trace ← IO.ofExcept ((← instanceValue.call 30 ⟨"trace", 0⟩).mapError reprStr)
  unless trace.result == .value (.list [.text "C", .text "A", .text "B", .text "O"]) do
    throw (IO.userError "diamond inherited chain duplicated or reordered a method")
  let scaled ← IO.ofExcept ((← instanceValue.call 30 ⟨"scale", 3⟩).mapError reprStr)
  let scaledOther ← IO.ofExcept ((← instanceValue.call 30 ⟨"scale", 4⟩).mapError reprStr)
  unless scaled.result == .value (.integer 15) && scaledOther.result == .value (.integer 20) do
    throw (IO.userError "final-self override or different parameter cache key")
  let broken ← IO.ofExcept ((← instanceValue.call 10 ⟨"broken", 1⟩).mapError reprStr)
  let brokenHot ← IO.ofExcept ((← alias.call 1 ⟨"broken", 1⟩).mapError reprStr)
  unless broken.result == .error "source failure" && brokenHot.result == broken.result do
    throw (IO.userError "source method errors are not shared")
  match ← instanceValue.callCertified 20 ⟨"loop", 7⟩ with
  | .error (.cycle path divergent) =>
    have _kernelCycle : Diverges plan.program ⟨"loop", 7⟩ := divergent
    unless path == [⟨"loop", 7⟩, ⟨"loop", 7⟩] do throw (IO.userError "method cycle lost its parameters")
  | _ => throw (IO.userError "parameterized cycle lacks divergence evidence")
  unless (← instanceValue.callCertified 12 ⟨"spiral", 0⟩) matches .error .budgetExhausted do
    throw (IO.userError "same method with changing arguments misclassified as a cycle")
  let fresh ← plan.instantiate
  let one ← IO.asTask (fresh.call 180 ⟨"fib", 25⟩) .dedicated
  let two ← IO.asTask (fresh.call 180 ⟨"fib", 25⟩) .dedicated
  let oneResult ← IO.ofExcept one.get
  let twoResult ← IO.ofExcept two.get
  unless oneResult.isOk && twoResult.isOk && (← fresh.statistics).misses == 26 do
    throw (IO.userError "concurrent aliases duplicate parameterized recursive work")
  let mutable ← plan.mutable
  let ⟨frozen, frozenResult⟩ ← mutable.callCertified 30 ⟨"scale", 3⟩
  let frozenReceipt ← IO.ofExcept (frozenResult.mapError reprStr)
  mutable.slot "factor" (constant (.integer 9))
  unless (← mutable.cachedRequests).isEmpty && (← mutable.snapshot).generation == 1 do
    throw (IO.userError "mutable method replacement retained stale argument results")
  let ⟨changed, changedResult⟩ ← mutable.callCertified 30 ⟨"scale", 3⟩
  let changedReceipt ← IO.ofExcept (changedResult.mapError reprStr)
  unless frozenReceipt.result == .value (.integer 15) && changedReceipt.result == .value (.integer 27) &&
      readPure frozen.storage 4 ⟨"scale", 3⟩ == .value (.integer 15) && changed.generation == 1 do
    throw (IO.userError "mutable final self or retained method snapshot")
  mutable.slot "scale" (modify fun _ value => match value with | .integer n => .integer (n + 1) | _ => value)
  let ⟨_, modifiedResult⟩ ← mutable.callCertified 30 ⟨"scale", 3⟩
  let modified ← IO.ofExcept (modifiedResult.mapError reprStr)
  unless modified.result == .value (.integer 28) do
    throw (IO.userError "inherited mutable method lost final-self rebinding")
  let dataStorage := MutableRecord.write (MutableRecord.fromValues [("x", .integer 1)]) "y"
    (MutableRecord.compute fun self => (self "x").map fun value => .list [value])
  let dataSchema : LeanPoo.Object.Recursive.Schema := ⟨[("Data", [])], fun _ => .identity, dataStorage⟩
  let dataPlan ← IO.ofExcept ((LeanPoo.Object.Recursive.compile dataSchema "Data").mapError reprStr)
  let callable := LeanPoo.Object.Callable.Plan.fromFields dataPlan (0 : Int)
  let dataInstance ← callable.instantiate
  let dataAnswer ← IO.ofExcept ((← dataInstance.call 20 ⟨"y", 99⟩).mapError reprStr)
  unless dataAnswer.result == .value (.list [.integer 1]) &&
      callable.call 3 ⟨"missing", 99⟩ == dataPlan.read 3 "missing" do
    throw (IO.userError "existing data object changed in the method protocol")
  let numeric : LeanPoo.Object.Callable.Schema Int :=
    ⟨[("Number", ["Even", "Cube", "Identity"]), ("Even", []), ("Cube", []), ("Identity", [])],
      fun name => match name with
      | "Even" => method "apply" (fun self inherited input =>
        if input < 0 then self ⟨"apply", -input⟩ else (inherited ()) input)
      | "Cube" => method "apply" (fun _ inherited input =>
        ((inherited ()) input).map fun value => match value with
          | .integer value => .integer (value * value * value) | _ => value)
      | "Identity" => method "apply" (fun _ _ input => .value (.integer input))
      | _ => Prototype.identity, {}⟩
  let numericPlan ← IO.ofExcept ((LeanPoo.Object.Callable.compile numeric "Number").mapError reprStr)
  let numericInstance ← numericPlan.instantiate
  for offset in List.range 9 do
    let input := Int.ofNat offset - 4
    let answer ← IO.ofExcept ((← numericInstance.call 30 ⟨"apply", input⟩).mapError reprStr)
    let magnitude := Int.ofNat input.natAbs
    unless answer.result == .value (.integer (magnitude * magnitude * magnitude)) do
      throw (IO.userError "paper numeric method self/super calls")
  let forwarded : LeanPoo.Object.Callable.Schema Int :=
    ⟨[("Child", ["Parent"]), ("Parent", [])], fun name =>
      if name == "Child" then method "shift" (fun _ inherited input => (inherited ()) (input + 1))
      else method "shift" (fun _ _ input => .value (.integer input)), {}⟩
  let forwardedPlan ← IO.ofExcept ((LeanPoo.Object.Callable.compile forwarded "Child").mapError reprStr)
  let forwardedInstance ← forwardedPlan.instantiate
  let forwardedAnswer ← IO.ofExcept ((← forwardedInstance.call 10 ⟨"shift", 7⟩).mapError reprStr)
  unless forwardedAnswer.result == .value (.integer 8) do
    throw (IO.userError "inherited method could not receive different arguments")
  IO.println "CALLABLE-OBJECTS-OK fib40=102334155 misses=41 sourceParity=11 c3=true parameters=true mutable=true concurrent=true"

#eval checks
#print axioms LeanPoo.Object.Callable.Plan.call_derivation
#print axioms LeanPoo.Object.Callable.Plan.call_fromFields
#print axioms LeanPoo.Object.Callable.Instance.call_agrees
end LeanPoo.Tests.CallableObjects
