import LeanPoo.Object.CallableValidation
import LeanPoo.Prototype.DynamicCodecSemantics

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.CallableRecord
open LeanPoo.Object.Callable
namespace LeanPoo.Tests.CallableValidation

private def schema : Schema Dynamic.Value :=
  ⟨[("Child", ["Parent"]), ("Parent", [])], fun name =>
    if name == "Child" then method "factor" (constant (.integer 5))
    else Prototype.composeAll [method "factor" (constant (.integer 2)),
      method "scale" (compute fun self argument => match argument with
        | .integer input => (self ⟨"factor", .unit⟩).map fun factor => match factor with
          | .integer factor => .integer (input * factor) | _ => .unit
        | _ => .error "integer argument required"),
      method "badResult" (constant (.text "wrong")),
      method "reference" (constant (.function "callback")),
      method "loop" (compute fun self argument => self ⟨"loop", argument⟩),
      method "echo" (compute fun _ argument => .value argument),
      method "sourceError" (fun _ _ _ => .error "method failed")], {}⟩

private def registry : Dynamic.Registry :=
  { descriptors := [("Input", ⟨"Small", .integerRange 0 10, []⟩),
      ("Output", ⟨"Result", .integerRange 0 100, []⟩)]
    functions := [("callback", fun value => .ok value)] }

example (invocation : Invocation plan registry signature argument) :
    Dynamic.Accepted registry signature.output invocation.value := invocation.outputAccepted

example (invocation : Invocation plan registry signature argument) :
    ∃ depth, plan.call depth ⟨signature.name, argument⟩ = .value invocation.value := invocation.observed

private def checks : IO Unit := do
  let plan ← IO.ofExcept ((compile schema "Child").mapError reprStr)
  let instanceValue ← plan.instantiate
  let signature : Signature := ⟨"scale", .named "Input", .named "Output"⟩
  let invocation ← IO.ofExcept ((← instanceValue.invoke registry signature (.integer 3) 30 30).mapError reprStr)
  unless invocation.value == .integer 15 do throw (IO.userError "actual C3 method validation")
  have _inputAccepted := invocation.inputAccepted
  have _outputAccepted := invocation.outputAccepted
  have _evaluation := invocation.evaluation
  let wire ← IO.ofExcept ((signature.resultType.encodeText registry 30 invocation.value).mapError reprStr)
  let decoded ← IO.ofExcept ((signature.resultType.decodeText registry 30 wire).mapError reprStr)
  unless decoded.value == invocation.value do throw (IO.userError "method result wire admission")
  let before ← instanceValue.statistics
  unless (← instanceValue.invoke registry signature (.integer 11) 30 30) matches .error (.argument _) do
    throw (IO.userError "runtime input refinement was ignored")
  unless (← instanceValue.statistics).misses == before.misses &&
      (← instanceValue.statistics).hits == before.hits do
    throw (IO.userError "rejected argument forced an object method")
  let narrow : Dynamic.Registry := { registry with descriptors :=
    [("Input", ⟨"Narrow", .integerRange 0 1, []⟩), ("Output", ⟨"Result", .integerRange 0 100, []⟩)] }
  unless (← instanceValue.invoke narrow signature (.integer 3) 1 30) matches .error (.argument _) do
    throw (IO.userError "hot method request retained stale input admission")
  let (factoryRegistry, factoryValue) ← IO.ofExcept ((Dynamic.DescriptorFactory.functionOf.call registry
    "ScaleSignature" [.descriptor "Input", .descriptor "Output"]).mapError reprStr)
  let slot : Dynamic.SlotDescription := ⟨"scale", "ScaleSignature", none, false⟩
  let reflected ← IO.ofExcept ((Dynamic.SlotDescription.fromValue slot.describe).mapError reprStr)
  let factoryDescriptor ← IO.ofExcept ((factoryRegistry.resolveDescriptor factoryValue).mapError reprStr)
  unless (← instanceValue.invokeSlot factoryRegistry reflected (.integer 4) 30 30).toOption ==
      some (.integer 20) &&
      (← instanceValue.invokeDescriptor factoryRegistry "scale" factoryDescriptor (.integer 5) 30 30).toOption ==
        some (.integer 25) do
    throw (IO.userError "runtime factory/catalog was not the method's calling convention")
  unless (← instanceValue.invokeSlot registry slot (.integer 4) 1 30) matches .error (.schema _) do
    throw (IO.userError "missing current signature identity was admitted")
  unless (← instanceValue.invokeDescriptor registry "scale" ⟨"Integer", .integer, []⟩
      (.integer 4) 1 30) matches .error (.signature .expectedFunctionContract) do
    throw (IO.userError "non-function descriptor was used as a method signature")
  let badSignature : Signature := ⟨"badResult", .unit, .integer⟩
  unless (← instanceValue.invoke registry badSignature .unit 30 30) matches .error (.result _) do
    throw (IO.userError "object method output validation was omitted")
  unless (← instanceValue.invoke registry badSignature .unit 1 30) matches .error (.result _) do
    throw (IO.userError "hot output bypassed the result gate")
  let reference : Signature := ⟨"reference", .unit, .functionOf .integer .integer⟩
  let accepted ← IO.ofExcept ((← instanceValue.invoke registry reference .unit 30 30).mapError reprStr)
  unless accepted.value == .function "callback" do throw (IO.userError "function result admission")
  let referenceBefore ← instanceValue.statistics
  unless (← instanceValue.invoke ({} : Dynamic.Registry) reference .unit 1 30) matches .error (.result _) do
    throw (IO.userError "cached function result bypassed current registry identity")
  let referenceAfter ← instanceValue.statistics
  unless referenceAfter.misses == referenceBefore.misses && referenceAfter.hits == referenceBefore.hits + 1 do
    throw (IO.userError "reference negative control did not exercise the hot cache")
  let sourceSignature : Signature := ⟨"sourceError", .unit, .top⟩
  unless (← instanceValue.invoke registry sourceSignature .unit 20 20) matches .error (.source "method failed") do
    throw (IO.userError "source error changed into a validation or cycle error")
  let loop : Signature := ⟨"loop", .unit, .unit⟩
  unless (← instanceValue.invoke registry loop .unit 20 20) matches .error (.diagnostic (.cycle _)) do
    throw (IO.userError "checked method lost its cycle diagnostic")
  let payloads : List Dynamic.Value := [.unit, .boolean true, .integer 1, .text "λ",
    .list [.integer 1], .dictionary [(.text "x", .integer 1)],
    .object [("x", .integer 1), ("x", .integer 2)], .function "callback", .descriptor "Input"]
  let echo ← plan.instantiate
  for value in payloads do
    let answer ← IO.ofExcept ((← echo.call 10 ⟨"echo", value⟩).mapError reprStr)
    unless answer.result == .value value do throw (IO.userError "dynamic argument cache collision")
  unless (← echo.statistics).misses == payloads.length && (← echo.cachedRequests).length == payloads.length do
    throw (IO.userError "dynamic argument constructors shared one request key")
  let mutable ← plan.mutable
  let frozen ← IO.ofExcept ((← mutable.invoke registry signature (.integer 3) 30 30).mapError reprStr)
  mutable.slot "factor" (constant (.integer 9))
  let changed ← IO.ofExcept ((← mutable.invoke registry signature (.integer 3) 30 30).mapError reprStr)
  unless frozen.1.generation == 0 && changed.1.generation == 1 &&
      frozen.2.value == .integer 15 && changed.2.value == .integer 27 do
    throw (IO.userError "checked mutable method lost its exact snapshot")
  let narrowOutput : Dynamic.Registry := { registry with descriptors :=
    [("Input", ⟨"Small", .integerRange 0 10, []⟩), ("Output", ⟨"Narrow", .integerRange 0 20, []⟩)] }
  unless (← mutable.invoke narrowOutput signature (.integer 3) 1 30) matches .error (.result _) do
    throw (IO.userError "mutable hot method retained stale output admission")
  IO.println "CALLABLE-VALIDATION-OK c3=true kernelInvocation=true inputBeforeForce=true hotRegistry=true reflectiveFactory=true wire=true"

#eval checks
#print axioms Invocation.observed
end LeanPoo.Tests.CallableValidation
