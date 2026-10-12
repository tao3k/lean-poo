import LeanPoo.Object.RecursiveValidation

open LeanPoo
open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
open LeanPoo.Prototype.MutableRecord
namespace LeanPoo.Tests.RecursiveValidation

private def registry : Dynamic.Registry :=
  { descriptors := [("Natural", ⟨"Natural", .integerRange 0 100, []⟩),
      ("Pair", ⟨"Pair", .listOf .integer, []⟩)] }

private def schema : Dynamic.RecordSchema :=
  ⟨"Coordinate", [⟨"x", "Natural", none, true⟩, ⟨"y", "Natural", none, true⟩,
    ⟨"z", "Pair", none, false⟩], false⟩

private def declarations (name : String) : Specification :=
  if name == "O" then .compose (.slot "x" (constant (.integer 1)))
    (.slot "y" (constant (.integer 2)))
  else if name == "Child" then .compose (.slot "z" (compute fun self =>
      (self "x").bind fun x => (self "y").map fun y => .list [x, y]))
    (.slot "unused" (compute fun self => self "unused"))
  else .identity

private def checks : IO Unit := do
  let graph : Object.Recursive.Schema :=
    ⟨[("O", []), ("Child", ["O"])], declarations, {}⟩
  let plan ← IO.ofExcept ((Object.Recursive.compile graph "Child").mapError reprStr)
  let instanceValue ← plan.instantiate
  let result ← IO.ofExcept ((← instanceValue.validate registry schema 30 30).mapError reprStr)
  unless result.snapshot.value.slot? "z" == some (.list [.integer 1, .integer 2]) &&
      (← instanceValue.cachedKeys).length == 3 do
    throw (IO.userError "actual C3 slots did not enter dynamic descriptor admission")
  let schemaDescriptor ← IO.ofExcept ((schema.descriptor registry).mapError reprStr)
  let wire ← IO.ofExcept ((schemaDescriptor.encodeText registry 30 result.snapshot.value).mapError reprStr)
  let decoded ← IO.ofExcept ((schema.decodeText registry 30 wire).mapError reprStr)
  unless decoded == result.snapshot.value do
    throw (IO.userError "observed object/schema wire boundary")
  unless (← instanceValue.validate registry {schema with sealed := true} 30 30) matches
      .error (.schema (.unknownSlot "unused")) do
    throw (IO.userError "sealed schema accepted an extra stored slot")
  let cyclic : Dynamic.RecordSchema := ⟨"Cyclic", [⟨"unused", "Natural", none, true⟩], false⟩
  unless (← instanceValue.validate registry cyclic 30 30) matches
      .error (.diagnostic (.cycle ["unused", "unused"])) do
    throw (IO.userError "selected recursive field was hidden from validation")
  let missing : Dynamic.RecordSchema := ⟨"Missing", [⟨"missing", "Natural", none, true⟩], false⟩
  unless (← instanceValue.validate registry missing 30 30) matches
      .error (.source "missing" "missing slot: missing") do
    throw (IO.userError "missing slot/source error boundary")
  let invalid : Object.Recursive.Schema := {graph with base := fromValues [("extra", .text "bad")]}
  let invalidPlan ← IO.ofExcept ((Object.Recursive.compile invalid "Child").mapError reprStr)
  let invalidInstance ← invalidPlan.instantiate
  let badSchema : Dynamic.RecordSchema := ⟨"Invalid", [⟨"extra", "Natural", none, true⟩], false⟩
  unless (← invalidInstance.validate registry badSchema 30 30) matches
      .error (.schema (.wire (.rejected "Invalid"))) do
    throw (IO.userError "observed slot violated its runtime refinement")
  IO.println "RECURSIVE-VALIDATION-OK C3+memo+descriptor+wire=connected fieldReceipts=kernel coldCycles=unforced selectedCycles=diagnosed"

#eval checks
#print axioms Object.Recursive.FieldReceipt.observed
#print axioms Dynamic.Descriptor.validate_value
end LeanPoo.Tests.RecursiveValidation
