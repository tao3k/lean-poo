import LeanPoo.Prototype.DynamicSchema

open LeanPoo.Prototype.Dynamic
namespace LeanPoo.Tests.DynamicSchema

private def registry : Registry :=
  { descriptors := [("Integer", ⟨"Integer", .integer, []⟩), ("Text", ⟨"Text", .text, []⟩),
      ("Descriptor", descriptorType)]
    functions := [("increment", fun value => match value with
      | .integer n => .ok (.integer (n + 1))
      | _ => .error (.functionError "integer required"))] }

private def nameSlot : SlotDescription := ⟨"name", "Text", some (.text "guest"), false⟩

private def schema : RecordSchema :=
  ⟨"Account", [nameSlot,
    ⟨"balance", "Bounded", some (.integer 0), true⟩], true⟩

private def values : List Value :=
  [.unit, .boolean true, .boolean false, .integer (-123456789012345678901234567890),
    .text "类型 λ \"quote\"\n", .list [], .list [.unit, .integer 1, .text "x"],
    .dictionary [(.text "key", .integer 1), (.text "key", .integer 2)],
    .object [("x", .integer 1), ("x", .integer 2)], .function "increment", .descriptor "Integer",
    .list [.object [("callback", .function "increment"), ("type", .descriptor "Descriptor")]]]

private def checks : IO Unit := do
  let (boundedRegistry, boundedValue) ← IO.ofExcept
    ((DescriptorFactory.integerRange.call registry "Bounded" [.integer 0, .integer 100]).mapError reprStr)
  let bounded ← IO.ofExcept ((boundedRegistry.resolveDescriptor boundedValue).mapError reprStr)
  let (listRegistry, listValue) ← IO.ofExcept
    ((DescriptorFactory.listOf.call boundedRegistry "BoundedList" [boundedValue]).mapError reprStr)
  let listType ← IO.ofExcept ((listRegistry.resolveDescriptor listValue).mapError reprStr)
  unless (listType.accepts listRegistry 20 (.list [.integer 0, .integer 100])).toOption == some true &&
      (listType.accepts listRegistry 20 (.list [.integer 101])).toOption == some false &&
      (DescriptorFactory.listOf.call listRegistry "Bad" [.integer 1]).toOption.isNone &&
      (DescriptorFactory.listOf.call listRegistry "Bad" [.descriptor "unknown"]).toOption.isNone &&
      (DescriptorFactory.listOf.call listRegistry "BoundedList" [boundedValue]).toOption.isNone do
    throw (IO.userError "dependent type factory or registry admission")
  let (functionRegistry, functionValue) ← IO.ofExcept
    ((DescriptorFactory.functionOf.call listRegistry "Increment" [boundedValue, boundedValue]).mapError reprStr)
  let functionType ← IO.ofExcept ((functionRegistry.resolveDescriptor functionValue).mapError reprStr)
  unless (functionType.call functionRegistry 20 (.function "increment") (.integer 41)).toOption == some (.integer 42) &&
      (functionType.call functionRegistry 20 (.function "increment") (.integer 100) matches .error (.resultRejected _)) do
    throw (IO.userError "factory result is not a checked callable descriptor")
  let (objectRegistry, objectValue) ← IO.ofExcept ((DescriptorFactory.objectOf.call functionRegistry "Coordinate"
    [.object [("x", boundedValue), ("y", boundedValue)]]).mapError reprStr)
  let objectType ← IO.ofExcept ((objectRegistry.resolveDescriptor objectValue).mapError reprStr)
  unless (objectType.accepts objectRegistry 20 (.object [("x", .integer 1), ("y", .integer 2)])).toOption == some true do
    throw (IO.userError "ObjectOf dynamic parameters")
  let account ← IO.ofExcept ((schema.construct objectRegistry 30 [("name", .text "alice")]).mapError reprStr)
  let rebuilt ← IO.ofExcept ((RecordSchema.fromValue schema.describe).mapError reprStr)
  unless rebuilt == schema && (slotDescriptionType.accepts objectRegistry 30 nameSlot.describe).toOption == some true &&
      (recordSchemaType.accepts objectRegistry 30 schema.describe).toOption == some true &&
      account.slot? "balance" == some (.integer 0) do
    throw (IO.userError "self-describing slot/schema catalog or defaults")
  let .object slotFields := nameSlot.describe | throw (IO.userError "slot description is not an object")
  let .object schemaFields := schema.describe | throw (IO.userError "schema description is not an object")
  unless (SlotDescription.fromValue (.object (("type", .descriptor "Integer") :: slotFields))) matches
      .error (.duplicateSlot "type") do
    throw (IO.userError "ambiguous slot catalog was accepted")
  unless (RecordSchema.fromValue (.object (("sealed", .boolean false) :: schemaFields))) matches
      .error (.duplicateSlot "sealed") do
    throw (IO.userError "ambiguous record catalog was accepted")
  let inspected ← IO.ofExcept ((schema.inspect objectRegistry 30 account).mapError reprStr)
  unless inspected matches .list [_, _] do throw (IO.userError "generated field inspection")
  let changed ← IO.ofExcept ((schema.patch objectRegistry 30 account
    [("balance", .integer 2), ("balance", .integer 7)]).mapError reprStr)
  unless changed.slot? "balance" == some (.integer 7) && changed.slot? "name" == account.slot? "name" &&
      account.slot? "balance" == some (.integer 0) &&
      (schema.set objectRegistry 30 account "name" (.text "other")).toOption.isNone &&
      (schema.set objectRegistry 30 account "balance" (.integer 101)).toOption.isNone &&
      (schema.patch objectRegistry 30 (.object []) []).toOption.isNone &&
      (schema.construct objectRegistry 30 [("extra", .unit)]).toOption.isNone &&
      (schema.construct objectRegistry 30 [("balance", .integer 1), ("balance", .integer 2)]).toOption.isNone do
    throw (IO.userError "generated update/refinement/frame gate")
  for n in List.range 101 do
    let value ← IO.ofExcept ((schema.construct objectRegistry 30 [("balance", .integer (Int.ofNat n))]).mapError reprStr)
    let wire ← IO.ofExcept ((schema.encodeText objectRegistry 30 value).mapError reprStr)
    let roundTrip ← IO.ofExcept ((schema.decodeText objectRegistry 30 wire).mapError reprStr)
    unless roundTrip == value do throw (IO.userError "generated schema wire round trip")
  let top : Descriptor := ⟨"Top", .top, []⟩
  for value in values do
    let text ← IO.ofExcept ((top.encodeText objectRegistry 30 value).mapError reprStr)
    let bytes ← IO.ofExcept ((top.encodeBytes objectRegistry 30 value).mapError reprStr)
    let decoded ← IO.ofExcept ((top.decodeText objectRegistry 30 text).mapError reprStr)
    let decodedBytes ← IO.ofExcept ((top.decodeBytes objectRegistry 30 bytes).mapError reprStr)
    unless decoded.value == value && decodedBytes.value == value do
      throw (IO.userError "dynamic value exact text/bytes round trip")
  unless (bounded.decodeJson objectRegistry 10 (.arr #[.str "integer", .str "101"])).toOption.isNone &&
      (top.decodeJson objectRegistry 10 (.arr #[.str "integer", .str "01"])).toOption.isNone &&
      (top.decodeJson objectRegistry 10 (.arr #[.str "unit", .str "extra"])).toOption.isNone &&
      (top.decodeJson objectRegistry 0 (.arr #[.str "unit"])).toOption.isNone &&
      (top.decodeBytes objectRegistry 10 ⟨#[255]⟩).toOption.isNone &&
      (top.decodeText objectRegistry 10 "[\"function\",\"unknown\"]").toOption.isNone &&
      (top.decodeText objectRegistry 10 "[\"list\",[[\"descriptor\",\"unknown\"]]]").toOption.isNone do
    throw (IO.userError "malformed/refinement/identity wire refusal")
  IO.println s!"DYNAMIC-SCHEMA-OK factories=runtimeParameters fieldCatalog=selfDescribing schemaRoundTrips=101 valueRoundTrips={values.length * 2} identityGate=currentRegistry"

#eval checks
end LeanPoo.Tests.DynamicSchema
