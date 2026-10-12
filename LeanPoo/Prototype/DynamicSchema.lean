import LeanPoo.Prototype.DynamicCodec

/-! Runtime dependent descriptor construction and generated field tools.
Factories consume ordinary dynamic parameters and return registered descriptor
values. One slot catalog owns defaults, recognition, inspection and updates. -/
namespace LeanPoo.Prototype.Dynamic

inductive SchemaError where
  | descriptor (error : Error)
  | wire (error : WireError)
  | invalidArgument (message : String)
  | duplicateIdentity (identity : String)
  | duplicateSlot (name : String)
  | missingSlot (name : String)
  | unknownSlot (name : String)
  | readOnlySlot (name : String)
  deriving Repr, BEq

def Registry.resolveDescriptor (registry : Registry) (value : Value) :
    Except SchemaError Descriptor :=
  match value with
  | .descriptor identity =>
    match registry.descriptor? identity with
    | some descriptor => .ok descriptor
    | none => .error (.descriptor (.unknownDescriptor identity))
  | _ => .error (.descriptor .expectedDescriptor)

/-- New identities are explicit and unique. Existing identity bindings are
preserved as the immutable registry grows. -/
def Registry.defineDescriptor (registry : Registry) (identity : String)
    (descriptor : Descriptor) : Except SchemaError (Registry × Value) := do
  if identity.isEmpty then throw (.invalidArgument "empty descriptor identity")
  if (registry.descriptor? identity).isSome then throw (.duplicateIdentity identity)
  return ({ registry with descriptors := (identity, descriptor) :: registry.descriptors }, .descriptor identity)

structure DescriptorFactory where
  name : String
  build : Registry → List Value → Except SchemaError Descriptor

def DescriptorFactory.call (factory : DescriptorFactory) (registry : Registry)
    (identity : String) (arguments : List Value) : Except SchemaError (Registry × Value) := do
  registry.defineDescriptor identity (← factory.build registry arguments)

def DescriptorFactory.listOf : DescriptorFactory :=
  ⟨"ListOf", fun registry arguments => do
    let [element] := arguments | throw (.invalidArgument "ListOf expects one descriptor")
    let descriptor ← registry.resolveDescriptor element
    return ⟨s!"ListOf {descriptor.name}", .listOf descriptor.contract, []⟩⟩

def DescriptorFactory.dictionaryOf : DescriptorFactory :=
  ⟨"DictionaryOf", fun registry arguments => do
    let [key, value] := arguments | throw (.invalidArgument "DictionaryOf expects two descriptors")
    let keyType ← registry.resolveDescriptor key
    let valueType ← registry.resolveDescriptor value
    return ⟨s!"DictionaryOf {keyType.name} {valueType.name}",
      .dictionaryOf keyType.contract valueType.contract, []⟩⟩

def DescriptorFactory.functionOf : DescriptorFactory :=
  ⟨"FunctionOf", fun registry arguments => do
    let [input, output] := arguments | throw (.invalidArgument "FunctionOf expects two descriptors")
    return Descriptor.functionOf (← registry.resolveDescriptor input) (← registry.resolveDescriptor output)⟩

/-- This factory depends on ordinary runtime integers, not only type values. -/
def DescriptorFactory.integerRange : DescriptorFactory :=
  ⟨"IntegerRange", fun _ arguments => do
    let [.integer lower, .integer upper] := arguments |
      throw (.invalidArgument "IntegerRange expects two integers")
    if upper < lower then throw (.invalidArgument "reversed integer range")
    return ⟨s!"IntegerRange {lower} {upper}", .integerRange lower upper, []⟩⟩

def DescriptorFactory.union : DescriptorFactory :=
  ⟨"Union", fun registry arguments => do
    let [left, right] := arguments | throw (.invalidArgument "Union expects two descriptors")
    let leftType ← registry.resolveDescriptor left
    let rightType ← registry.resolveDescriptor right
    return ⟨s!"{leftType.name} | {rightType.name}", .union leftType.contract rightType.contract, []⟩⟩

def DescriptorFactory.intersection : DescriptorFactory :=
  ⟨"Intersection", fun registry arguments => do
    let [left, right] := arguments | throw (.invalidArgument "Intersection expects two descriptors")
    let leftType ← registry.resolveDescriptor left
    let rightType ← registry.resolveDescriptor right
    return ⟨s!"{leftType.name} & {rightType.name}", .intersection leftType.contract rightType.contract, []⟩⟩

structure SlotDescription where
  name : String
  typeIdentity : String
  defaultValue : Option Value := none
  writable : Bool := true
  deriving Repr, BEq

def SlotDescription.describe (slot : SlotDescription) : Value :=
  .object [("name", .text slot.name), ("type", .descriptor slot.typeIdentity),
    ("default", .list slot.defaultValue.toList), ("writable", .boolean slot.writable)]

def slotDescriptionType : Descriptor :=
  ⟨"SlotDescription", .objectOf [("name", .text), ("type", .descriptor),
    ("default", .listOf .top), ("writable", .boolean)], []⟩

structure RecordSchema where
  name : String
  slots : List SlotDescription
  sealed : Bool := true
  deriving Repr, BEq

def RecordSchema.describe (schema : RecordSchema) : Value :=
  .object [("name", .text schema.name), ("slots", .list (schema.slots.map SlotDescription.describe)),
    ("sealed", .boolean schema.sealed)]

private def uniqueNames (names : List String) : Except SchemaError Unit :=
  let rec check (seen : List String) : List String → Except SchemaError Unit
    | [] => .ok ()
    | name :: rest =>
      if name ∈ seen then .error (.duplicateSlot name)
      else if name.isEmpty then .error (.invalidArgument "empty slot name")
      else check (name :: seen) rest
  check [] names

def SlotDescription.fromValue (value : Value) : Except SchemaError SlotDescription := do
  let .object fields := value | throw (.invalidArgument "expected a slot description object")
  uniqueNames (fields.map Prod.fst)
  let some (.text name) := value.slot? "name" | throw (.invalidArgument "slot name is required")
  let some (.descriptor identity) := value.slot? "type" |
    throw (.invalidArgument "slot type must be a descriptor")
  let some (.boolean writable) := value.slot? "writable" |
    throw (.invalidArgument "slot writable flag is required")
  let some (.list defaults) := value.slot? "default" |
    throw (.invalidArgument "slot default must be a list")
  let defaultValue ← match defaults with
    | [] => pure none
    | [value] => pure (some value)
    | _ => throw (.invalidArgument "slot default must contain zero or one value")
  return ⟨name, identity, defaultValue, writable⟩

def RecordSchema.fromValue (value : Value) : Except SchemaError RecordSchema := do
  let .object fields := value | throw (.invalidArgument "expected a record schema object")
  uniqueNames (fields.map Prod.fst)
  let some (.text name) := value.slot? "name" | throw (.invalidArgument "schema name is required")
  let some (.list slots) := value.slot? "slots" | throw (.invalidArgument "schema slots are required")
  let some (.boolean sealed) := value.slot? "sealed" | throw (.invalidArgument "schema sealed flag is required")
  let slots ← slots.mapM SlotDescription.fromValue
  uniqueNames (slots.map SlotDescription.name)
  return ⟨name, slots, sealed⟩

def recordSchemaType : Descriptor :=
  ⟨"RecordSchema", .objectOf [("name", .text), ("slots", .listOf slotDescriptionType.contract),
    ("sealed", .boolean)], []⟩

def RecordSchema.descriptor (schema : RecordSchema) (registry : Registry) :
    Except SchemaError Descriptor := do
  uniqueNames (schema.slots.map SlotDescription.name)
  let slots ← schema.slots.mapM fun slot => do
    let _ ← registry.resolveDescriptor (.descriptor slot.typeIdentity)
    return (slot.name, Contract.named slot.typeIdentity)
  return ⟨schema.name, .objectOf slots, [("schema", schema.describe)]⟩

private def RecordSchema.checkShape (schema : RecordSchema) (fields : List (String × Value)) :
    Except SchemaError Unit := do
  uniqueNames (fields.map Prod.fst)
  if schema.sealed then
    let _ ← fields.mapM fun field =>
      if schema.slots.any (fun slot => slot.name == field.1) then .ok ()
      else .error (.unknownSlot field.1)
    return ()

def RecordSchema.validate (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) : Except SchemaError Value := do
  let .object fields := value | throw (.invalidArgument "expected an object")
  schema.checkShape fields
  let descriptor ← schema.descriptor registry
  let admitted ← (descriptor.validate registry fuel value).mapError SchemaError.wire
  return admitted.value

/-- Defaults and supplied values enter the same refinement gate. Unknown,
duplicate, missing and invalid fields fail before an instance escapes. -/
def RecordSchema.construct (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (supplied : List (String × Value)) : Except SchemaError Value := do
  schema.checkShape supplied
  let fields ← schema.slots.mapM fun slot => do
    match (supplied.find? (fun entry => entry.1 == slot.name)).map Prod.snd with
    | some value => return (slot.name, value)
    | none =>
      let some value := slot.defaultValue | throw (.missingSlot slot.name)
      return (slot.name, value)
  let extra := supplied.filter fun entry => !(schema.slots.any (fun slot => slot.name == entry.1))
  schema.validate registry fuel (.object (fields ++ extra))

def RecordSchema.inspect (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) : Except SchemaError Value := do
  let checked ← schema.validate registry fuel value
  let slots ← schema.slots.mapM fun slot => do
    let some value := checked.slot? slot.name | throw (.missingSlot slot.name)
    return Value.object [("slot", slot.describe), ("value", value)]
  return .list slots

def RecordSchema.set (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (object : Value) (name : String) (value : Value) : Except SchemaError Value := do
  let .object fields ← schema.validate registry fuel object |
    throw (.invalidArgument "expected an object")
  let some slot := schema.slots.find? (fun slot => slot.name == name) | throw (.unknownSlot name)
  unless slot.writable do throw (.readOnlySlot name)
  schema.validate registry fuel (.object (fields.map fun entry =>
    if entry.1 == name then (name, value) else entry))

/-- Ordered edits are pure: a rejected later edit does not publish earlier
partial values. Mutable callers choose explicitly when to install the result. -/
def RecordSchema.patch (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (object : Value) (edits : List (String × Value)) : Except SchemaError Value := do
  let checked ← schema.validate registry fuel object
  edits.foldlM (fun current edit => schema.set registry fuel current edit.1 edit.2) checked

def RecordSchema.encodeText (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (object : Value) : Except SchemaError String := do
  let value ← schema.validate registry fuel object
  let descriptor ← schema.descriptor registry
  (descriptor.encodeText registry fuel value).mapError SchemaError.wire

def RecordSchema.decodeText (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (source : String) : Except SchemaError Value := do
  let descriptor ← schema.descriptor registry
  let decoded ← (descriptor.decodeText registry fuel source).mapError SchemaError.wire
  schema.validate registry fuel decoded.value

def DescriptorFactory.objectOf : DescriptorFactory :=
  ⟨"ObjectOf", fun registry arguments => do
    let [.object fields] := arguments | throw (.invalidArgument "ObjectOf expects named descriptors")
    uniqueNames (fields.map Prod.fst)
    let slots ← fields.mapM fun entry => do
      let descriptor ← registry.resolveDescriptor entry.2
      return (entry.1, descriptor.contract)
    return ⟨"ObjectOf", .objectOf slots, []⟩⟩

end LeanPoo.Prototype.Dynamic
