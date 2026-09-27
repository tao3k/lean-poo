import LeanPoo.Object.Generic
import LeanPoo.Prototype.Class

/-!
Runtime class and slot descriptors for the existing typed C4 object model.
These values describe object shapes and defaults; `Memoized` still owns slot
evaluation and Lean's key-indexed family owns each slot's static type.
-/

namespace LeanPoo.Object

universe u v

/-- A runtime condition for one statically typed slot. -/
structure SlotRule (Key : Type u) (Value : Key → Type v) where
  key : Key
  accepts : Value key → Bool := fun _ => true
  optional : Bool := false
  fixed : Bool := false
  default : Option (Value key) := none
  compute : Option (Prototype.SlotSpec (Self Key Value) (Option (Value key))) := none
  json : Option (Prototype.JsonCodec (Value key)) := none

/-- One descriptor owns both runtime membership and the slot's JSON codec. -/
def SlotRule.fromDescriptor {Key : Type u} {Value : Key → Type v}
    (key : Key) (descriptor : Prototype.Descriptor (Value key)) :
    SlotRule Key Value :=
  { key
    accepts := descriptor.accepts
    default := descriptor.prototypeValue
    json := descriptor.json }

/-- Reuse Lean's JSON type classes for a statically typed slot. -/
def SlotRule.withJson {Key : Type u} {Value : Key → Type v}
    (rule : SlotRule Key Value)
    [Lean.ToJson (Value rule.key)] [Lean.FromJson (Value rule.key)] :
    SlotRule Key Value :=
  { rule with json := some ⟨Lean.toJson, Lean.fromJson?⟩ }

/-- A fixed-value rule both defines and recognizes its slot. -/
def SlotRule.constant {Key : Type u} {Value : Key → Type v}
    (key : Key) [BEq (Value key)] (value : Value key) : SlotRule Key Value :=
  { key
    accepts := fun candidate => candidate == value
    fixed := true
    compute := some (.constant (some value)) }

def SlotRule.acceptsObject {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (rule : SlotRule Key Value) (object : Memoized Key Value) : Bool :=
  match object.read rule.key with
  | some value => rule.accepts value
  | none => rule.optional

/-- A class describes a finite typed object shape and its default prototype
declaration. A sealed class rejects any declared key outside its rules. -/
structure ClassSpec (Key : Type u) (Value : Key → Type v) where
  name : String
  rules : List (SlotRule Key Value)
  sealed : Bool := false

/-- Repeated declarations of one key obey last-write-wins while retaining
the key's first declaration position, as typed object declarations do. -/
def ClassSpec.effectiveRules {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (classSpec : ClassSpec Key Value) :
    List (SlotRule Key Value) :=
  classSpec.rules.foldl (fun current rule =>
    if current.any (fun old => decide (old.key = rule.key)) then
      current.map (fun old =>
        if decide (old.key = rule.key) then rule else old)
    else current ++ [rule]) []

/-- Extend a runtime class descriptor with typed rules. A child rule
replaces a parent rule at the same key; otherwise parent order is retained. -/
def ClassSpec.derive {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (parent : ClassSpec Key Value) (name : String)
    (rules : List (SlotRule Key Value)) (sealed : Bool := parent.sealed) :
    ClassSpec Key Value :=
  { name
    rules := parent.effectiveRules ++ rules
    sealed }

/-- Field names retain their first declaration position even when a child
replaces an inherited rule. -/
def ClassSpec.fieldNames {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (classSpec : ClassSpec Key Value) : List Key :=
  classSpec.effectiveRules.map (fun rule => rule.key)

/-- A class layer is itself a delayed prototype for a class descriptor.
`Prototype.Object` can retain and extend it after instantiation. -/
def ClassSpec.layer {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (name : String) (rules : List (SlotRule Key Value))
    (sealed : Bool) : Prototype.DelayedProto
      (ClassSpec Key Value) (ClassSpec Key Value) (ClassSpec Key Value) :=
  fun _ inherited => (inherited.get).derive name rules sealed

def ClassSpec.toDeclaration {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (classSpec : ClassSpec Key Value) :
    Declaration Key Value :=
  classSpec.effectiveRules.foldl (fun declaration rule =>
    let declaration := match rule.default with
      | some value => declaration.withDefault rule.key value
      | none => declaration
    match rule.compute with
    | some specification => declaration.withSlot rule.key specification
    | none => declaration) Declaration.empty

/-- Build a standalone instance from the class prototype using the same C4
compiler and memoized evaluator as every other object. -/
def ClassSpec.instantiate {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) :
    Except C4.Error (Memoized Key Value) := do
  let empty : Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  return (← LeanPoo.mix empty classSpec.name [] classSpec.toDeclaration).memoize

def ClassSpec.acceptsObject {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) (object : Memoized Key Value) : Bool :=
  classSpec.effectiveRules.all (fun rule => rule.acceptsObject object) &&
    (!classSpec.sealed ||
      (LeanPoo.allSlots object.plan).all (fun key =>
        classSpec.effectiveRules.any (fun rule => decide (key = rule.key))))

def ClassSpec.validateObject {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) (object : Memoized Key Value) :
    Except String (Memoized Key Value) :=
  if classSpec.acceptsObject object then .ok object
  else .error s!"object rejected by {classSpec.name}"

/-- Use the same runtime descriptor API as ordinary and parameterized types. -/
def ClassSpec.toDescriptor {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) :
    Prototype.Descriptor (Memoized Key Value) :=
  { name := classSpec.name
    accepts := classSpec.acceptsObject
    display := fun object => s!"{classSpec.name} object {object.plan.root}" }

private def ClassSpec.jsonNames {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (classSpec : ClassSpec Key Value)
    (keyName : Key → String) : List String :=
  classSpec.effectiveRules.filterMap fun rule =>
    if rule.json.isSome && !rule.fixed && rule.compute.isNone then
      some (keyName rule.key)
    else none

private def ClassSpec.checkJsonNames {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (classSpec : ClassSpec Key Value) (keyName : Key → String) :
    Except String Unit := do
  let names := classSpec.jsonNames keyName
  unless names.length == (C4.unique names).length do
    throw s!"duplicate JSON slot names for {classSpec.name}"

/-- Serialize the declared JSON slots of a validated object. Computed
slots without a codec stay in the prototype and are recomputed on decoding. -/
def ClassSpec.encodeJson {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) (keyName : Key → String)
    (object : Memoized Key Value) : Except String Lean.Json := do
  classSpec.checkJsonNames keyName
  unless classSpec.acceptsObject object do
    throw s!"object rejected by {classSpec.name}"
  let fields ← classSpec.effectiveRules.foldlM (fun fields rule =>
    match if rule.fixed || rule.compute.isSome then none else rule.json with
    | none => .ok fields
    | some codec =>
      match object.read rule.key with
      | some value => .ok (fields ++ [(keyName rule.key, codec.encode value)])
      | none => if rule.optional then .ok fields
        else .error s!"missing serializable slot: {keyName rule.key}") []
  return Lean.Json.mkObj fields

/-- Decode direct values into a typed declaration while preserving the
class's computed slot specifications and defaults. -/
def ClassSpec.decodeJson {Key : Type} {Value : Key → Type}
    [DecidableEq Key]
    (classSpec : ClassSpec Key Value) (keyName : Key → String)
    (raw : Lean.Json) : Except String (Declaration Key Value) := do
  classSpec.checkJsonNames keyName
  let fields : Std.TreeMap.Raw String Lean.Json compare ← raw.getObj?
  if classSpec.sealed && fields.toList.any (fun (name, _) =>
      !classSpec.effectiveRules.any (fun rule =>
        rule.json.isSome && !rule.fixed && rule.compute.isNone &&
          keyName rule.key == name)) then
    throw s!"unknown JSON slot for {classSpec.name}"
  classSpec.effectiveRules.foldlM (fun declaration rule => do
    match fields.get? (keyName rule.key),
        (if rule.fixed || rule.compute.isSome then none else rule.json) with
    | some value, some codec =>
      let decoded ← codec.decode value
      unless rule.accepts decoded do
        throw s!"slot rejected by {classSpec.name}: {keyName rule.key}"
      return declaration.withValue rule.key decoded
    | some _, none =>
      throw s!"slot has no JSON codec: {keyName rule.key}"
    | none, _ =>
      if rule.optional || rule.default.isSome || rule.compute.isSome then
        return declaration
      else
        throw s!"missing required slot: {keyName rule.key}")
    classSpec.toDeclaration

inductive ClassDecodeError where
  | codec (message : String)
  | c4 (error : C4.Error)
  | rejected (name : String)
  deriving Repr

/-- Deserialize and validate a complete object, leaving C4 ordering and
computed slot evaluation with the existing compiler and memoized instance. -/
def ClassSpec.decodeObjectJson {Key : Type} {Value : Key → Type}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (classSpec : ClassSpec Key Value) (keyName : Key → String)
    (raw : Lean.Json) : Except ClassDecodeError (Memoized Key Value) := do
  let declaration ← (classSpec.decodeJson keyName raw).mapError .codec
  let empty : Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let object := (← (LeanPoo.mix empty classSpec.name [] declaration).mapError .c4).memoize
  let _ ← (classSpec.validateObject object).mapError
    (fun _ => ClassDecodeError.rejected classSpec.name)
  return object

end LeanPoo.Object
