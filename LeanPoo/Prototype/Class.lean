import Lean
import LeanPoo.Prototype.Object

/-!
The paper's class construction: a class is a prototype for a type
descriptor. Lean's type parameter supplies the static type; the descriptor
adds runtime recognition and presentation for a refinement of that type.
-/

namespace LeanPoo.Prototype

universe u

/-- A typed JSON boundary for a runtime descriptor. Lean's native JSON
representation supplies the wire format; descriptors supply refinement
checks after decoding. -/
structure JsonCodec (α : Type u) where
  encode : α → Lean.Json
  decode : Lean.Json → Except String α

/-- JSON object keys are strings. A non-string Lean key supplies an explicit
reversible textual mapping instead of an implicit dynamic coercion. -/
structure TextCodec (α : Type u) where
  encode : α → String
  decode : String → Except String α

def TextCodec.string : TextCodec String :=
  { encode := id, decode := .ok }

def TextCodec.nat : TextCodec Nat :=
  { encode := toString
    decode := fun source =>
      match source.toNat? with
      | some value => .ok value
      | none => .error s!"invalid natural map key: {source}" }

def JsonCodec.listOf (element : JsonCodec α) : JsonCodec (List α) :=
  { encode := fun values => Lean.Json.arr (values.toArray.map element.encode)
    decode := fun raw => do
      let values ← raw.getArr?
      values.toList.mapM element.decode }

def JsonCodec.arrayOf (element : JsonCodec α) : JsonCodec (Array α) :=
  { encode := fun values => Lean.Json.arr (values.map element.encode)
    decode := fun raw => do
      let values ← raw.getArr?
      values.mapM element.decode }

def JsonCodec.optionOf (element : JsonCodec α) : JsonCodec (Option α) :=
  { encode := fun value => match value with
      | none => Lean.Json.mkObj [("tag", "none")]
      | some item => Lean.Json.mkObj
          [("tag", "some"), ("value", element.encode item)]
    decode := fun raw => do
      let tag ← raw.getObjValAs? String "tag"
      match tag with
      | "none" => return none
      | "some" => return some (← element.decode (← raw.getObjVal? "value"))
      | _ => throw s!"unknown option tag: {tag}" }

def JsonCodec.pairOf (left : JsonCodec α) (right : JsonCodec β) :
    JsonCodec (α × β) :=
  { encode := fun value => Lean.Json.arr #[left.encode value.1, right.encode value.2]
    decode := fun raw => do
      let values ← raw.getArr?
      match values.toList with
      | [first, second] => return (← left.decode first, ← right.decode second)
      | _ => throw "expected a two-element JSON array" }

def JsonCodec.sumOf (left : JsonCodec α) (right : JsonCodec β) :
    JsonCodec (Sum α β) :=
  { encode := fun value => match value with
      | .inl item => Lean.Json.mkObj [("tag", "left"), ("value", left.encode item)]
      | .inr item => Lean.Json.mkObj [("tag", "right"), ("value", right.encode item)]
    decode := fun raw => do
      let tag ← raw.getObjValAs? String "tag"
      let value ← raw.getObjVal? "value"
      match tag with
      | "left" => return .inl (← left.decode value)
      | "right" => return .inr (← right.decode value)
      | _ => throw s!"unknown sum tag: {tag}" }

def JsonCodec.mapOf {Key : Type} [BEq Key] [Hashable Key]
    (key : TextCodec Key) (element : JsonCodec α) :
    JsonCodec (Std.HashMap Key α) :=
  { encode := fun values => Lean.Json.mkObj
      (values.toList.map fun (name, value) => (key.encode name, element.encode value))
    decode := fun raw => do
      let fields ← raw.getObj?
      fields.toList.foldlM (fun values (name, value) => do
        let decodedKey ← key.decode name
        if values.contains decodedKey then
          throw s!"duplicate decoded map key: {name}"
        return values.insert decodedKey (← element.decode value)) {} }

def JsonCodec.stringMapOf (element : JsonCodec α) :
    JsonCodec (Std.HashMap String α) :=
  JsonCodec.mapOf TextCodec.string element

/-- Preserve arbitrary bytes as JSON numbers, including invalid UTF-8. -/
def JsonCodec.bytes : JsonCodec ByteArray :=
  { encode := fun bytes => Lean.Json.arr
      (bytes.data.map fun byte => Lean.toJson byte.toNat)
    decode := fun raw => do
      let values ← raw.getArr?
      let bytes ← values.mapM fun value => do
        let number ← value.getNat?
        if number < 256 then return UInt8.ofNat number
        else throw "byte outside 0..255"
      return ByteArray.mk bytes }

/-- Runtime operations associated with a Lean type or a refinement of it. -/
structure Descriptor (α : Type u) where
  name : String
  accepts : α → Bool
  display : α → String
  prototypeValue : Option α := none
  json : Option (JsonCodec α) := none

def Descriptor.top (name : String) (display : α → String) : Descriptor α :=
  { name, accepts := fun _ => true, display }

def Descriptor.bottom (name : String) (display : α → String) : Descriptor α :=
  { name, accepts := fun _ => false, display }

/-- A bounded natural uses Lean's `Fin` proof as its static representation;
the runtime decoder checks the bound before constructing that proof. -/
def Descriptor.fin (bound : Nat) : Descriptor (Fin bound) :=
  { name := s!"Fin {bound}"
    accepts := fun _ => true
    display := fun value => toString value.val
    json := some {
      encode := fun value => Lean.toJson value.val
      decode := fun raw => do
        let value ← raw.getNat?
        if smaller : value < bound then
          return ⟨value, smaller⟩
        else
          throw s!"number outside Fin {bound}" } }

/-- Arbitrary byte sequences are native Lean values, independent of the
UTF-8 JSON representation used for other descriptor byte boundaries. -/
def Descriptor.bytes : Descriptor ByteArray :=
  { name := "Bytes"
    accepts := fun _ => true
    display := fun bytes => s!"{bytes.size} bytes"
    json := some JsonCodec.bytes }

/-- Attach Lean's existing JSON type-class instances to a descriptor. -/
def Descriptor.withJson [Lean.ToJson α] [Lean.FromJson α]
    (descriptor : Descriptor α) : Descriptor α :=
  { descriptor with json := some ⟨Lean.toJson, Lean.fromJson?⟩ }

/-- A type descriptor may provide a default prototype value for a slot
whose class rule does not define one directly. -/
def Descriptor.withPrototypeValue (descriptor : Descriptor α) (value : α) :
    Except String (Descriptor α) := do
  unless descriptor.accepts value do
    throw s!"prototype value rejected by {descriptor.name}"
  return { descriptor with prototypeValue := some value }

def Descriptor.validate (descriptor : Descriptor α) (value : α) :
    Except String α :=
  if descriptor.accepts value then .ok value
  else .error s!"value rejected by {descriptor.name}"

def Descriptor.encodeJson (descriptor : Descriptor α) (value : α) :
    Except String Lean.Json :=
  match descriptor.validate value with
  | .error error => .error error
  | .ok accepted =>
    match descriptor.json with
    | none => .error s!"no JSON codec for {descriptor.name}"
    | some codec => .ok (codec.encode accepted)

def Descriptor.decodeJson (descriptor : Descriptor α) (raw : Lean.Json) :
    Except String α := do
  let some codec := descriptor.json |
    throw s!"no JSON codec for {descriptor.name}"
  let value ← codec.decode raw
  descriptor.validate value

/-- A Lean-native textual source form for JSON-capable descriptors. -/
def Descriptor.encodeText (descriptor : Descriptor α) (value : α) :
    Except String String := do
  return (← descriptor.encodeJson value).compress

def Descriptor.decodeText (descriptor : Descriptor α) (source : String) :
    Except String α := do
  descriptor.decodeJson (← Lean.Json.parse source)

/-- A portable byte representation of the JSON codec. This is a Lean-native
UTF-8 format; it does not claim Gerbil's binary wire compatibility. -/
def Descriptor.encodeBytes (descriptor : Descriptor α) (value : α) :
    Except String ByteArray := do
  return (← descriptor.encodeText value).toUTF8

def Descriptor.decodeBytes (descriptor : Descriptor α) (bytes : ByteArray) :
    Except String α := do
  let some source := String.fromUTF8? bytes |
    throw "invalid UTF-8 descriptor bytes"
  descriptor.decodeText source

/-- A runtime refinement retains the original Lean type and descriptor
operations while restricting the values recognized by the descriptor. -/
def Descriptor.refine (base : Descriptor α) (name : String)
    (predicate : α → Bool) : Descriptor α :=
  { base with
    name
    accepts := fun value => base.accepts value && predicate value
    prototypeValue := base.prototypeValue.filter predicate }

def Descriptor.bytesN (count : Nat) : Descriptor ByteArray :=
  (Descriptor.bytes).refine s!"Bytes {count}" (fun bytes => bytes.size == count)

/-- An equality refinement corresponds to a runtime singleton type. -/
def Descriptor.exactly [BEq α] (base : Descriptor α) (value : α) :
    Descriptor α :=
  base.refine s!"Exactly {base.display value}" (· == value)

/-- A finite enumeration is a refinement of one statically known Lean type. -/
def Descriptor.oneOf [BEq α] (base : Descriptor α)
    (values : List α) : Descriptor α :=
  base.refine s!"Enum {base.name}" (fun candidate => values.any (· == candidate))

/-- A union of refinements over the same Lean type. When both branches can
decode JSON, decoding tries each branch and retains only accepted values. -/
def Descriptor.union (left right : Descriptor α) : Descriptor α :=
  { name := s!"{left.name} ∪ {right.name}"
    accepts := fun value => left.accepts value || right.accepts value
    display := fun value =>
      if left.accepts value then left.display value else right.display value
    prototypeValue := left.prototypeValue.orElse fun _ => right.prototypeValue
    json := do
      let leftCodec ← left.json
      let rightCodec ← right.json
      let decodeBranch (descriptor : Descriptor α) (codec : JsonCodec α)
          (raw : Lean.Json) : Except String α := do
        let value ← codec.decode raw
        if descriptor.accepts value then return value
        else throw s!"value rejected by {descriptor.name}"
      return {
        encode := fun value =>
          if left.accepts value then leftCodec.encode value
          else rightCodec.encode value
        decode := fun raw =>
          match decodeBranch left leftCodec raw with
          | .ok value => .ok value
          | .error _ => decodeBranch right rightCodec raw } }

/-- Intersection retains the left codec where available and checks both
refinements at the outer descriptor boundary. -/
def Descriptor.intersect (left right : Descriptor α) : Descriptor α :=
  { name := s!"{left.name} ∩ {right.name}"
    accepts := fun value => left.accepts value && right.accepts value
    display := left.display
    prototypeValue := (left.prototypeValue.filter right.accepts).orElse
      (fun _ => right.prototypeValue.filter left.accepts)
    json := left.json.orElse fun _ => right.json }

/-- Lean fixes a function's domain and codomain statically. A runtime
descriptor can still check refinements at both call boundaries. -/
def Descriptor.functionOf (input : Descriptor α) (output : Descriptor β) :
    Descriptor (α → β) :=
  { name := s!"{input.name} → {output.name}"
    accepts := fun _ => true
    display := fun _ => s!"function {input.name} → {output.name}" }

def Descriptor.checkedCall (input : Descriptor α) (output : Descriptor β)
    (function : α → β) (argument : α) : Except String β := do
  unless input.accepts argument do
    throw s!"argument rejected by {input.name}"
  let result := function argument
  unless output.accepts result do
    throw s!"result rejected by {output.name}"
  return result

/-- A class is an open-recursive, inheritable descriptor computation. -/
abbrev DescriptorClass (α : Type u) :=
  DelayedProto (Descriptor α) (Descriptor α) (Descriptor α)

/-- Close the descriptor fixed point while retaining its class prototype. -/
unsafe def DescriptorClass.instantiate (prototype : DescriptorClass α)
    (base : Descriptor α) : Object (Descriptor α) (Descriptor α) :=
  Object.ofPrototype prototype (Thunk.pure base)

/-- A parameterized type descriptor built from an element descriptor. -/
def Descriptor.listOf (element : Descriptor α) : Descriptor (List α) :=
  { name := s!"List {element.name}"
    accepts := fun values => values.all element.accepts
    display := fun values => s!"{element.name} list of length {values.length}"
    prototypeValue := some []
    json := element.json.map JsonCodec.listOf }

def Descriptor.arrayOf (element : Descriptor α) : Descriptor (Array α) :=
  { name := s!"Array {element.name}"
    accepts := fun values => values.all element.accepts
    display := fun values => s!"{element.name} array of length {values.size}"
    prototypeValue := some #[]
    json := element.json.map JsonCodec.arrayOf }

def Descriptor.stringMapOf (element : Descriptor α) :
    Descriptor (Std.HashMap String α) :=
  { name := s!"String → {element.name}"
    accepts := fun values => values.toList.all (fun (_, value) => element.accepts value)
    display := fun values => s!"{element.name} map of size {values.size}"
    prototypeValue := some {}
    json := element.json.map JsonCodec.stringMapOf }

/-- A homogeneous map with an explicit key-to-JSON-field conversion. -/
def Descriptor.mapOf {Key : Type} [BEq Key] [Hashable Key]
    (key : TextCodec Key) (element : Descriptor α) :
    Descriptor (Std.HashMap Key α) :=
  { name := s!"Map → {element.name}"
    accepts := fun values => values.toList.all (fun (_, value) => element.accepts value)
    display := fun values => s!"{element.name} map of size {values.size}"
    prototypeValue := some {}
    json := element.json.map (JsonCodec.mapOf key) }

/-- Lean's `Option` is the native counterpart of a parameterized maybe type. -/
def Descriptor.optionOf (element : Descriptor α) : Descriptor (Option α) :=
  { name := s!"Option {element.name}"
    accepts := fun value => value.elim true element.accepts
    display := fun value => value.elim "none" element.display
    prototypeValue := some none
    json := element.json.map JsonCodec.optionOf }

/-- A product descriptor checks both components using their own descriptors. -/
def Descriptor.pairOf (left : Descriptor α) (right : Descriptor β) :
    Descriptor (α × β) :=
  { name := s!"{left.name} × {right.name}"
    accepts := fun value => left.accepts value.1 && right.accepts value.2
    display := fun value => s!"({left.display value.1}, {right.display value.2})"
    prototypeValue := do
      return (← left.prototypeValue, ← right.prototypeValue)
    json := do
      let leftCodec ← left.json
      let rightCodec ← right.json
      return JsonCodec.pairOf leftCodec rightCodec }

/-- An algebraic sum uses Lean's native tagged union. -/
def Descriptor.sumOf (left : Descriptor α) (right : Descriptor β) :
    Descriptor (Sum α β) :=
  { name := s!"{left.name} + {right.name}"
    accepts := fun value => match value with
      | .inl item => left.accepts item
      | .inr item => right.accepts item
    display := fun value => match value with
      | .inl item => s!"left {left.display item}"
      | .inr item => s!"right {right.display item}"
    prototypeValue := left.prototypeValue.map Sum.inl |>.orElse
      (fun _ => right.prototypeValue.map Sum.inr)
    json := do
      let leftCodec ← left.json
      let rightCodec ← right.json
      return JsonCodec.sumOf leftCodec rightCodec }

end LeanPoo.Prototype
