import LeanPoo.Prototype.RecordDescription

namespace LeanPoo.Prototype
namespace RecordCodec

private structure Field (Key : Type) (Value : Key → Type) where
  key : Key
  label : String
  descriptor : Descriptor (Value key)
  codec : JsonCodec (Value key)

private def accepts (fields : List (Field Key Value)) (record : Record Key Value) : Bool :=
  fields.all fun field => (record.lookup field.key).any field.descriptor.accepts

private def encode (fields : List (Field Key Value)) (record : Record Key Value) : Lean.Json :=
  Lean.Json.mkObj (fields.map fun field =>
    (field.label, match record.lookup field.key with
      | some value => field.codec.encode value
      | none => .null))

private def decode [DecidableEq Key] (fields : List (Field Key Value))
    (raw : Lean.Json) : Except String (Record Key Value) := do
  let object ← raw.getObj?
  let allowed := fields.map Field.label
  unless object.toList.all (fun entry => allowed.contains entry.1) do throw "unknown record field"
  fields.foldlM (fun record field => do
    let value ← field.codec.decode (← raw.getObjVal? field.label)
    return { record with lookup := fun query =>
      if same : query = field.key then some (same.symm ▸ value) else record.lookup query }) Record.empty

/-- Compile the field catalog once into a descriptor with a strict JSON codec.
All declared labels must be unique/nonempty and all fields need codecs. Descriptor.decodeJson
rejects unknown/missing fields and checks each refinement once. Encode admission goes
through Descriptor.encodeJson; direct JsonCodec.encode is its unchecked layer. -/
def prepare [DecidableEq Key] (description : RecordDescription Key Value) :
    Except String (Descriptor (Record Key Value)) := do
  let labels := description.keys.map description.label
  if labels.any String.isEmpty then throw "empty record field label"
  if labels.eraseDups.length != labels.length then throw "duplicate record field label"
  let fields ← (description.keys.zip labels).mapM fun (key,label) => do
    let descriptor := description.field key
    let some codec := descriptor.json | throw s!"no JSON codec for field: {label}"
    return Field.mk key label descriptor codec
  return { name := description.name
           accepts := accepts fields
           display := fun _ => s!"{description.name}: {fields.length} JSON fields"
           json := some { encode := encode fields, decode := decode fields } }

end RecordCodec
end LeanPoo.Prototype
