import LeanPoo.Prototype.Class

namespace LeanPoo.Prototype

/-- Runtime descriptions of a finite dependent record's fields. Lean owns
field carrier types; descriptors own refinements, presentation and codecs. -/
structure RecordDescription (Key : Type) (Value : Key → Type) where
  name : String
  keys : List Key
  label : Key → String
  field : (key : Key) → Descriptor (Value key)

def RecordDescription.accepts (description : RecordDescription Key Value)
    (record : Record Key Value) : Bool :=
  description.keys.all fun key =>
    (record.lookup key).any (description.field key).accepts

def RecordDescription.toDescriptor (description : RecordDescription Key Value) :
    Descriptor (Record Key Value) :=
  { name := description.name
    accepts := description.accepts
    display := fun _ => s!"{description.name}: {description.keys.length} declared fields" }

/-- Generate a human/tool-facing schema from the same field description that
owns validation. This describes callable fields, without serializing closures. -/
def RecordDescription.schema (description : RecordDescription Key Value) : Lean.Json :=
  Lean.Json.mkObj [("name",.str description.name), ("fields",.arr (description.keys.map fun key =>
    Lean.Json.mkObj [("name",.str (description.label key)),
      ("type",.str (description.field key).name),
      ("json",.bool (description.field key).json.isSome)]).toArray)]

/-- Generated inspection uses each field's codec or presentation method. -/
def RecordDescription.inspect (description : RecordDescription Key Value)
    (record : Record Key Value) : Except String Lean.Json := do
  let pairs ← description.keys.mapM fun key => do
    let some value := record.lookup key | throw s!"missing field: {description.label key}"
    let descriptor := description.field key
    let _ ← descriptor.validate value
    let rendered ← match descriptor.json with
      | some _ => descriptor.encodeJson value
      | none => pure (.str (descriptor.display value))
    return (description.label key,rendered)
  return Lean.Json.mkObj pairs

/-- Type-indexed updates retain the other values and enforce field refinement. -/
def RecordDescription.set [DecidableEq Key] (description : RecordDescription Key Value)
    (record : Record Key Value) (key : Key) (value : Value key) : Except String (Record Key Value) := do
  unless description.keys.any (fun candidate => decide (candidate = key)) do throw "undeclared field"
  let checked ← (description.field key).validate value
  return { record with lookup := fun query =>
    if same : query = key then some (same.symm ▸ checked) else record.lookup query }

/-- A declared accepted update supplies exactly the requested value. -/
theorem RecordDescription.set_lookup_same [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value)
    (key : Key) (value : Value key)
    (declared : description.keys.any (fun candidate => decide (candidate = key)) = true)
    (accepted : (description.field key).accepts value = true) :
    (description.set record key value).map (fun updated => updated.lookup key) = .ok (some value) := by
  simp [set, Descriptor.validate, declared, accepted, Except.map, Functor.map]

/-- Updating one field preserves every differently named dependent field. -/
theorem RecordDescription.set_lookup_other [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value)
    (key query : Key) (value : Value key)
    (different : query ≠ key)
    (declared : description.keys.any (fun candidate => decide (candidate = key)) = true)
    (accepted : (description.field key).accepts value = true) :
    (description.set record key value).map (fun updated => updated.lookup query) = .ok (record.lookup query) := by
  simp [set, Descriptor.validate, declared, accepted, different, Except.map, Functor.map]

end LeanPoo.Prototype
