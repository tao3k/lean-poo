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

/-- An accepted field update keeps a previously valid dependent record valid. -/
theorem RecordDescription.set_preserves_accepts [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value)
    (key : Key) (value : Value key)
    (valid : description.accepts record = true)
    (declared : description.keys.any (fun candidate => decide (candidate = key)) = true)
    (accepted : (description.field key).accepts value = true) :
    (description.set record key value).map description.accepts = .ok true := by
  simp [set, Descriptor.validate, declared, accepted, Except.map, Functor.map,
    RecordDescription.accepts]
  intro query present
  by_cases same : query = key
  · subst query
    simp [accepted]
  · have previous := (List.all_eq_true.mp valid) query present
    simpa [RecordDescription.accepts, same] using previous

/-- Apply type-indexed edits in order. An error returns no intermediate record. -/
def RecordDescription.patch [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value) :
    List (Sigma Value) → Except String (Record Key Value)
  | [] => .ok record
  | edit :: edits => do
    let next ← description.set record edit.1 edit.2
    description.patch next edits

/-- A batch of admitted edits preserves the record's generated recognizer. -/
theorem RecordDescription.patch_preserves_accepts [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value)
    (edits : List (Sigma Value))
    (valid : description.accepts record = true)
    (declared : ∀ edit ∈ edits,
      description.keys.any (fun candidate => decide (candidate = edit.1)) = true)
    (accepted : ∀ edit ∈ edits, (description.field edit.1).accepts edit.2 = true) :
    (description.patch record edits).map description.accepts = .ok true := by
  induction edits generalizing record with
  | nil => simp [patch, valid, Except.map]
  | cons edit rest ih =>
    have thisDeclared := declared edit (by simp)
    have thisAccepted := accepted edit (by simp)
    have restDeclared : ∀ item ∈ rest,
        description.keys.any (fun candidate => decide (candidate = item.1)) = true := by
      intro item member
      exact declared item (by simp [member])
    have restAccepted : ∀ item ∈ rest, (description.field item.1).accepts item.2 = true := by
      intro item member
      exact accepted item (by simp [member])
    have step := description.set_preserves_accepts record edit.1 edit.2
      valid thisDeclared thisAccepted
    cases hset : description.set record edit.1 edit.2 with
    | error err => simp [hset, Except.map] at step
    | ok next =>
      have nextValid : description.accepts next = true := by
        simpa [hset, Except.map] using step
      simp only [patch, hset]
      exact ih next nextValid restDeclared restAccepted

/-- A batch of edits leaves every unmentioned key unchanged. -/
theorem RecordDescription.patch_lookup_untouched [DecidableEq Key]
    (description : RecordDescription Key Value) (record : Record Key Value)
    (edits : List (Sigma Value)) (query : Key)
    (declared : ∀ edit ∈ edits,
      description.keys.any (fun candidate => decide (candidate = edit.1)) = true)
    (accepted : ∀ edit ∈ edits, (description.field edit.1).accepts edit.2 = true)
    (untouched : ∀ edit ∈ edits, query ≠ edit.1) :
    (description.patch record edits).map (fun updated => updated.lookup query) =
      .ok (record.lookup query) := by
  induction edits generalizing record with
  | nil => simp [patch, Except.map]
  | cons edit rest ih =>
    have thisDeclared := declared edit (by simp)
    have thisAccepted := accepted edit (by simp)
    have thisUntouched := untouched edit (by simp)
    have restDeclared : ∀ item ∈ rest,
        description.keys.any (fun candidate => decide (candidate = item.1)) = true := by
      intro item member
      exact declared item (by simp [member])
    have restAccepted : ∀ item ∈ rest, (description.field item.1).accepts item.2 = true := by
      intro item member
      exact accepted item (by simp [member])
    have restUntouched : ∀ item ∈ rest, query ≠ item.1 := by
      intro item member
      exact untouched item (by simp [member])
    have step := description.set_lookup_other record edit.1 query edit.2
      thisUntouched thisDeclared thisAccepted
    cases hset : description.set record edit.1 edit.2 with
    | error err => simp [hset, Except.map] at step
    | ok next =>
      have sameLookup : next.lookup query = record.lookup query := by
        simpa [hset, Except.map] using step
      simp only [patch, hset]
      change (description.patch next rest).map (fun updated => updated.lookup query) =
        .ok (record.lookup query)
      rw [ih next restDeclared restAccepted restUntouched, sameLookup]

end LeanPoo.Prototype
