import LeanPoo.Functional.StatefulValidation
import LeanPoo.Prototype.DynamicSchema
import LeanPoo.Prototype.DynamicCodecSemantics

/-! Current-catalog record migration and checked, staged field updates.
Defaults, shape checks and writable flags come from the existing slot catalog.
An ordinary batch retains completed groups; atomic publication rolls back the
whole batch on refusal. Both use the same pure transition. -/
namespace LeanPoo.Functional
open Prototype.Dynamic

/-- A record bound to the actual schema, current catalog and admission budget.
Changing any of those indices requires another admission. -/
structure CheckedRecord (schema : RecordSchema) (registry : Registry) (fuel : Nat) where
  value : Value
  validated : schema.validate registry fuel value = .ok value

theorem CheckedRecord.membership (record : CheckedRecord schema registry fuel) :
    ∃ descriptor, schema.descriptor registry = .ok descriptor ∧
      Accepted registry descriptor.contract record.value :=
  schema.validate_membership registry fuel record.value record.value record.validated

/-- A field consumer obtains membership from the exact resolved descriptor. -/
theorem CheckedRecord.slotAccepted (record : CheckedRecord schema registry fuel)
    (descriptor : Descriptor) (resolved : schema.descriptor registry = .ok descriptor)
    (slots : List (String × Contract)) (contract : descriptor.contract = .objectOf slots)
    (name : String) (fieldType : Contract) (value : Value)
    (member : (name, fieldType) ∈ slots) (found : record.value.slot? name = some value) :
    Accepted registry fieldType value := by
  obtain ⟨actual, binding, admitted⟩ := record.membership
  have same := Except.ok.inj (binding.symm.trans resolved)
  subst actual
  rw [contract] at admitted
  generalize record.value = object at admitted found
  cases admitted with
  | object present members => exact members (name, fieldType) member value found

/-- Structural transport reconstructs the admitted value. Reusing the witness
under a different catalog still requires the new catalog's admission. -/
theorem CheckedRecord.decode_encode (record : CheckedRecord schema registry fuel)
    (wireFuel : Nat) (bound : record.value.wireDepth ≤ wireFuel) :
    Value.decodeJson wireFuel record.value.encodeJson = .ok record.value :=
  record.value.decodeJson_encodeJson wireFuel bound

namespace RecordEvolution

/-- Obtain the witness from the same gate, without a second recognition. -/
def admit (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) : Except SchemaError (CheckedRecord schema registry fuel) :=
  match checked : schema.validate registry fuel value with
  | .error error => .error error
  | .ok output => .ok ⟨output, by
      have same := schema.validate_value registry fuel value output checked
      simpa only [same] using checked⟩

theorem admit_outcome (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) :
    (admit schema registry fuel value).map CheckedRecord.value = schema.validate registry fuel value := by
  unfold admit
  split <;> simp_all [Except.map]

def construct (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (supplied : List (String × Value)) : Except SchemaError (CheckedRecord schema registry fuel) :=
  match built : schema.construct registry fuel supplied with
  | .error error => .error error
  | .ok value => .ok ⟨value, schema.construct_validated registry fuel supplied value built⟩

theorem construct_outcome (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (supplied : List (String × Value)) :
    (construct schema registry fuel supplied).map CheckedRecord.value =
      schema.construct registry fuel supplied := by
  unfold construct
  split <;> simp_all [Except.map]

def patch (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (edits : List (String × Value)) :
    Except SchemaError (CheckedRecord schema registry fuel) :=
  match changed : schema.patch registry fuel value edits with
  | .error error => .error error
  | .ok output => .ok ⟨output, schema.patch_validated registry fuel value edits output changed⟩

theorem patch_outcome (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (edits : List (String × Value)) :
    (patch schema registry fuel value edits).map CheckedRecord.value =
      schema.patch registry fuel value edits := by
  unfold patch
  split <;> simp_all [Except.map]

structure FieldTransfer where
  source : String
  target : String
  deriving Repr, BEq

/-- Only declared fields cross a version boundary. Unknown source fields fail
in caller order; target duplicates/defaults/refinements remain catalog-owned. -/
def transferFields (fields : List FieldTransfer) (value : Value) :
    Except SchemaError (List (String × Value)) :=
  Validation.traverse (fun field =>
    match value.slot? field.source with
    | none => .error (.missingSlot field.source)
    | some entry => .ok (field.target, entry)) fields

theorem transferFields_cons (field : FieldTransfer) (rest : List FieldTransfer) (value : Value) :
    transferFields (field :: rest) value =
      ((match value.slot? field.source with
        | none => .error (.missingSlot field.source)
        | some entry => .ok (field.target, entry)) : Except SchemaError (String × Value)).bind fun supplied =>
          (transferFields rest value).map (supplied :: ·) := rfl

theorem transferFields_targets (fields : List FieldTransfer) (value : Value)
    (supplied : List (String × Value)) (success : transferFields fields value = .ok supplied) :
    supplied.map Prod.fst = fields.map FieldTransfer.target := by
  induction fields generalizing supplied with
  | nil => cases success; rfl
  | cons field rest ih =>
    rw [transferFields_cons] at success
    cases found : value.slot? field.source with
    | none => simp [found, Except.bind] at success
    | some entry =>
      cases tail : transferFields rest value with
      | error error => simp [found, tail, Except.bind, Except.map] at success
      | ok entries =>
        have same : (field.target, entry) :: entries = supplied := by
          simpa [found, tail, Except.bind, Except.map] using success
        subst supplied
        simp only [List.map_cons, ih entries tail]

structure RecordMigration where
  source : RecordSchema
  target : RecordSchema
  fields : List FieldTransfer

/-- Source admission precedes every field read. Target construction supplies
defaults and rechecks values and nested identities in the target catalog. -/
def RecordMigration.run (migration : RecordMigration) (sourceRegistry targetRegistry : Registry)
    (sourceFuel targetFuel : Nat) (value : Value) : Except SchemaError Value := do
  let checked ← migration.source.validate sourceRegistry sourceFuel value
  let supplied ← transferFields migration.fields checked
  migration.target.construct targetRegistry targetFuel supplied

theorem RecordMigration.run_validated (migration : RecordMigration)
    (sourceRegistry targetRegistry : Registry) (sourceFuel targetFuel : Nat) (value output : Value)
    (success : migration.run sourceRegistry targetRegistry sourceFuel targetFuel value = .ok output) :
    migration.target.validate targetRegistry targetFuel output = .ok output := by
  unfold run at success
  cases first : migration.source.validate sourceRegistry sourceFuel value with
  | error error => simp [first, bind, Except.bind] at success
  | ok checked =>
    cases projected : transferFields migration.fields checked with
    | error error => simp [first, projected, bind, Except.bind] at success
    | ok supplied =>
      exact migration.target.construct_validated targetRegistry targetFuel supplied output
        (by simpa only [first, projected, bind, Except.bind] using success)

/-- The source's exact refusal wins over projection and target errors. -/
theorem RecordMigration.run_source_error (migration : RecordMigration)
    (sourceRegistry targetRegistry : Registry) (sourceFuel targetFuel : Nat) (value : Value)
    (error : SchemaError)
    (failed : migration.source.validate sourceRegistry sourceFuel value = .error error) :
    migration.run sourceRegistry targetRegistry sourceFuel targetFuel value = .error error := by
  simp [run, failed, bind, Except.bind]

/-- The target was constructed from the declared projection of this exact
source. Source admission cannot silently normalize or substitute another value. -/
theorem RecordMigration.run_success_iff (migration : RecordMigration)
    (sourceRegistry targetRegistry : Registry) (sourceFuel targetFuel : Nat) (value output : Value) :
    migration.run sourceRegistry targetRegistry sourceFuel targetFuel value = .ok output ↔
      ∃ supplied, migration.source.validate sourceRegistry sourceFuel value = .ok value ∧
        transferFields migration.fields value = .ok supplied ∧
        migration.target.construct targetRegistry targetFuel supplied = .ok output := by
  constructor
  · intro success
    cases first : migration.source.validate sourceRegistry sourceFuel value with
    | error error => simp [run, first, bind, Except.bind] at success
    | ok checked =>
      have same := migration.source.validate_value sourceRegistry sourceFuel value checked first
      subst checked
      cases projected : transferFields migration.fields value with
      | error error => simp [run, first, projected, bind, Except.bind] at success
      | ok supplied =>
        exact ⟨supplied, rfl, rfl,
          by simpa only [run, first, projected, bind, Except.bind] using success⟩
  · rintro ⟨supplied, first, projected, constructed⟩
    simp [run, first, projected, constructed, bind, Except.bind]

def RecordMigration.checked (migration : RecordMigration) (sourceRegistry targetRegistry : Registry)
    (sourceFuel targetFuel : Nat) (value : Value) :
    Except SchemaError (CheckedRecord migration.target targetRegistry targetFuel) :=
  match result : migration.run sourceRegistry targetRegistry sourceFuel targetFuel value with
  | .error error => .error error
  | .ok output => .ok ⟨output,
      migration.run_validated sourceRegistry targetRegistry sourceFuel targetFuel value output result⟩

theorem RecordMigration.checked_outcome (migration : RecordMigration)
    (sourceRegistry targetRegistry : Registry) (sourceFuel targetFuel : Nat) (value : Value) :
    (migration.checked sourceRegistry targetRegistry sourceFuel targetFuel value).map CheckedRecord.value =
      migration.run sourceRegistry targetRegistry sourceFuel targetFuel value := by
  unfold checked
  split <;> simp_all [Except.map]

/-- Publish a whole converted collection only when every record migrates. -/
def RecordMigration.batch (migration : RecordMigration) (sourceRegistry targetRegistry : Registry)
    (sourceFuel targetFuel : Nat) (values : List Value) :=
  Validation.traverse (migration.checked sourceRegistry targetRegistry sourceFuel targetFuel) values

theorem RecordMigration.batch_error_iff (migration : RecordMigration)
    (sourceRegistry targetRegistry : Registry) (sourceFuel targetFuel : Nat)
    (values : List Value) (error : SchemaError) :
    migration.batch sourceRegistry targetRegistry sourceFuel targetFuel values = .error error ↔
      ∃ before item after outputs, values = before ++ item :: after ∧
        migration.batch sourceRegistry targetRegistry sourceFuel targetFuel before = .ok outputs ∧
        migration.checked sourceRegistry targetRegistry sourceFuel targetFuel item = .error error :=
  Validation.traverse_error_iff _ values error

/-- A group is the existing pure patch transaction. A refused group keeps its
input; a successful group publishes exactly its admitted record. -/
def update (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (edits : List (String × Value)) :
    Except SchemaError (CheckedRecord schema registry fuel) × Value :=
  match patch schema registry fuel value edits with
  | .error error => (.error error, value)
  | .ok checked => (.ok checked, checked.value)

theorem update_error (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (edits : List (String × Value)) (error : SchemaError)
    (failed : schema.patch registry fuel value edits = .error error) :
    update schema registry fuel value edits = (.error error, value) := by
  have refused : patch schema registry fuel value edits = .error error := by
    unfold patch
    split <;> simp_all
  simp [update, refused]

theorem update_invariant (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (edits : List (String × Value))
    (valid : schema.validate registry fuel value = .ok value) :
    schema.validate registry fuel (update schema registry fuel value edits).2 =
      .ok (update schema registry fuel value edits).2 := by
  unfold update
  cases patch schema registry fuel value edits with
  | error error => exact valid
  | ok record => exact record.validated

theorem update_failure_state (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value final : Value) (edits : List (String × Value)) (error : SchemaError)
    (failed : update schema registry fuel value edits = (.error error, final)) : final = value := by
  unfold update at failed
  cases result : patch schema registry fuel value edits with
  | error refused => simpa only [result, Prod.mk.injEq, Except.error.injEq] using
      (congrArg Prod.snd failed).symm
  | ok checked => simp [result] at failed

def updateBatch (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (groups : List (List (String × Value))) :=
  Validation.traverseState (update schema registry fuel) value groups

theorem updateBatch_append (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (left right : List (List (String × Value))) :
    updateBatch schema registry fuel value (left ++ right) =
      match updateBatch schema registry fuel value left with
      | (.error error, final) => (.error error, final)
      | (.ok before, next) =>
        let (after, final) := updateBatch schema registry fuel next right
        (after.map (before ++ ·), final) := by
  unfold updateBatch
  rw [Validation.traverseState_append]
  cases Validation.traverseState (update schema registry fuel) value left with
  | mk outcome next => cases outcome with
    | error error => rfl
    | ok before =>
      cases Validation.traverseState (update schema registry fuel) next right with
      | mk after final => rfl

/-- A later refusal retains the successful prefix and the entire group input;
no partial record from the refusing group or later group is published. -/
theorem updateBatch_error_iff (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value final : Value) (groups : List (List (String × Value))) (error : SchemaError) :
    updateBatch schema registry fuel value groups = (.error error, final) ↔
      ∃ before item after outputs next, groups = before ++ item :: after ∧
        updateBatch schema registry fuel value before = (.ok outputs, next) ∧
        update schema registry fuel next item = (.error error, final) :=
  Validation.traverseState_error_iff _ value groups error final

theorem updateBatch_invariant (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (groups : List (List (String × Value)))
    (valid : schema.validate registry fuel value = .ok value) :
    schema.validate registry fuel (updateBatch schema registry fuel value groups).2 =
      .ok (updateBatch schema registry fuel value groups).2 :=
  Validation.traverseState_invariant _ _ (fun state edits => update_invariant schema registry fuel state edits)
    value valid groups

/-- Explicit all-or-error publication over the same staged batch. This does
not undo external effects: values and catalog operations here are pure. -/
def updateAtomic (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (groups : List (List (String × Value))) :
    Except SchemaError (List (CheckedRecord schema registry fuel)) × Value :=
  match updateBatch schema registry fuel value groups with
  | (.error error, _) => (.error error, value)
  | (.ok outputs, final) => (.ok outputs, final)

theorem updateAtomic_error (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value final : Value) (groups : List (List (String × Value))) (error : SchemaError)
    (failed : updateBatch schema registry fuel value groups = (.error error, final)) :
    updateAtomic schema registry fuel value groups = (.error error, value) := by
  simp [updateAtomic, failed]

theorem updateAtomic_success (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value final : Value) (groups : List (List (String × Value)))
    (outputs : List (CheckedRecord schema registry fuel))
    (success : updateBatch schema registry fuel value groups = (.ok outputs, final)) :
    updateAtomic schema registry fuel value groups = (.ok outputs, final) := by
  simp [updateAtomic, success]

theorem updateAtomic_invariant (schema : RecordSchema) (registry : Registry) (fuel : Nat)
    (value : Value) (groups : List (List (String × Value)))
    (valid : schema.validate registry fuel value = .ok value) :
    schema.validate registry fuel (updateAtomic schema registry fuel value groups).2 =
      .ok (updateAtomic schema registry fuel value groups).2 := by
  have retained := updateBatch_invariant schema registry fuel value groups valid
  unfold updateAtomic
  cases result : updateBatch schema registry fuel value groups with
  | mk outcome final => cases outcome with
    | error error => exact valid
    | ok outputs => simpa only [result] using retained

end RecordEvolution
end LeanPoo.Functional
