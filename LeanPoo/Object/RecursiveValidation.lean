import LeanPoo.Object.RecursiveInstance
import LeanPoo.Prototype.DynamicSchema

/-! Runtime schema admission of actual lazy C3 object slots. Each materialized
field retains its evaluation proof for the exact immutable plan. Descriptor
admission then checks the same field values in the current dynamic registry. -/
namespace LeanPoo.Object.Recursive

open Prototype
open Prototype.Recursive
open Prototype.MutableRecord

inductive ReadError where
  | diagnostic (error : Cached.Diagnostic String)
  | source (key message : String)
  | schema (error : Dynamic.SchemaError)
  deriving Repr

structure FieldReceipt (plan : Plan) where
  key : String
  value : Dynamic.Value
  evaluation : Evaluates (generator plan.storage) (generator plan.storage key) (.value value)

structure Materialized (plan : Plan) where
  fields : List (FieldReceipt plan)

def Materialized.value (snapshot : Materialized plan) : Dynamic.Value :=
  .object (snapshot.fields.map fun field => (field.key, field.value))

def Instance.materialize (instanceValue : Instance plan) (budget : Nat) (keys : List String) :
    IO (Except ReadError (Materialized plan)) := do
  let mut fields := []
  for key in keys do
    match ← instanceValue.read budget key with
    | .error diagnostic => return .error (.diagnostic diagnostic)
    | .ok receipt =>
      match receipt with
      | ⟨.error message, _⟩ => return .error (.source key message)
      | ⟨.value value, proof⟩ => fields := ⟨key, value, proof⟩ :: fields
  return .ok ⟨fields.reverse⟩

structure Validated (plan : Plan) (registry : Dynamic.Registry) (schema : Dynamic.RecordSchema) where
  snapshot : Materialized plan
  descriptor : Dynamic.Descriptor
  describes : schema.descriptor registry = .ok descriptor
  accepted : Dynamic.Accepted registry descriptor.contract snapshot.value

/-- Only catalog fields are forced. A sealed schema rejects extra stored
slots without evaluating them; an open schema can leave unrelated cycles cold. -/
def Instance.validate (instanceValue : Instance plan) (registry : Dynamic.Registry)
    (schema : Dynamic.RecordSchema) (budget fuel : Nat) :
    IO (Except ReadError (Validated plan registry schema)) := do
  if schema.sealed then
    for entry in plan.storage.toList do
      unless schema.slots.any (fun slot => slot.name == entry.1) do
        return .error (.schema (.unknownSlot entry.1))
  match described : schema.descriptor registry with
  | .error error => return .error (.schema error)
  | .ok descriptor =>
    match ← instanceValue.materialize budget (schema.slots.map Dynamic.SlotDescription.name) with
    | .error error => return .error error
    | .ok snapshot =>
      match checked : descriptor.validate registry fuel snapshot.value with
      | .error error => return .error (.schema (.wire error))
      | .ok admitted =>
        have same := descriptor.validate_value registry fuel snapshot.value admitted checked
        return .ok ⟨snapshot, descriptor, described, same ▸ admitted.valid⟩

/-- Every reflected field can be observed at a finite recursive depth. -/
theorem FieldReceipt.observed (field : FieldReceipt plan) :
    ∃ depth, plan.read depth field.key = .value field.value :=
  solve_complete field.evaluation

end LeanPoo.Object.Recursive
