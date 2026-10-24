import LeanPoo.Functional.ObjectContractValidation
import LeanPoo.Functional.FunctionValidation

/-! Finite containers reuse ordered validation and the existing object pipeline.
Tuple vectors are interpreted as rows of tagged values; function values need no
function equality. Named-field schemas remain ObjectContract descriptors. -/
namespace LeanPoo.Functional.ContainerValidation

/-- List elements retain declaration order and the exact first child error. -/
def list (check : Input → Except Error Output) (values : List Input) : Except Error (List Output) :=
  Validation.traverse check values

/-- Every normalized position comes from that position's successful validator. -/
theorem list_positions (check : Input → Except Error Output) (values : List Input) (checked : List Output)
    (accepted : list check values = .ok checked) :
    checked.length = values.length ∧
      ∀ pair ∈ values.zip checked, check pair.1 = .ok pair.2 := by
  induction values generalizing checked with
  | nil => simp [list, Validation.traverse] at accepted; subst checked; simp
  | cons value rest ih =>
    cases hv : check value with
    | error error => simp [list, Validation.traverse, hv, Except.bind] at accepted
    | ok normalized =>
      cases ht : Validation.traverse check rest with
      | error error => simp [list, Validation.traverse, hv, ht, Except.bind, Except.map] at accepted
      | ok tail =>
        have same : normalized :: tail = checked := by
          simpa [list, Validation.traverse, hv, ht, Except.bind, Except.map] using accepted
        subst checked
        obtain ⟨length, positions⟩ := ih tail ht
        constructor
        · simp [length]
        · intro pair member
          simp only [List.zip_cons_cons, List.mem_cons] at member
          rcases member with rfl | member
          · exact hv
          · exact positions pair member

/-- Successful normalization preserves finite container length. -/
theorem list_length (check : Input → Except Error Output) (values : List Input) (checked : List Output)
    (accepted : list check values = .ok checked) : checked.length = values.length :=
  (list_positions check values checked accepted).1

/-- Validators that return each original value preserve the list mathematically.
Scheme's eq? reuse is additionally exercised by concrete host tests. -/
theorem list_unchanged (check : Value → Except Error Value) (values : List Value)
    (unchanged : ∀ value ∈ values, check value = .ok value) : list check values = .ok values := by
  simpa [list] using Validation.traverse_success check id values unchanged

/-- Heterogeneous tuple Types are row-specific validators over a shared tagged
carrier. Arity is checked before zip, so truncation can never admit a tuple. -/
def tuple (arityError : Error) (checks : List (Value → Except Error Value)) (values : List Value) :
    Except Error (List Value) :=
  if checks.length = values.length then
    Validation.traverse (fun pair => pair.1 pair.2) (checks.zip values)
  else .error arityError

/-- Wrong tuple arity rejects before any child validator is applied. -/
theorem tuple_arity_error (error : Error) (checks : List (Value → Except Error Value)) (values : List Value)
    (wrong : checks.length ≠ values.length) : tuple error checks values = .error error := by
  simp [tuple, wrong]

/-- Successful tuple validation proves both exact input arity and ordered child
validation. The theorem retains the supplied normalizing result, not raw values. -/
theorem tuple_success (error : Error) (checks : List (Value → Except Error Value)) (values checked : List Value) :
    tuple error checks values = .ok checked ↔ checks.length = values.length ∧
      Validation.traverse (fun pair => pair.1 pair.2) (checks.zip values) = .ok checked := by
  by_cases same : checks.length = values.length <;> simp [tuple, same]

/-- Every heterogeneous tuple position passed its corresponding Type validator;
exact arity prevents any unchecked source suffix from disappearing through zip. -/
theorem tuple_positions (error : Error) (checks : List (Value → Except Error Value)) (values checked : List Value)
    (good : tuple error checks values = .ok checked) :
    checked.length = values.length ∧
      ∀ pair ∈ (checks.zip values).zip checked, pair.1.1 pair.1.2 = .ok pair.2 := by
  obtain ⟨same, normalized⟩ := (tuple_success error checks values checked).mp good
  have positions := list_positions (fun (pair : (Value → Except Error Value) × Value) => pair.1 pair.2) (checks.zip values) checked normalized
  constructor
  · simpa [List.length_zip, same] using positions.1
  · exact positions.2

/-- Distinguish outer structure, child normalization and final obligations. This
is also the schema/container nesting discipline used by ObjectContract validation. -/
def validate (shape : List Value → Except Error Unit) (children : List Value → Except Error (List Value))
    (final : List Value → Except Error Unit) (values : List Value) : Except Error (List Value) :=
  ObjectContract.validateObject shape children final values

/-- Complete acceptance gives final obligations on exactly the returned container. -/
theorem accepted (shape : List Value → Except Error Unit) (children : List Value → Except Error (List Value))
    (final : List Value → Except Error Unit) (values checked : List Value) :
    validate shape children final values = .ok checked ↔ shape values = .ok () ∧
      children values = .ok checked ∧ final checked = .ok () :=
  ObjectContract.validateObject_success shape children final values checked

/-- With complete structural success, a first child failure suppresses final
obligations and returns its original cause without a successful container prefix. -/
theorem child_error (shape : List Value → Except Error Unit) (children : List Value → Except Error (List Value))
    (final : List Value → Except Error Unit) (values : List Value) (error : Error)
    (structural : shape values = .ok ()) (failed : children values = .error error) :
    validate shape children final values = .error error := by
  simp [validate, ObjectContract.validateObject, structural, failed, Except.bind]

/-- Schema refinement and nested containers compose through the already proved
object pipeline. Parent and additional obligations both hold on the checked schema. -/
theorem refined [DecidableEq Key] (contract : ObjectContract.Contract (List Value) Key Field Detail)
    (additional : List Value → List Key → List (ObjectContract.Issue Key Detail)) (path : List Key)
    (shape : List Value → Except (List (ObjectContract.Issue Key Detail)) Unit)
    (children : List Value → Except (List (ObjectContract.Issue Key Detail)) (List Value))
    (values checked : List Value)
    (good : validate shape children
      (ObjectContract.reportGate (fun candidate => ObjectContract.diagnose (ObjectContract.refine contract additional) candidate path))
      values = .ok checked) :
    ObjectContract.diagnose contract checked path = [] ∧ additional checked path = [] :=
  ObjectContract.validateObject_refine contract additional path shape children values checked good
end LeanPoo.Functional.ContainerValidation
