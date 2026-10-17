import LeanPoo.Functional.ObjectDiagnostics
import LeanPoo.Functional.DeclarativeMetadata

/-! Finite structural value contracts over an explicitly supplied object view.
This models recognizers/diagnostics, not a Scheme runtime or subtype inference. -/
namespace LeanPoo.Functional.ObjectContract
open ObjectDiagnostics
/-- Field-specific diagnostics retain an explicit path; raw user values are absent. -/
inductive Issue (Key Detail : Type) where
  | expectedObject (path : List Key)
  | prototypeMismatch (path : List Key)
  | unknownField (path : List Key)
  | missingField (path : List Key)
  | rejected (path : List Key) (detail : Detail)
  deriving Repr, DecidableEq
/-- A finite field declaration reuses an arbitrary, explicitly supplied checker. -/
structure Field (Key Value Detail : Type) where
  name : Key
  check : Value → List Key → List (Issue Key Detail)
/-- Object observation is an adapter premise. Names enumerate actual public slots;
lookup distinguishes absence from a stored false/null value. Prototype checking
is supplied by the existing object protocol, rather than inferred from shape. -/
structure View (Carrier Key Value : Type) where
  isObject : Carrier → Bool
  prototype : Carrier → Bool
  names : Carrier → List Key
  lookup : Carrier → Key → Option Value
/-- Strict inventory rejects extra names; delegation leaves inventory policy to
explicit whole-value constraints. At least one constraint is required in Scheme. -/
structure Contract (Carrier Key Value Detail : Type) where
  view : View Carrier Key Value
  fields : List (Field Key Value Detail)
  strict : Bool
  constraints : List (Carrier → List Key → List (Issue Key Detail))
  obligations : Carrier → List Key → List (Issue Key Detail)
  validInventory : strict = true ∨ constraints ≠ []
/-- Inspect inventory names without fetching unknown field values. -/
def extras [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) : List (Issue Key Detail) :=
  if contract.strict then (contract.view.names value).filterMap fun name =>
    if name ∈ contract.fields.map Field.name then none else some (.unknownField (path ++ [name]))
  else []
/-- Check every required field, retaining missing versus present-but-rejected. -/
def required (contract : Contract Carrier Key Value Detail) (value : Carrier)
    (path : List Key) : List (Issue Key Detail) := contract.fields.flatMap fun field =>
  match contract.view.lookup value field.name with
  | none => [.missingField (path ++ [field.name])]
  | some item => field.check item (path ++ [field.name])
/-- Object/prototype refusal precedes field demand. Whole-value constraints and
obligations are gated behind successful structural checks, as in ObjectContract. -/
def diagnose [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key := []) : List (Issue Key Detail) :=
  if !contract.view.isObject value then [.expectedObject path]
  else if !contract.view.prototype value then [.prototypeMismatch path]
  else andThen (fun value => extras contract value path ++ required contract value path)
    (andThen (fun value => all (contract.constraints.map (fun check value => check value path)) value)
      (fun value => contract.obligations value path)) value
/-- Successful recognition gives exact inventory, required-field, constraint and
obligation success. No assumption of arbitrary custom callback correctness is used. -/
theorem diagnose_nil_iff [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) :
    diagnose contract value path = [] ↔
      contract.view.isObject value = true ∧ contract.view.prototype value = true ∧
      extras contract value path = [] ∧ required contract value path = [] ∧
      (∀ check ∈ contract.constraints, check value path = []) ∧ contract.obligations value path = [] := by
  cases object : contract.view.isObject value <;> cases prototype : contract.view.prototype value <;>
    simp [diagnose,object,prototype,andThen_nil_iff,all_nil_iff, and_assoc]
/-- Rejecting a non-object does not observe field values or later callbacks. -/
theorem diagnose_nonobject [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) (no : contract.view.isObject value = false) :
    diagnose contract value path = [.expectedObject path] := by simp [diagnose,no]
/-- Prototype rejection preserves the exact early issue, independently of shape. -/
theorem diagnose_prototype [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) (yes : contract.view.isObject value = true)
    (no : contract.view.prototype value = false) :
    diagnose contract value path = [.prototypeMismatch path] := by simp [diagnose,yes,no]
/-- Strict inventory success means every observed name is explicitly declared. -/
theorem extras_nil_iff [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) (strict : contract.strict = true) :
    extras contract value path = [] ↔
      ∀ name ∈ contract.view.names value, name ∈ contract.fields.map Field.name := by
  simp [extras,strict,List.filterMap_eq_nil_iff]
/-- Every accepted required field actually exists and its own diagnostic succeeds. -/
theorem required_nil_iff (contract : Contract Carrier Key Value Detail) (value : Carrier) (path : List Key) :
    required contract value path = [] ↔ ∀ field ∈ contract.fields,
      ∃ item, contract.view.lookup value field.name = some item ∧ field.check item (path ++ [field.name]) = [] := by
  simp only [required,List.flatMap_eq_nil_iff]
  apply forall_congr'
  intro field
  apply imp_congr_right
  intro _
  cases contract.view.lookup value field.name <;> simp
/-- Changing observations outside declared fields cannot affect required checks.
Whole-value constraints may deliberately observe more; no such claim is made for them. -/
theorem required_lookup_congr (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) (lookup : Carrier → Key → Option Value)
    (same : ∀ field ∈ contract.fields, lookup value field.name = contract.view.lookup value field.name) :
    required {contract with view := {contract.view with lookup := lookup}} value path = required contract value path := by
  simp only [required,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro field member
  rw [same field member]
/-- A shape-preserving custom Type is sound only with this explicit callback law.
Lean does not manufacture that law from a Scheme procedure or a method name. -/
theorem required_sound (contract : Contract Carrier Key Value Detail) (value : Carrier) (path : List Key)
    (accepts : Field Key Value Detail → Value → Prop)
    (law : ∀ field ∈ contract.fields, ∀ item, field.check item (path ++ [field.name]) = [] → accepts field item)
    (good : required contract value path = []) :
    ∀ field ∈ contract.fields, ∃ item, contract.view.lookup value field.name = some item ∧ accepts field item := by
  intro field member
  obtain ⟨item,found,checked⟩ := (required_nil_iff contract value path).mp good field member
  exact ⟨item,found,law field member item checked⟩
/-- Semantic completeness/soundness requires explicit agreement between each
custom recognizer and its diagnostics, at the path actually supplied. -/
theorem required_semantics_iff (contract : Contract Carrier Key Value Detail) (value : Carrier) (path : List Key)
    (accepts : Field Key Value Detail → Value → Prop)
    (law : ∀ field ∈ contract.fields, ∀ item, field.check item (path ++ [field.name]) = [] ↔ accepts field item) :
    required contract value path = [] ↔
      ∀ field ∈ contract.fields, ∃ item, contract.view.lookup value field.name = some item ∧ accepts field item := by
  rw [required_nil_iff]
  constructor
  · intro good field member
    obtain ⟨item,found,checked⟩ := good field member
    exact ⟨item,found,(law field member item).mp checked⟩
  · intro good field member
    obtain ⟨item,found,accepted⟩ := good field member
    exact ⟨item,found,(law field member item).mpr accepted⟩
/-- Adapt structural recognition to the EXISTING checked invocation predicate.
This is recognition, not higher-order Function validation or a provenance receipt. -/
def predicate [DecidableEq Key] (label : String) (contract : Contract Carrier Key Value Detail)
    (path : List Key := []) : DeclarativeMetadata.Predicate Carrier where
  name := label
  holds value := (diagnose contract value path).isEmpty = true
  decide _value := inferInstance
/-- The invocation adapter admits exactly empty structural diagnostics. -/
theorem predicate_holds_iff [DecidableEq Key] (label : String) (contract : Contract Carrier Key Value Detail)
    (value : Carrier) (path : List Key) :
    (predicate label contract path).holds value ↔ diagnose contract value path = [] := by
  simp [predicate]
/-- Reader admission preserves the original error or passes the validated value
(including possible normalization) to the consumer, without returning a prefix. -/
def checkedAction (validate : Value → Except Error Checked)
    (consume : Checked → Except Error Result) : Factory Value (fun _ => Except Error Result) :=
  fun value => (validate value).bind consume
/-- No consumer result is reachable after value admission fails. -/
theorem checkedAction_refused (validate : Value → Except Error Checked)
    (consume : Checked → Except Error Result) (value : Value) (failure : Error)
    (refused : validate value = .error failure) : checkedAction validate consume value = .error failure := by
  simp [checkedAction,refused,Except.bind]
/-- Admission passes the exact normalized value, rather than the unvalidated input. -/
theorem checkedAction_accepted (validate : Value → Except Error Checked)
    (consume : Checked → Except Error Result) (value : Value) (checked : Checked)
    (accepted : validate value = .ok checked) : checkedAction validate consume value = consume checked := by
  simp [checkedAction,accepted,Except.bind]
end LeanPoo.Functional.ObjectContract
