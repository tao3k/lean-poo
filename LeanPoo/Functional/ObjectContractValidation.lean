import LeanPoo.Functional.Validation
import LeanPoo.Functional.ObjectContractRefinement
import LeanPoo.Functional.EvidenceBinding

/-! Persistent finite field validation followed by whole-object obligations.
The commit callback supplies representation/lens laws. Scheme identity, arbitrary
recursive termination, effects and wrapper deduplication are outside these laws. -/
namespace LeanPoo.Functional.ObjectContract

/-- Validate the declared fields against the original source in order. Commit one
complete batch only after success; a failure cannot expose a partial object. -/
def validateFields (read : Carrier → Key → Value)
    (commit : Carrier → List (Key × Value) → Carrier)
    (checks : List (Key × (Value → Except Error Value))) (source : Carrier) : Except Error Carrier :=
  (Validation.traverse (fun entry => (entry.2 (read source entry.1)).map (entry.1, ·)) checks).map
    (commit source)

/-- Successful field normalization performs exactly the supplied batch commit. -/
theorem validateFields_commit (read : Carrier → Key → Value)
    (commit : Carrier → List (Key × Value) → Carrier)
    (checks : List (Key × (Value → Except Error Value))) (source : Carrier) (updates : List (Key × Value))
    (checked : Validation.traverse (fun entry => (entry.2 (read source entry.1)).map (entry.1, ·)) checks = .ok updates) :
    validateFields read commit checks source = .ok (commit source updates) := by
  unfold validateFields
  rw [checked]
  rfl

/-- Field failure preserves the exact first error without calling commit. -/
theorem validateFields_error (read : Carrier → Key → Value)
    (commit : Carrier → List (Key × Value) → Carrier)
    (checks : List (Key × (Value → Except Error Value))) (source : Carrier) (error : Error)
    (failed : Validation.traverse (fun entry => (entry.2 (read source entry.1)).map (entry.1, ·)) checks = .error error) :
    validateFields read commit checks source = .error error := by
  unfold validateFields
  rw [failed]
  rfl

/-- The representation callback must provide its own lookup law. With that law,
every installed normalized field is observable in the committed object. -/
theorem validateFields_lookup (read : Carrier → Key → Value)
    (commit : Carrier → List (Key × Value) → Carrier)
    (checks : List (Key × (Value → Except Error Value))) (source : Carrier)
    (updates : List (Key × Value)) (key : Key) (value : Value)
    (checked : Validation.traverse (fun entry => (entry.2 (read source entry.1)).map (entry.1, ·)) checks = .ok updates)
    (installed : (key, value) ∈ updates)
    (law : ∀ pair ∈ updates, read (commit source updates) pair.1 = pair.2) :
    (validateFields read commit checks source).map (fun result => read result key) = .ok value := by
  rw [validateFields_commit read commit checks source updates checked]
  simp only [Except.map]
  rw [law (key, value) installed]

/-- A structural gate precedes recursive field normalization. The final gate
observes the normalized root; it never receives an intermediate field update. -/
def validateObject (shape : Carrier → Except Error Unit) (fields : Carrier → Except Error Carrier)
    (final : Carrier → Except Error Unit) (source : Carrier) : Except Error Carrier :=
  (shape source).bind fun _ => (fields source).bind fun checked => (final checked).map fun _ => checked

/-- Structural refusal precedes all recursive validators. -/
theorem validateObject_shape_error (shape : Carrier → Except Error Unit) (fields : Carrier → Except Error Carrier)
    (final : Carrier → Except Error Unit) (source : Carrier) (error : Error)
    (failed : shape source = .error error) : validateObject shape fields final source = .error error := by
  simp [validateObject, failed, Except.bind]

/-- Acceptance is equivalent to successful shape, normalization and final checks
on the exact returned object. No premise asserts that normalization preserves raw identity. -/
theorem validateObject_success (shape : Carrier → Except Error Unit) (fields : Carrier → Except Error Carrier)
    (final : Carrier → Except Error Unit) (source checked : Carrier) :
    validateObject shape fields final source = .ok checked ↔
      shape source = .ok () ∧ fields source = .ok checked ∧ final checked = .ok () := by
  cases hs : shape source <;> cases hf : fields source <;>
    simp [validateObject, hs, hf, Except.bind, Except.map]
  case ok.ok first normalized =>
    cases he : final normalized <;> simp [eq_comm]
    all_goals intro same; subst normalized; simp_all


/-- Turn an exact diagnostic report into a gate; no issue is discarded. -/
def reportGate (report : Carrier → List Problem) (value : Carrier) : Except (List Problem) Unit :=
  match report value with | [] => .ok () | errors => .error errors

/-- Final refinement requires both parent and added obligations on the checked
object. This law concerns final validation, not recognition of an unwrapped procedure. -/
theorem validateObject_refine [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (Issue Key Detail)) (path : List Key)
    (shape : Carrier → Except (List (Issue Key Detail)) Unit)
    (fields : Carrier → Except (List (Issue Key Detail)) Carrier) (source checked : Carrier)
    (accepted : validateObject shape fields (reportGate (fun value => diagnose (refine contract additional) value path)) source = .ok checked) :
    diagnose contract checked path = [] ∧ additional checked path = [] := by
  have final := (validateObject_success _ _ _ source checked).mp accepted |>.2.2
  have empty : diagnose (refine contract additional) checked path = [] := by
    cases h : diagnose (refine contract additional) checked path <;> simp_all [reportGate]
  exact (refine_accepts_iff contract additional checked path).mp empty
/-- Compose normalization with the existing exact-reference publication rule.
The application supplies a pure reference projection; its correspondence to
Scheme eq? and immutability are premises, not consequences of this model. -/
theorem validated_binding [DecidableEq Reference] [DecidableEq Descriptor] [DecidableEq Context]
    (shape : Carrier → Except Error Unit) (fields : Carrier → Except Error Carrier)
    (final : Carrier → Except Error Unit) (source checked : Carrier)
    (accepted : validateObject shape fields final source = .ok checked)
    (reference : Carrier → Reference)
    (template : DeclarativeMetadata.Contract Atom Reference Result)
    (descriptor : Descriptor) (context : Context) (view : Result → Reference × Descriptor × Context)
    (execute : Reference → Except Cause (Result × State))
    (receipt : DeclarativeMetadata.Invocation
      (template.bindEvidence (reference checked) descriptor context view) execute (reference checked)) :
    final checked = .ok () ∧
      template.rule.Holds (fun key => template.meaning key (reference checked) receipt.result) ∧
      view receipt.result = (reference checked, descriptor, context) := by
  have bound := template.bindEvidence_accepted (reference checked) descriptor context view
    execute (reference checked) receipt
  exact ⟨((validateObject_success _ _ _ source checked).mp accepted).2.2, bound.1, bound.2.2⟩
end LeanPoo.Functional.ObjectContract
