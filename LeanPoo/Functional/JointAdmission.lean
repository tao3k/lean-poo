import LeanPoo.Functional.JointPublication

/-! Endpoint admission and whole-family admission remain distinct checks.
This composes their results with the existing immutable request protocol. -/
namespace LeanPoo.Functional.JointPublication
universe u v
variable {Id Endpoint Policy : Type} {Head : Endpoint → Type u} {Metadata : Policy → Type v}
/-- Check every declared endpoint against the same candidate's proposed policies,
then require the whole-family relation. Enumeration completeness is a premise. -/
def admitted (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool)
    (candidate : Bundle Id Endpoint Policy Head Metadata) : Bool :=
  endpoints.all (endpointCheck candidate) && joint candidate
/-- Prepare immutable checks without changing the expected snapshot identity. -/
def prepare (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool) (expected : Id)
    (candidate : Bundle Id Endpoint Policy Head Metadata) : Request Id Endpoint Policy Head Metadata :=
  ⟨expected,candidate,admitted endpoints endpointCheck joint candidate⟩
/-- Successful admission requires both complete endpoint checks and joint approval. -/
theorem admitted_iff (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool)
    (candidate : Bundle Id Endpoint Policy Head Metadata) :
    admitted endpoints endpointCheck joint candidate = true ↔
      endpoints.all (endpointCheck candidate) = true ∧ joint candidate = true := by
  simp [admitted]
/-- Every named member of the declared family passed its own candidate check;
this does not infer checks for endpoints omitted from the declaration. -/
theorem admitted_endpoint (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool)
    (candidate : Bundle Id Endpoint Policy Head Metadata) (checked : admitted endpoints endpointCheck joint candidate = true)
    (key : Endpoint) (member : key ∈ endpoints) : endpointCheck candidate key = true := by
  exact List.all_eq_true.mp ((admitted_iff endpoints endpointCheck joint candidate).mp checked).1 key member
variable [DecidableEq Id]
/-- Even unanimous endpoint approval cannot publish a jointly refused candidate. -/
theorem joint_refused (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool) (expected : Id)
    (current candidate : Bundle Id Endpoint Policy Head Metadata) (denied : joint candidate = false) :
    install expected current candidate (admitted endpoints endpointCheck joint candidate) = current := by
  simp [admitted,denied,refused]
/-- A refused request leaves competing requests bound to the same current head;
arbitrary later interleavings therefore run from exactly the previous bundle. -/
theorem run_denied_prefix (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool) (expected : Id)
    (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (rest : List (Request Id Endpoint Policy Head Metadata)) (denied : joint candidate = false) :
    run current (prepare endpoints endpointCheck joint expected candidate :: rest) = run current rest := by
  simp only [run,List.foldl_cons,prepare]
  rw [joint_refused endpoints endpointCheck joint expected current candidate denied]
/-- Jointly refused work is inert at ANY position in a serialized interleaving,
including after a successful rival changed support, SCCs or shared approvals. -/
theorem run_denied_between (endpoints : List Endpoint)
    (endpointCheck : Bundle Id Endpoint Policy Head Metadata → Endpoint → Bool)
    (joint : Bundle Id Endpoint Policy Head Metadata → Bool) (expected : Id)
    (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (before after : List (Request Id Endpoint Policy Head Metadata)) (denied : joint candidate = false) :
    run current (before ++ prepare endpoints endpointCheck joint expected candidate :: after) =
      run current (before ++ after) := by
  simp only [run,List.foldl_append,List.foldl_cons,prepare]
  rw [joint_refused endpoints endpointCheck joint expected _ candidate denied]
end LeanPoo.Functional.JointPublication
