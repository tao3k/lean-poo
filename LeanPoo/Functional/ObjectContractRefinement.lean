import LeanPoo.Functional.ObjectContract

/-! Explicit strengthening of effective structural contracts. Ordinary descriptor
inheritance remains override; these laws concern the supplied pure interpretation. -/
namespace LeanPoo.Functional.ObjectContract
open ObjectDiagnostics

/-- Keep shape, constraints and existing obligations; add one gated phase. -/
def refine (contract : Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (Issue Key Detail)) : Contract Carrier Key Value Detail :=
  {contract with obligations := (fun value path =>
    andThen (fun value => contract.obligations value path)
      (fun value => additional value path) value)}

/-- Successful refinement requires both the full original contract and the new
phase. This is explicit strengthening, without inference about inheritance. -/
theorem refine_accepts_iff [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (Issue Key Detail)) (value : Carrier) (path : List Key) :
    diagnose (refine contract additional) value path = [] ↔
      diagnose contract value path = [] ∧ additional value path = [] := by
  simp [diagnose_nil_iff, refine, extras, required, andThen_nil_iff, and_assoc]

/-- The original report is retained exactly; only its success enables the new
phase on the same candidate and caller path. -/
theorem diagnose_refine [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (Issue Key Detail)) (value : Carrier) (path : List Key) :
    diagnose (refine contract additional) value path =
      andThen (fun value => diagnose contract value path) (fun value => additional value path) value := by
  let shape := fun value => extras contract value path ++ required contract value path
  let checks := fun value => all (contract.constraints.map (fun check value => check value path)) value
  let parent := fun value => contract.obligations value path
  let extra := fun value => additional value path
  change (if !contract.view.isObject value then [.expectedObject path]
    else if !contract.view.prototype value then [.prototypeMismatch path]
    else andThen shape (andThen checks (andThen parent extra)) value) =
    andThen (fun value => if !contract.view.isObject value then [.expectedObject path]
      else if !contract.view.prototype value then [.prototypeMismatch path]
      else andThen shape (andThen checks parent) value) extra value
  cases object : contract.view.isObject value <;> cases prototype : contract.view.prototype value <;>
    cases structural : shape value <;> cases constraints : checks value <;> cases obligations : parent value <;>
    simp [andThen, object, prototype, structural, constraints, obligations]


/-- Refinement cannot admit a value rejected by the original descriptor. -/
theorem refine_preserves_rejection [DecidableEq Key] (contract : Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (Issue Key Detail)) (value : Carrier) (path : List Key)
    (rejected : diagnose contract value path ≠ []) :
    diagnose (refine contract additional) value path ≠ [] := by
  intro accepted
  exact rejected ((refine_accepts_iff contract additional value path).mp accepted).1

/-- Invariant shape metadata is unchanged, including the inventory policy. -/
theorem refine_fields (contract : Contract Carrier Key Value Detail) (additional) :
    (refine contract additional).fields = contract.fields := rfl

/-- Regrouping added phases retains the exact callback, including refusal order. -/
theorem refine_assoc (contract : Contract Carrier Key Value Detail)
    (second third : Carrier → List Key → List (Issue Key Detail)) :
    refine (refine contract second) third =
      refine contract (fun value path =>
        andThen (fun value => second value path) (fun value => third value path) value) := by
  have same : (refine (refine contract second) third).obligations =
      (refine contract (fun value path =>
        andThen (fun value => second value path) (fun value => third value path) value)).obligations := by
    funext value path
    exact congrFun (andThen_assoc (fun value => contract.obligations value path)
      (fun value => second value path) (fun value => third value path)) value
  exact congrArg (fun obligations => {contract with obligations := obligations}) same
end LeanPoo.Functional.ObjectContract
