import LeanPoo.Functional.ResultView

/-! Collapse intermediate named views while preserving first-occurrence semantics.
These laws do not require unique source names or identical duplicate values. -/
namespace LeanPoo.Functional.Requirements
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [DecidableEq Key] {source : List Key}

/-- Named access through a view returns the original first source occurrence. -/
theorem resultAt_project {context : Context} (data : Results Value context source)
    (middle : List Key) (included : ∀ k ∈ middle, k ∈ source)
    (key : Key) (member : key ∈ middle) :
    resultAt (projectResults data middle included) key member = resultAt data key (included key member) := by
  induction middle with
  | nil => simp at member
  | cons head rest ih =>
    by_cases same : head = key
    · subst key; simp [projectResults, resultAt]
    · simp only [projectResults, resultAt, dite_eq_right same]
      exact ih _ _

/-- Project directly to final keys instead of constructing the intermediate tuple.
Source/target order, empty lists and duplicate requests retain their semantics. -/
theorem projectResults_trans {context : Context} (data : Results Value context source)
    (middle keys : List Key) (first : ∀ k ∈ middle, k ∈ source)
    (second : ∀ k ∈ keys, k ∈ middle) :
    projectResults (projectResults data middle first) keys second =
      projectResults data keys (fun k h => first k (second k h)) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [projectResults, resultAt_project]
    exact congrArg (fun tail => (resultAt data key _, tail)) (ih _)

/-- A projected factory family retains the original named function itself. -/
theorem factoryAt_project (factories : Factories Context Value source)
    (middle : List Key) (included : ∀ k ∈ middle, k ∈ source)
    (key : Key) (member : key ∈ middle) :
    factoryAt (project factories middle included) key member = factoryAt factories key (included key member) := by
  induction middle with
  | nil => simp at member
  | cons head rest ih =>
    by_cases same : head = key
    · subst key; simp [project, factoryAt]
    · simp only [project, factoryAt, dite_eq_right same]
      exact ih _ _

/-- Prepared views can also be flattened before any context is evaluated. -/
theorem project_trans (factories : Factories Context Value source)
    (middle keys : List Key) (first : ∀ k ∈ middle, k ∈ source)
    (second : ∀ k ∈ keys, k ∈ middle) :
    project (project factories middle first) keys second =
      project factories keys (fun k h => first k (second k h)) := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    simp only [project, factoryAt_project]
    exact congrArg (fun tail => (factoryAt factories key _, tail)) (ih _)

end LeanPoo.Functional.Requirements
