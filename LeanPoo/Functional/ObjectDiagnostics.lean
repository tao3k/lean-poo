import LeanPoo.Functional.Validation

/-! Ordered refusal accumulation and gated diagnostic phases. Reports are pure;
callback exceptions and termination are explicitly outside these list laws. -/
namespace LeanPoo.Functional.ObjectDiagnostics
universe u v
/-- A diagnostic callback observes the same candidate throughout composition. -/
abbrev Report (Value : Type u) (Issue : Type v) := Value → List Issue
/-- Accumulate every ordinary refusal in declaration order, without deduplication. -/
def all (checks : List (Report Value Issue)) (value : Value) : List Issue :=
  checks.flatMap (fun check => check value)
/-- Run the next phase only when the preceding phase reports no refusal. -/
def andThen (first next : Report Value Issue) : Report Value Issue := fun value =>
  match first value with
  | [] => next value
  | failures => failures
/-- Accumulation preserves the exact report order at a composition boundary. -/
theorem all_append (left right : List (Report Value Issue)) (value : Value) :
    all (left ++ right) value = all left value ++ all right value := by
  simp [all]
/-- Empty accumulated diagnostics characterize simultaneous success of ALL checks. -/
theorem all_nil_iff (checks : List (Report Value Issue)) (value : Value) :
    all checks value = [] ↔ ∀ check ∈ checks, check value = [] := by
  exact List.flatMap_eq_nil_iff
/-- Refusing phases preserve their exact list; the next report contributes nothing. -/
theorem andThen_refused (first next : Report Value Issue) (value : Value)
    (refused : first value ≠ []) : andThen first next value = first value := by
  cases found : first value with
  | nil => exact False.elim (refused found)
  | cons _ _ => simp [andThen,found]
/-- A successful prefix passes the original candidate to the next phase. -/
theorem andThen_accepted (first next : Report Value Issue) (value : Value)
    (accepted : first value = []) : andThen first next value = next value := by
  simp [andThen,accepted]
/-- Gated success requires both phases to admit the same value. -/
theorem andThen_nil_iff (first next : Report Value Issue) (value : Value) :
    andThen first next value = [] ↔ first value = [] ∧ next value = [] := by
  cases found : first value <;> simp [andThen,found]
/-- Phases can be regrouped without changing refusal lists or successful input. -/
theorem andThen_assoc (first second third : Report Value Issue) :
    andThen (andThen first second) third = andThen first (andThen second third) := by
  funext value
  cases found : first value <;> simp [andThen,found]
end LeanPoo.Functional.ObjectDiagnostics
