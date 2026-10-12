import LeanPoo.Functional.DependencyAnalysis
import LeanPoo.Functional.Validation

/-! Finite ordered capability batches retain inspectable dependency syntax.
Data validation may report source errors without hiding provider access. -/
namespace LeanPoo.Functional.Computation
universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {Result : Context → Type w} {Input : Type x}

def sequence : List (Computation Context Key Value Result) →
    Computation Context Key Value (fun c => List (Result c))
  | [] => .pure (fun _ => [])
  | first :: rest => .both first (sequence rest) (fun _ value values => value :: values)

def traverse (items : List Input) (make : Input → Computation Context Key Value Result) :
    Computation Context Key Value (fun c => List (Result c)) := sequence (items.map make)

/-- Batch execution agrees with the common first-error validation semantics.
Every child is run at the same context, in caller order. -/
theorem sequence_evaluate (codes : List (Computation Context Key Value Result))
    (provider : Provider Context Key Value) (context : Context) :
    (sequence codes).evaluate provider context =
      Validation.traverse (fun code => code.evaluate provider context) codes := by
  induction codes with
  | nil => rfl
  | cons first rest ih =>
    simp only [sequence, evaluate, ih, Validation.traverse]
    cases first.evaluate provider context <;>
      cases Validation.traverse (fun code => code.evaluate provider context) rest <;> rfl

/-- Analysis includes the whole finite batch, even callbacks after an error.
This conservative footprint can safely govern later graph migrations. -/
theorem sequence_analyze (codes : List (Computation Context Key Value Result)) :
    (sequence codes).analyze = codes.foldr (fun code footprint => code.analyze.merge footprint) {} := by
  induction codes with
  | nil => rfl
  | cons first rest ih => simp [sequence, analyze, ih]

theorem sequence_error_iff (codes : List (Computation Context Key Value Result))
    (provider : Provider Context Key Value) (context : Context) (error : ComputationError Key) :
    (sequence codes).evaluate provider context = .error error ↔
      ∃ before code after values, codes = before ++ code :: after ∧
        (sequence before).evaluate provider context = .ok values ∧
        code.evaluate provider context = .error error := by
  simp only [sequence_evaluate]
  exact Validation.traverse_error_iff _ codes error

/-- Validation propagates a child error without invoking the check. -/
theorem validate_child_error (child : Computation Context Key Value Result)
    {Output : Context → Type w} (check : ∀ c, Result c → Except String (Output c))
    (provider : Provider Context Key Value) (context : Context) (error : ComputationError Key)
    (failed : child.evaluate provider context = .error error) :
    (child.validate check).evaluate provider context = .error error := by
  simp [evaluate, failed, Except.bind]

/-- Callback refusals remain source errors and do not fabricate capability errors. -/
theorem validate_rejected (child : Computation Context Key Value Result)
    {Output : Context → Type w} (check : ∀ c, Result c → Except String (Output c))
    (provider : Provider Context Key Value) (context : Context) (value : Result context) (message : String)
    (built : child.evaluate provider context = .ok value) (rejected : check context value = .error message) :
    (child.validate check).evaluate provider context = .error (.source message) := by
  simp [evaluate, built, rejected, Except.bind]
end LeanPoo.Functional.Computation
