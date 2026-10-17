import LeanPoo.Functional.Validation

/-! Predicate contracts delegated to a host guard, with POO refusal at the boundary.
The host premise is its Boolean/truthiness guard behavior, not compiler correctness.
Exceptions from predicates, normalization and consumers are outside local translation.
-/
namespace LeanPoo.Functional.ContractAdaptation
universe u v w x
variable {Input : Type u} {Checked : Type v} {Result : Type w} {Error : Type x}

/-- The host contract's local refusal has a separate type from user exceptions. -/
def hostGuard (accepted : Bool) (value : Input) : Except Unit Input :=
  if accepted then .ok value else .error ()

/-- Translate only the local guard refusal, preserving the accepted value. -/
def translate (refusal : Error) (localResult : Except Unit Input) : Except Error Input :=
  match localResult with
  | .ok value => .ok value
  | .error () => .error refusal

/-- Observe the user predicate before entering the local guard translation. -/
def adapt (predicate : Input → Except Error Bool) (refusal : Error) (value : Input) :
    Except Error Input :=
  (predicate value).bind fun accepted => translate refusal (hostGuard accepted value)

/-- The previous direct predicate boundary, independent of the host guard. -/
def direct (predicate : Input → Except Error Bool) (refusal : Error) (value : Input) :
    Except Error Input :=
  match predicate value with
  | .error error => .error error
  | .ok accepted => if accepted then .ok value else .error refusal

/-- Delegation preserves every result and error, for arbitrary predicates and values. -/
theorem adapt_eq_direct (predicate : Input → Except Error Bool) (refusal : Error) (value) :
    adapt predicate refusal value = direct predicate refusal value := by
  cases observed : predicate value with
  | error error => simp [adapt, direct, observed, Except.bind]
  | ok accepted => cases accepted <;> simp [adapt, direct, hostGuard, translate, observed, Except.bind]

/-- A predicate error is unchanged even when it has the same family as a host error. -/
theorem predicate_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (value) (failed : predicate value = .error error) :
    adapt predicate refusal value = .error error := by
  simp [adapt, failed, Except.bind]

/-- Shape checks finish before recursive wrapping; consumers receive the wrapped value. -/
def run (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value : Input) : Except Error Result :=
  (adapt predicate refusal value).bind fun original => (normalize original).bind consume

/-- The entire workflow preserves the previous direct boundary, including body errors. -/
theorem run_eq_direct (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result) (value) :
    run predicate refusal normalize consume value =
      (direct predicate refusal value).bind (fun original => (normalize original).bind consume) := by
  simp only [run, adapt_eq_direct]

/-- A failed shape check stops before normalization and observation. -/
theorem rejected (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value) (failed : predicate value = .ok false) :
    run predicate refusal normalize consume value = .error refusal := by
  simp [run, adapt, failed, hostGuard, translate, Except.bind]

/-- Successful wrapping feeds the checked result, rather than the original, to the consumer. -/
theorem normalized (predicate : Input → Except Error Bool) (refusal : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value checked) (accepted : predicate value = .ok true)
    (wrapped : normalize value = .ok checked) :
    run predicate refusal normalize consume value = consume checked := by
  simp [run, adapt, accepted, wrapped, hostGuard, translate, Except.bind]

/-- Normalizer errors, including recursive budget/cycle refusals, are never remapped. -/
theorem normalization_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value) (accepted : predicate value = .ok true) (failed : normalize value = .error error) :
    run predicate refusal normalize consume value = .error error := by
  simp [run, adapt, accepted, failed, hostGuard, translate, Except.bind]

/-- An error from a checked consumer is not caught by the local host guard adapter. -/
theorem consumer_error (predicate : Input → Except Error Bool) (refusal error : Error)
    (normalize : Input → Except Error Checked) (consume : Checked → Except Error Result)
    (value checked) (accepted : predicate value = .ok true)
    (wrapped : normalize value = .ok checked) (failed : consume checked = .error error) :
    run predicate refusal normalize consume value = .error error := by
  rw [normalized predicate refusal normalize consume value checked accepted wrapped, failed]

/-- Ordered batches inherit the same equivalence without a second traversal implementation. -/
theorem batch_eq_direct (predicate : Input → Except Error Bool) (refusal : Error)
    (values : List Input) :
    Validation.traverse (adapt predicate refusal) values =
      Validation.traverse (direct predicate refusal) values := by
  have same : adapt predicate refusal = direct predicate refusal :=
    funext (adapt_eq_direct predicate refusal)
  rw [same]
end LeanPoo.Functional.ContractAdaptation
