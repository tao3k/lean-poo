import LeanPoo.Functional.PropertyGenerators

/-! Finite revision-bound differential observations. State includes the declared
model/fixture epochs; host scope cleanup and callback termination are premises. -/
namespace LeanPoo.Functional.PropertyTesting
universe u

/-- Reference preparation precedes the actual step, which precedes comparison.
Each existing guarded action retains exact values, state and original causes. -/
def guardedTraceStep (live : State → Bool)
    (advance : State → Except Cause (Expected × State))
    (step : State → Except Cause (Actual × State))
    (compare : Expected → Actual → State → Except Cause (Bool × State)) (state : State) :
    Except (Option Cause) (Bool × State) :=
  match guardedGeneration live advance state with
  | .error cause => .error cause
  | .ok (expected, next) => match guardedGeneration live step next with
    | .error cause => .error cause
    | .ok (actual, observed) => guardedGeneration live (compare expected actual) observed

/-- An obsolete declaration cannot begin reference or fixture effects. -/
theorem guardedTraceStep_preflight (live : State → Bool)
    (advance : State → Except Cause (Expected × State)) (step : State → Except Cause (Actual × State))
    (compare : Expected → Actual → State → Except Cause (Bool × State)) (state : State)
    (stale : live state = false) : guardedTraceStep live advance step compare state = .error none := by
  simp [guardedTraceStep, guardedGeneration_preflight live advance state stale]

/-- A changed reference cannot authorize an actual fixture step. -/
theorem guardedTraceStep_reference_revised (live : State → Bool) (state next : State)
    (expected : Expected) (step : State → Except Cause (Actual × State))
    (compare : Expected → Actual → State → Except Cause (Bool × State))
    (before : live state = true) (after : live next = false) :
    guardedTraceStep live (fun _ => .ok (expected, next)) step compare state = .error none := by
  simp [guardedTraceStep, guardedGeneration_revised live state next expected before after]

/-- A declaration edit inside an actual step suppresses subsequent comparison. -/
theorem guardedTraceStep_fixture_revised (live : State → Bool) (state next : State)
    (expected : Expected) (actual : Actual)
    (compare : Expected → Actual → State → Except Cause (Bool × State))
    (before : live state = true) (after : live next = false) :
    guardedTraceStep live (fun _ => .ok (expected, state)) (fun _ => .ok (actual, next)) compare state =
      .error none := by
  simp [guardedTraceStep, guardedGeneration_state live state state expected before before,
    guardedGeneration_revised live state next actual before after]

/-- Reference callback failures retain their exact cause and skip the fixture. -/
theorem guardedTraceStep_reference_cause (live : State → Bool) (state : State) (cause : Cause)
    (step : State → Except Cause (Actual × State))
    (compare : Expected → Actual → State → Except Cause (Bool × State)) (before : live state = true) :
    guardedTraceStep live (fun _ => .error cause) step compare state = .error (some cause) := by
  simp [guardedTraceStep, guardedGeneration_cause live state cause before]

/-- Fixture callback failures are errors rather than mismatches or stale EOF. -/
theorem guardedTraceStep_fixture_cause (live : State → Bool) (state : State) (cause : Cause)
    (expected : Expected) (compare : Expected → Actual → State → Except Cause (Bool × State))
    (before : live state = true) :
    guardedTraceStep live (fun _ => .ok (expected, state)) (fun _ => .error cause) compare state =
      .error (some cause) := by
  simp [guardedTraceStep, guardedGeneration_state live state state expected before before,
    guardedGeneration_cause live state cause before]

/-- An observer/comparator exception retains its own cause after both steps. -/
theorem guardedTraceStep_comparison_cause (live : State → Bool) (state : State) (cause : Cause)
    (expected : Expected) (actual : Actual) (before : live state = true) :
    guardedTraceStep live (fun _ => .ok (expected, state)) (fun _ => .ok (actual, state))
      (fun _ _ _ => .error cause) state = .error (some cause) := by
  simp [guardedTraceStep, guardedGeneration_state live state state expected before before,
    guardedGeneration_state live state state actual before before,
    guardedGeneration_cause live state cause before]

/-- Even a true comparison cannot publish a report after changing its rules. -/
theorem guardedTraceStep_comparison_revised {Cause : Type u} (live : State → Bool) (state next : State)
    (expected : Expected) (actual : Actual) (matched : Bool)
    (before : live state = true) (after : live next = false) :
    guardedTraceStep (Cause := Cause) live (fun _ => .ok (expected, state)) (fun _ => .ok (actual, state))
      (fun _ _ _ => .ok (matched, next)) state = .error none := by
  simp [guardedTraceStep, guardedGeneration_state live state state expected before before,
    guardedGeneration_state live state state actual before before,
    guardedGeneration_revised live state next matched before after]

/-- Stable execution preserves both success and first-difference judgments exactly. -/
theorem guardedTraceStep_stable {Cause : Type u} (live : State → Bool) (state prepared observed final : State)
    (expected : Expected) (actual : Actual) (matched : Bool)
    (first : live state = true) (second : live prepared = true)
    (third : live observed = true) (last : live final = true) :
    guardedTraceStep (Cause := Cause) live (fun _ => .ok (expected, prepared)) (fun _ => .ok (actual, observed))
      (fun _ _ _ => .ok (matched, final)) state = .ok (matched, final) := by
  simp [guardedTraceStep, guardedGeneration_state live state prepared expected first second,
    guardedGeneration_state live prepared observed actual second third,
    guardedGeneration_state live observed final matched third last]

end LeanPoo.Functional.PropertyTesting
