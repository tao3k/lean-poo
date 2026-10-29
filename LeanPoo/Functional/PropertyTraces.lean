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

/-- An admitted host configuration contains exact natural steps and size.
None models configuration refusal before initialization; original callback causes
remain distinct from that refusal. Choice receives the unchanged declared size. -/
def configuredDraw (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (initial : Unit → Except Cause State)
    (disabled : Cause) (limits : Option (Nat × Nat)) : Except (Option Cause) (List Command) :=
  match limits with
  | none => .error none
  | some (steps, size) => match initial () with
    | .error cause => .error (some cause)
    | .ok state => match drawTrace model (fun state _ => choose state size) (min steps size) state with
      | .error _ => .error (some disabled)
      | .ok commands => .ok commands

/-- Invalid limits cannot depend on initialization or command callbacks. -/
theorem configuredDraw_refused (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (initial : Unit → Except Cause State) (disabled : Cause) :
    configuredDraw model choose initial disabled none = .error none := rfl

/-- A valid configuration preserves the initializer's original error. -/
theorem configuredDraw_initial_cause (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (cause disabled : Cause) (steps size : Nat) :
    configuredDraw model choose (fun _ => .error cause) disabled (some (steps, size)) =
      .error (some cause) := rfl

/-- Zero steps preserves successful initialization and draws no commands. -/
theorem configuredDraw_zero_steps (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (state : State) (disabled : Cause) (size : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (0, size)) = .ok [] := by
  simp [configuredDraw, drawTrace]

/-- Size zero bounds drawing even with a positive command cap. -/
theorem configuredDraw_zero_size (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (state : State) (disabled : Cause) (steps : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (steps, 0)) = .ok [] := by
  simp [configuredDraw, drawTrace]

/-- Every draw receives the original size, not a decreasing residual budget.
The existing pure draw engine owns the state transition and ordered prefix. -/
theorem configuredDraw_delegates (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (state : State) (disabled : Cause) (steps size : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (steps, size)) =
      match drawTrace model (fun state _ => choose state size) (min steps size) state with
      | .error _ => .error (some disabled)
      | .ok commands => .ok commands := rfl

/-- An explicit stop returns an empty suffix without command admission. -/
theorem configuredDraw_stop (model : TraceModel State Command Reply)
    (state : State) (disabled : Cause) (steps size : Nat) :
    configuredDraw model (fun _ _ => none) (fun _ => .ok state) disabled (some (steps, size)) =
      .ok [] := by
  cases cap : min steps size <;> simp [configuredDraw, cap, drawTrace]

/-- A disabled command is refused rather than silently omitted or advanced. -/
theorem configuredDraw_disabled (model : TraceModel State Command Reply)
    (state : State) (command : Command) (disabled : Cause) (notEnabled : model.enabled state command = false) :
    configuredDraw model (fun _ _ => some command) (fun _ => .ok state) disabled (some (1, 1)) =
      .error (some disabled) := by
  simp [configuredDraw, drawTrace, notEnabled]

/-- A successful generated prefix respects both independent caps and every
model precondition. Host normalization and accurate choice are premises. -/
theorem configuredDraw_sound (model : TraceModel State Command Reply)
    (choose : State → Nat → Option Command) (initial : Unit → Except Cause State)
    (state : State) (disabled : Cause) (steps size : Nat) (commands : List Command)
    (initialized : initial () = .ok state)
    (drawn : configuredDraw model choose initial disabled (some (steps, size)) = .ok commands) :
    traceValid model state commands = true ∧ commands.length ≤ steps ∧ commands.length ≤ size := by
  cases generated : drawTrace model (fun state _ => choose state size) (min steps size) state with
  | error cause => simp [configuredDraw, initialized, generated] at drawn
  | ok values =>
    have same : values = commands := by simpa [configuredDraw, initialized, generated] using drawn
    subst values
    obtain ⟨valid, bound⟩ := drawTrace_sound model (fun state _ => choose state size) _ state commands generated
    exact ⟨valid, Nat.le_trans bound (Nat.min_le_left _ _), Nat.le_trans bound (Nat.min_le_right _ _)⟩

/-- An enabled one-command result preserves the exact command payload. -/
theorem configuredDraw_single (model : TraceModel State Command Reply)
    (state : State) (command : Command) (disabled : Cause) (enabled : model.enabled state command = true) :
    configuredDraw model (fun _ _ => some command) (fun _ => .ok state) disabled (some (1, 1)) =
      .ok [command] := by
  simp [configuredDraw, drawTrace, enabled, Functor.map, Except.map]

end LeanPoo.Functional.PropertyTesting
