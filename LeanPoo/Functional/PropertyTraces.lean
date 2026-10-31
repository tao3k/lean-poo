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
remain distinct from that refusal. Choice receives the unchanged declared size and the existing remaining-fuel
observation index; repeated logical states need not make identical choices. -/
def configuredDraw (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (initial : Unit → Except Cause State)
    (disabled : Cause) (limits : Option (Nat × Nat)) : Except (Option Cause) (List Command) :=
  match limits with
  | none => .error none
  | some (steps, size) => match initial () with
    | .error cause => .error (some cause)
    | .ok state => match drawTrace model (fun state fuel => choose state size fuel) (min steps size) state with
      | .error _ => .error (some disabled)
      | .ok commands => .ok commands

/-- Invalid limits cannot depend on initialization or command callbacks. -/
theorem configuredDraw_refused (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (initial : Unit → Except Cause State) (disabled : Cause) :
    configuredDraw model choose initial disabled none = .error none := rfl

/-- A valid configuration preserves the initializer's original error. -/
theorem configuredDraw_initial_cause (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (cause disabled : Cause) (steps size : Nat) :
    configuredDraw model choose (fun _ => .error cause) disabled (some (steps, size)) =
      .error (some cause) := rfl

/-- Zero steps preserves successful initialization and draws no commands. -/
theorem configuredDraw_zero_steps (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (state : State) (disabled : Cause) (size : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (0, size)) = .ok [] := by
  simp [configuredDraw, drawTrace]

/-- Size zero bounds drawing even with a positive command cap. -/
theorem configuredDraw_zero_size (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (state : State) (disabled : Cause) (steps : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (steps, 0)) = .ok [] := by
  simp [configuredDraw, drawTrace]

/-- Every draw receives the original size, not a decreasing residual budget.
The existing pure draw engine owns the state transition and ordered prefix. -/
theorem configuredDraw_delegates (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (state : State) (disabled : Cause) (steps size : Nat) :
    configuredDraw model choose (fun _ => .ok state) disabled (some (steps, size)) =
      match drawTrace model (fun state fuel => choose state size fuel) (min steps size) state with
      | .error _ => .error (some disabled)
      | .ok commands => .ok commands := rfl

/-- An explicit stop returns an empty suffix without command admission. -/
theorem configuredDraw_stop (model : TraceModel State Command Reply)
    (state : State) (disabled : Cause) (steps size : Nat) :
    configuredDraw model (fun _ _ _ => none) (fun _ => .ok state) disabled (some (steps, size)) =
      .ok [] := by
  cases cap : min steps size <;> simp [configuredDraw, cap, drawTrace]

/-- A disabled command is refused rather than silently omitted or advanced. -/
theorem configuredDraw_disabled (model : TraceModel State Command Reply)
    (state : State) (command : Command) (disabled : Cause) (notEnabled : model.enabled state command = false) :
    configuredDraw model (fun _ _ _ => some command) (fun _ => .ok state) disabled (some (1, 1)) =
      .error (some disabled) := by
  simp [configuredDraw, drawTrace, notEnabled]

/-- A successful generated prefix respects both independent caps and every
model precondition. Host normalization and accurate choice are premises. -/
theorem configuredDraw_sound (model : TraceModel State Command Reply)
    (choose : State → Nat → Nat → Option Command) (initial : Unit → Except Cause State)
    (state : State) (disabled : Cause) (steps size : Nat) (commands : List Command)
    (initialized : initial () = .ok state)
    (drawn : configuredDraw model choose initial disabled (some (steps, size)) = .ok commands) :
    traceValid model state commands = true ∧ commands.length ≤ steps ∧ commands.length ≤ size := by
  cases generated : drawTrace model (fun state fuel => choose state size fuel) (min steps size) state with
  | error cause => simp [configuredDraw, initialized, generated] at drawn
  | ok values =>
    have same : values = commands := by simpa [configuredDraw, initialized, generated] using drawn
    subst values
    obtain ⟨valid, bound⟩ := drawTrace_sound model (fun state fuel => choose state size fuel) _ state commands generated
    exact ⟨valid, Nat.le_trans bound (Nat.min_le_left _ _), Nat.le_trans bound (Nat.min_le_right _ _)⟩

/-- An enabled one-command result preserves the exact command payload. -/
theorem configuredDraw_single (model : TraceModel State Command Reply)
    (state : State) (command : Command) (disabled : Cause) (enabled : model.enabled state command = true) :
    configuredDraw model (fun _ _ _ => some command) (fun _ => .ok state) disabled (some (1, 1)) =
      .ok [command] := by
  simp [configuredDraw, drawTrace, enabled, Functor.map, Except.map]

/-- One active use is admitted before fixture metadata preparation. The captured
use count is incremented by the host scope on every active attempt, even if the
caller catches its refusal. Preparation and actual execution retain the existing
source guard, value/state forwarding and exact exception causes. -/
def admitFixture (refusal : Cause) (live : State → Bool) (active : Bool) (uses : Nat)
    (prepare : Raw → State → Except Cause (Prepared × State))
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw) (state : State) :
    Except (Option Cause) (Report × State) :=
  if active && (uses == 1) then
    match guardedGeneration live (prepare raw) state with
    | .error cause => .error cause
    | .ok (prepared, next) => guardedGeneration live (run prepared) next
  else .error (some refusal)

/-- A closed callback cannot even enter raw fixture preparation. -/
theorem admitFixture_closed (refusal : Cause) (live : State → Bool) (uses : Nat)
    (prepare : Raw → State → Except Cause (Prepared × State))
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw) (state : State) :
    admitFixture refusal live false uses prepare run raw state = .error (some refusal) := by simp [admitFixture]

/-- A repeated active attempt skips all preparation and actual fixture effects. -/
theorem admitFixture_reused (refusal : Cause) (live : State → Bool) (active : Bool) (uses : Nat)
    (prepare : Raw → State → Except Cause (Prepared × State))
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw) (state : State)
    (reused : uses ≠ 1) : admitFixture refusal live active uses prepare run raw state = .error (some refusal) := by
  simp [admitFixture, reused]

/-- Lifetime admission never replaces a stale source with fresh preparation. -/
theorem admitFixture_stale (refusal : Cause) (live : State → Bool)
    (prepare : Raw → State → Except Cause (Prepared × State))
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw) (state : State)
    (stale : live state = false) : admitFixture refusal live true 1 prepare run raw state = .error none := by
  simp [admitFixture, guardedGeneration_preflight live (prepare raw) state stale]

/-- Metadata exceptions retain their exact cause; the actual run is unreachable. -/
theorem admitFixture_prepare_cause (refusal : Cause) (live : State → Bool) (state : State) (cause : Cause)
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw)
    (before : live state = true) :
    admitFixture refusal live true 1 (fun _ _ => .error cause) run raw state = .error (some cause) := by
  simp [admitFixture, guardedGeneration_cause live state cause before]

/-- A normal preparation that retires a captured Type cannot begin actual work. -/
theorem admitFixture_prepare_revised (refusal : Cause) (live : State → Bool) (state next : State) (prepared : Prepared)
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw)
    (before : live state = true) (after : live next = false) :
    admitFixture refusal live true 1 (fun _ _ => .ok (prepared, next)) run raw state = .error none := by
  simp [admitFixture, guardedGeneration_revised live state next prepared before after]

/-- Successful preparation passes its exact normalized fixture and state onward. -/
theorem admitFixture_forward (refusal : Cause) (live : State → Bool) (state next : State) (prepared : Prepared)
    (run : Prepared → State → Except Cause (Report × State)) (raw : Raw)
    (before : live state = true) (after : live next = true) :
    admitFixture refusal live true 1 (fun _ _ => .ok (prepared, next)) run raw state =
      guardedGeneration live (run prepared) next := by
  simp [admitFixture, guardedGeneration_state live state next prepared before after]

/-- An actual fixture failure is neither a mismatch nor a lifecycle refusal. -/
theorem admitFixture_run_cause (refusal : Cause) (live : State → Bool) (state next : State) (prepared : Prepared)
    (cause : Cause) (raw : Raw) (before : live state = true) (after : live next = true) :
    admitFixture refusal live true 1 (fun _ _ => .ok (prepared, next))
      (fun _ _ => (.error cause : Except Cause (Report × State))) raw state = .error (some cause) := by
  rw [admitFixture_forward refusal live state next prepared _ raw before after]
  exact guardedGeneration_cause live next cause after

/-- Scope delivery requires one active invocation and the exact observed receipt.
The host supplies identity equality; semantic field equality is insufficient. -/
def fixtureReceipt (uses : Nat) (sameReceipt : Bool) : Bool := (uses == 1) && sameReceipt

/-- Exactly one call may deliver its own receipt, including a mismatch report. -/
theorem fixtureReceipt_once (sameReceipt : Bool) : fixtureReceipt 1 sameReceipt = sameReceipt := rfl

/-- An earlier valid receipt cannot hide a caught duplicate or reentrant attempt. -/
theorem fixtureReceipt_reused (uses : Nat) (sameReceipt : Bool) (reused : uses ≠ 1) :
    fixtureReceipt uses sameReceipt = false := by simp [fixtureReceipt, reused]

/-- Further attempts cannot rehabilitate a scope whose use counter already exceeds one. -/
theorem fixtureReceipt_monotone_refusal (uses extra : Nat) (sameReceipt : Bool) (reused : 2 ≤ uses) :
    fixtureReceipt (uses + extra) sameReceipt = false := by
  apply fixtureReceipt_reused
  omega

/-- Finite semantic prefix of the lazy trace neighborhood. Only demanded raw
proposals are repaired; the actual Iterator/PRNG implementation remains a premise. -/
def repairedTracePrefix (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (proposals : List (List Command)) : List (List Command) :=
  (proposals.take budget).map (retire model state)

/-- Demand and repair commute for the finite observable prefix. No unvisited
parameter neighborhood must be constructed to obtain that same prefix. -/
theorem repairedTracePrefix_agrees (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (proposals : List (List Command)) :
    repairedTracePrefix model state budget proposals = (proposals.map (retire model state)).take budget := by
  induction budget generalizing proposals with
  | zero => rfl
  | succ budget ih =>
    cases proposals with
    | nil => rfl
    | cons head tail =>
      change retire model state head :: repairedTracePrefix model state budget tail =
        retire model state head :: (tail.map (retire model state)).take budget
      exact congrArg (List.cons _) (ih tail)

/-- One completed repair per returned proposal, bounded by the existing budget. -/
theorem repairedTracePrefix_budget (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (proposals : List (List Command)) :
    (repairedTracePrefix model state budget proposals).length ≤ budget := by
  simp only [repairedTracePrefix, List.length_map, List.length_take]
  exact Nat.min_le_left _ _

/-- No requested proposal performs any repair, even with a nonempty neighborhood. -/
theorem repairedTracePrefix_zero (model : TraceModel State Command Reply) (state : State)
    (proposals : List (List Command)) : repairedTracePrefix model state 0 proposals = [] := rfl

/-- Each demanded repaired candidate retains valid producer/consumer dependencies. -/
theorem repairedTracePrefix_valid (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (proposals : List (List Command)) (candidate : List Command)
    (member : candidate ∈ repairedTracePrefix model state budget proposals) :
    traceValid model state candidate = true := by
  obtain ⟨raw, _, rfl⟩ := List.mem_map.mp member
  exact retire_valid model raw state

/-- Repair never invents or reorders a command in its corresponding raw proposal. -/
theorem repairedTracePrefix_origin (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (proposals : List (List Command)) (candidate : List Command)
    (member : candidate ∈ repairedTracePrefix model state budget proposals) :
    ∃ raw ∈ proposals, candidate.Sublist raw := by
  obtain ⟨raw, selected, rfl⟩ := List.mem_map.mp member
  exact ⟨raw, List.mem_of_mem_take selected, retire_sublist model raw state⟩

/-- A sufficient structural prefix makes later parameter proposals irrelevant. -/
theorem repairedTracePrefix_tail (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (structural parameters : List (List Command)) (enough : budget ≤ structural.length) :
    repairedTracePrefix model state budget (structural ++ parameters) =
      repairedTracePrefix model state budget structural := by
  simp only [repairedTracePrefix, List.take_append_of_le_length enough]

/-- Replacing an unvisited parameter suffix cannot alter the result or repair count. -/
theorem repairedTracePrefix_parameters (model : TraceModel State Command Reply) (state : State)
    (budget : Nat) (structural left right : List (List Command)) (enough : budget ≤ structural.length) :
    repairedTracePrefix model state budget (structural ++ left) =
      repairedTracePrefix model state budget (structural ++ right) := by
  rw [repairedTracePrefix_tail model state budget structural left enough,
      repairedTracePrefix_tail model state budget structural right enough]

/-- Full deletion is the first structural candidate and needs no parameter proposal. -/
theorem repairedTracePrefix_full_deletion (model : TraceModel State Command Reply) (state : State)
    (parameters : List (List Command)) :
    repairedTracePrefix model state 1 ([] :: parameters) = [[]] := rfl

/-- That full-deletion candidate strictly decreases any nonempty trace's natural
structural-plus-parameter measure. Falsity is still checked by the existing runner. -/
theorem repairedTracePrefix_empty_smaller (weight : Command → Nat) (commands : List Command)
    (nonempty : 0 < commands.length) : traceWeight weight [] < traceWeight weight commands := by
  have lower := traceWeight_length weight commands
  simp only [traceWeight]
  omega

/-- The typed trace front door admits exact integer steps in its existing finite
range. Host recognition of fixnums and callable arity are executable premises. -/
def traceStepLimit (steps : Int) : Bool := decide (0 ≤ steps ∧ steps ≤ 65536)

/-- Zero steps remains a legal empty-trace request, not a refusal sentinel. -/
theorem traceStepLimit_zero : traceStepLimit 0 = true := rfl

/-- The existing upper endpoint is admitted without widening its range. -/
theorem traceStepLimit_maximum : traceStepLimit 65536 = true := rfl

/-- Negative steps refuse independently of model state or callback behavior. -/
theorem traceStepLimit_negative (steps : Int) (negative : steps < 0) :
    traceStepLimit steps = false := by
  simp [traceStepLimit]; omega

/-- Oversized steps likewise refuse rather than silently clamping. -/
theorem traceStepLimit_oversized (steps : Int) (large : 65536 < steps) :
    traceStepLimit steps = false := by
  simp [traceStepLimit]; omega

/-- Reuse the existing Boolean admission judgment before source observations:
invalid shape/callable configuration cannot prepare metadata or open a fixture. -/
theorem traceRequest_invalid (invalid : Cause) (live : State → Bool)
    (prepare : State → Except Cause (Value × State)) (state : State) :
    admitWitness (.ok false) invalid (fun _ => guardedGeneration live prepare state) =
      .error (some invalid) := rfl

/-- Invalid finite bounds use the same refusal, before source or metadata work. -/
theorem traceRequest_limit (steps : Int) (bad : traceStepLimit steps = false)
    (invalid : Cause) (live : State → Bool)
    (prepare : State → Except Cause (Value × State)) (state : State) :
    admitWitness (.ok (traceStepLimit steps)) invalid
      (fun _ => guardedGeneration live prepare state) = .error (some invalid) := by
  rw [bad]; rfl

/-- Valid static configuration forwards preparation to its original source owner. -/
theorem traceRequest_valid (invalid : Cause) (live : State → Bool)
    (prepare : State → Except Cause (Value × State)) (state : State) :
    admitWitness (.ok true) invalid (fun _ => guardedGeneration live prepare state) =
      guardedGeneration live prepare state := rfl

/-- Static validity does not authorize an already obsolete source. -/
theorem traceRequest_stale (invalid : Cause) (live : State → Bool)
    (prepare : State → Except Cause (Value × State)) (state : State)
    (stale : live state = false) :
    admitWitness (.ok true) invalid (fun _ => guardedGeneration live prepare state) =
      .error none := by simp [admitWitness, guardedGeneration, stale]

/-- A well-configured callback retains its original exception, including false. -/
theorem traceRequest_cause (invalid cause : Cause) (live : State → Bool)
    (state : State) (before : live state = true) :
    admitWitness (.ok true) invalid
      (fun _ => guardedGeneration live (fun _ => (.error cause : Except Cause (Value × State))) state) =
        .error (some cause) := by simp [admitWitness, guardedGeneration, before]

/-- Preparation cannot deliver a value after retiring its own declarations. -/
theorem traceRequest_revised (invalid : Cause) (live : State → Bool)
    (state next : State) (value : Value) (before : live state = true) (after : live next = false) :
    admitWitness (.ok true) invalid
      (fun _ => guardedGeneration live (fun _ => (.ok (value, next) : Except Cause (Value × State))) state) =
        .error none := by simp [admitWitness, guardedGeneration, before, after]

/-- Successful preparation preserves both its value and state exactly; it does
not change first-difference semantics or infer callback correctness. -/
theorem traceRequest_state (invalid : Cause) (live : State → Bool)
    (state next : State) (value : Value) (before : live state = true) (after : live next = true) :
    admitWitness (.ok true) invalid
      (fun _ => guardedGeneration live (fun _ => (.ok (value, next) : Except Cause (Value × State))) state) =
        .ok (value, next) := by simp [admitWitness, guardedGeneration, before, after]

/-- Capture the ingress request once, before declaration preparation can change
caller state. Request may pair an optional command row with explicit owner IDs.
Host shallow-copy fidelity and truthful revision observers remain premises. -/
def guardedTraceRequest (capture : State → Request) (live : State → Bool)
    (prepare : State → Except Cause (Prepared × State))
    (execute : Request → Prepared → State → Except Cause (Output × State)) (state : State) :
    Except (Option Cause) (Output × State) :=
  let owned := capture state
  match guardedGeneration live prepare state with
  | .error cause => .error cause
  | .ok (prepared, next) => guardedGeneration live (execute owned prepared) next

/-- Obsolete authority cannot enter declaration preparation or execution. Pure
capture may still occur; this is not a claim of zero host allocation. -/
theorem guardedTraceRequest_stale (capture : State → Request) (live : State → Bool)
    (prepare : State → Except Cause (Prepared × State))
    (execute : Request → Prepared → State → Except Cause (Output × State)) (state : State)
    (stale : live state = false) :
    guardedTraceRequest capture live prepare execute state = .error none := by
  simp [guardedTraceRequest, guardedGeneration, stale]

/-- Metadata exceptions retain their exact cause before any trailing source test. -/
theorem guardedTraceRequest_prepare_cause (capture : State → Request) (live : State → Bool)
    (cause : Cause) (execute : Request → Prepared → State → Except Cause (Output × State))
    (state : State) (before : live state = true) :
    guardedTraceRequest capture live (fun _ => .error cause) execute state =
      .error (some cause) := by simp [guardedTraceRequest, guardedGeneration, before]

/-- An explicit owner retired by metadata cannot authorize execution or a sampler. -/
theorem guardedTraceRequest_prepare_revised (capture : State → Request) (live : State → Bool)
    (prepared : Prepared) (execute : Request → Prepared → State → Except Cause (Output × State))
    (state next : State) (before : live state = true) (after : live next = false) :
    guardedTraceRequest capture live (fun _ => .ok (prepared, next)) execute state = .error none := by
  simp [guardedTraceRequest, guardedGeneration, before, after]

/-- A normal metadata return hands off the ORIGINAL request, not a new reading of
its edited state. None, empty rows, duplicates and false payloads remain distinct. -/
theorem guardedTraceRequest_handoff (capture : State → Request) (live : State → Bool)
    (prepared : Prepared) (execute : Request → Prepared → State → Except Cause (Output × State))
    (state next : State) (before : live state = true) (after : live next = true) :
    guardedTraceRequest capture live (fun _ => .ok (prepared, next)) execute state =
      guardedGeneration live (execute (capture state) prepared) next := by
  simp [guardedTraceRequest, guardedGeneration, before, after]

/-- Later observations are irrelevant when two captures agree at ingress. This
applies equally to the command row and the explicit dependency directory. -/
theorem guardedTraceRequest_ingress (left right : State → Request) (live : State → Bool)
    (prepare : State → Except Cause (Prepared × State))
    (execute : Request → Prepared → State → Except Cause (Output × State)) (state : State)
    (same : left state = right state) :
    guardedTraceRequest left live prepare execute state =
      guardedTraceRequest right live prepare execute state := by
  simp [guardedTraceRequest, same]

/-- Execution exceptions are not converted into a mismatch or new preparation. -/
theorem guardedTraceRequest_execute_cause (capture : State → Request) (live : State → Bool)
    (prepared : Prepared) (cause : Cause) (state next : State)
    (before : live state = true) (after : live next = true) :
    guardedTraceRequest capture live (fun _ => .ok (prepared, next))
      (fun _ _ _ => (.error cause : Except Cause (Output × State))) state = .error (some cause) := by
  simp [guardedTraceRequest, guardedGeneration, before, after]

/-- An action that retires its captured owners cannot deliver its normal result. -/
theorem guardedTraceRequest_execute_revised (capture : State → Request) (live : State → Bool)
    (prepared : Prepared) (output : Output) (state next final : State)
    (a : live state = true) (b : live next = true) (c : live final = false) :
    guardedTraceRequest capture live (fun _ => .ok (prepared, next))
      (fun _ _ _ => (.ok (output, final) : Except Cause (Output × State))) state = .error none := by
  simp [guardedTraceRequest, guardedGeneration, a, b, c]

/-- A successful request preserves its action's exact output and final state. -/
theorem guardedTraceRequest_state (capture : State → Request) (live : State → Bool)
    (prepared : Prepared) (output : Output) (state next final : State)
    (a : live state = true) (b : live next = true) (c : live final = true) :
    guardedTraceRequest capture live (fun _ => .ok (prepared, next))
      (fun _ _ _ => (.ok (output, final) : Except Cause (Output × State))) state = .ok (output, final) := by
  simp [guardedTraceRequest, guardedGeneration, a, b, c]

end LeanPoo.Functional.PropertyTesting
