import Std

/-! Descriptor-driven testing and shrinking is finite evidence. The model admits
only a smaller valid counterexample; it does not prove a sampled property universal,
PRNG quality, host callback termination, or global minimality. -/
namespace LeanPoo.Functional.PropertyTesting

/-- One shrink attempt records its candidate even if it is refused. -/
def admissible (valid fails : Value → Bool) (measure : Value → Nat) (best candidate : Value) : Bool :=
  valid candidate && decide (measure candidate < measure best) && fails candidate

/-- Every admitted step preserves the descriptor, falsity and strict descent. -/
theorem admissible_sound (valid fails : Value → Bool) (measure : Value → Nat) (best candidate : Value)
    (accepted : admissible valid fails measure best candidate = true) :
    valid candidate = true ∧ measure candidate < measure best ∧ fails candidate = true := by
  simpa [admissible, Bool.and_eq_true, and_assoc] using accepted

/-- A finite candidate stream charges every candidate, including invalid ones.
The Scheme driver restarts its stream after acceptance; each restart shares this
same decreasing budget. candidates models that possibly adaptive observed stream. -/
def shrink (valid fails : Value → Bool) (measure : Value → Nat) : Nat → Value → List Value → Value × Nat
  | 0, best, _ => (best, 0)
  | _ + 1, best, [] => (best, 0)
  | fuel + 1, best, candidate :: rest =>
    let next := if admissible valid fails measure best candidate then candidate else best
    let result := shrink valid fails measure fuel next rest
    (result.1, result.2 + 1)

/-- Invalid and nondecreasing candidates cannot evade the attempt bound. -/
theorem shrink_budget (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best : Value) (candidates : List Value) :
    (shrink valid fails measure fuel best candidates).2 ≤ fuel := by
  induction fuel generalizing best candidates with
  | zero => simp [shrink]
  | succ fuel ih =>
    cases candidates with
    | nil => simp [shrink]
    | cons candidate rest =>
      simpa only [shrink] using Nat.succ_le_succ (ih
        (if admissible valid fails measure best candidate then candidate else best) rest)

/-- Starting with a valid false witness, shrinking retains a valid false witness
and cannot increase its measure, even when the budget is exhausted. -/
theorem shrink_preserves (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best : Value) (candidates : List Value)
    (domain : valid best = true) (failure : fails best = true) :
    let result := (shrink valid fails measure fuel best candidates).1
    valid result = true ∧ fails result = true ∧ measure result ≤ measure best := by
  induction fuel generalizing best candidates with
  | zero => exact ⟨domain, failure, Nat.le_refl _⟩
  | succ fuel ih =>
    cases candidates with
    | nil => exact ⟨domain, failure, Nat.le_refl _⟩
    | cons candidate rest =>
      simp only [shrink]
      split
      next accepted =>
        obtain ⟨v, lower, f⟩ := admissible_sound valid fails measure best candidate accepted
        obtain ⟨rv, rf, bound⟩ := ih candidate rest v f
        exact ⟨rv, rf, Nat.le_trans bound (Nat.le_of_lt lower)⟩
      next refused => exact ih best rest domain failure

/-- Local minimality means exactly no immediate supplied admissible candidate. -/
def locallyMinimal (valid fails : Value → Bool) (measure : Value → Nat)
    (best : Value) (candidates : List Value) : Bool :=
  !(candidates.any (admissible valid fails measure best))

/-- A complete negative scan certifies only the supplied neighbourhood. -/
theorem locallyMinimal_iff (valid fails : Value → Bool) (measure : Value → Nat)
    (best : Value) (candidates : List Value) :
    locallyMinimal valid fails measure best candidates = true ↔
      ∀ candidate ∈ candidates, admissible valid fails measure best candidate = false := by
  simp [locallyMinimal, List.any_eq_false]

/-- Source stamps are a separate admission condition; a reusable seed is no proof
that descriptors or callback dependencies remained unchanged. -/
def admit [DecidableEq Stamp] (captured current : Stamp) (result : Result) : Option Result :=
  if captured = current then some result else none

/-- A changed dependency snapshot refuses both successes and counterexamples. -/
theorem admit_stale [DecidableEq Stamp] (captured current : Stamp) (result : Result)
    (changed : captured ≠ current) : admit captured current result = none := by
  simp [admit, changed]

/-- Deterministic replay is conditional on the same pure draw callback, seed and
size; Scheme requires additionally the same host PRNG and stable ambient state. -/
def samples (draw : Seed → Nat → Value × Seed) : Nat → Seed → Nat → List Value
  | 0, _, _ => []
  | n + 1, seed, size =>
    let (value, next) := draw seed size
    value :: samples draw n next size

theorem samples_length (draw : Seed → Nat → Value × Seed) (count seed size) :
    (samples draw count seed size).length = count := by
  induction count generalizing seed with
  | zero => rfl
  | succ n ih => simp [samples, ih]

/-- A typed reference protocol. Host descriptor/normalizer fidelity and callback
termination are separate premises; this finite model has no untyped fallback. -/
structure TraceModel (State Command Reply : Type) where
  initial : State
  enabled : State → Command → Bool
  advance : State → Command → State × Reply

/-- Whole-prefix validity, including the state produced by each retained command. -/
def traceValid (model : TraceModel State Command Reply) : State → List Command → Bool
  | _, [] => true
  | state, command :: rest =>
      model.enabled state command && traceValid model (model.advance state command).1 rest

/-- Semantic retirement omits a disabled dependent and continues from the SAME
state. It never renames handles, invents a producer or generates a new suffix. -/
def retire (model : TraceModel State Command Reply) : State → List Command → List Command
  | _, [] => []
  | state, command :: rest =>
      if model.enabled state command then
        command :: retire model (model.advance state command).1 rest
      else retire model state rest

/-- Every repaired sequence has valid dependencies under the pure model. -/
theorem retire_valid (model : TraceModel State Command Reply) (commands : List Command) (state : State) :
    traceValid model state (retire model state commands) = true := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    cases enabled : model.enabled state command <;> simp [retire, traceValid, enabled, ih]

/-- Retirement preserves the relative order of surviving commands. -/
theorem retire_sublist (model : TraceModel State Command Reply) (commands : List Command) (state : State) :
    (retire model state commands).Sublist commands := by
  induction commands generalizing state with
  | nil => exact List.Sublist.refl []
  | cons command rest ih =>
    cases enabled : model.enabled state command with
    | false => simpa [retire, enabled] using (ih state).cons command
    | true => simpa [retire, enabled] using (ih (model.advance state command).1).cons_cons command

/-- A valid supplied sequence is not rewritten by dependency retirement. -/
theorem retire_identity (model : TraceModel State Command Reply) (commands : List Command) (state : State)
    (valid : traceValid model state commands = true) : retire model state commands = commands := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    have both : model.enabled state command = true ∧
        traceValid model (model.advance state command).1 rest = true := by
      simpa only [traceValid, Bool.and_eq_true] using valid
    obtain ⟨enabled, tail⟩ := both
    simp [retire, enabled, ih _ tail]

/-- Positive command cost is exactly length plus the sum of parameter weights. -/
def traceWeight (weight : Command → Nat) : List Command → Nat
  | [] => 0
  | command :: rest => 1 + weight command + traceWeight weight rest

/-- Reference retirement cannot increase the complete shrink measure. -/
theorem retire_weight (model : TraceModel State Command Reply) (weight : Command → Nat)
    (commands : List Command) (state : State) :
    traceWeight weight (retire model state commands) ≤ traceWeight weight commands := by
  induction commands generalizing state with
  | nil => exact Nat.le_refl _
  | cons command rest ih =>
    cases enabled : model.enabled state command <;> simp only [retire, enabled, Bool.false_eq_true,
      ↓reduceIte, traceWeight]
    · have h := ih state; omega
    · have h := ih (model.advance state command).1; omega

/-- Smaller parameter/deletion proposals remain smaller after dependency retirement. -/
theorem retire_smaller (model : TraceModel State Command Reply) (weight : Command → Nat)
    (proposal original : List Command) (state : State)
    (smaller : traceWeight weight proposal < traceWeight weight original) :
    traceWeight weight (retire model state proposal) < traceWeight weight original :=
  Nat.lt_of_le_of_lt (retire_weight model weight proposal state) smaller

/-- Appending independent segments adds their complete parameter/length weights. -/
theorem traceWeight_append (weight : Command → Nat) (left right : List Command) :
    traceWeight weight (left ++ right) = traceWeight weight left + traceWeight weight right := by
  induction left with
  | nil => simp [traceWeight]
  | cons command rest ih => simp [traceWeight, ih, Nat.add_assoc]

/-- Deleting any one command and retiring its dependents strictly decreases weight. -/
theorem retire_deletion (model : TraceModel State Command Reply) (weight : Command → Nat)
    (before after : List Command) (command : Command) (state : State) :
    traceWeight weight (retire model state (before ++ after)) <
      traceWeight weight (before ++ command :: after) := by
  apply retire_smaller
  simp only [traceWeight_append, traceWeight]
  omega

/-- The existing shrink engine preserves a valid false trace within its budget. -/
theorem shrink_trace_preserves (model : TraceModel State Command Reply) (state : State)
    (fails : List Command → Bool) (weight : Command → Nat) (fuel : Nat)
    (witness : List Command) (proposals : List (List Command))
    (valid : traceValid model state witness = true) (failure : fails witness = true) :
    let result := (shrink (traceValid model state) fails (traceWeight weight) fuel witness proposals).1
    traceValid model state result = true ∧ fails result = true ∧
      traceWeight weight result ≤ traceWeight weight witness :=
  shrink_preserves _ _ _ _ _ _ valid failure

/-- Draw only a finite prefix. Disabled draws are explicit errors rather than
silently discarded trials. choose models the observed state-dependent choices. -/
def drawTrace (model : TraceModel State Command Reply) (choose : State → Nat → Option Command) :
    Nat → State → Except Unit (List Command)
  | 0, _ => .ok []
  | fuel + 1, state =>
      match choose state fuel with
      | none => .ok []
      | some command =>
          if model.enabled state command then do
            let rest ← drawTrace model choose fuel (model.advance state command).1
            pure (command :: rest)
          else .error ()

/-- Every successful finite draw has valid prefixes and respects its step cap. -/
theorem drawTrace_sound (model : TraceModel State Command Reply) (choose : State → Nat → Option Command)
    (fuel : Nat) (state : State) (commands : List Command)
    (drawn : drawTrace model choose fuel state = .ok commands) :
    traceValid model state commands = true ∧ commands.length ≤ fuel := by
  induction fuel generalizing state commands with
  | zero => simp [drawTrace] at drawn; subst commands; simp [traceValid]
  | succ fuel ih =>
    simp only [drawTrace] at drawn
    cases chosen : choose state fuel with
    | none => simp [chosen] at drawn; subst commands; simp [traceValid]
    | some command =>
      cases enabled : model.enabled state command with
      | false => simp [chosen, enabled] at drawn
      | true =>
        simp only [chosen, enabled, ↓reduceIte] at drawn
        cases tail : drawTrace model choose fuel (model.advance state command).1 with
        | error cause => simp [tail, Functor.map, Except.map] at drawn
        | ok rest =>
          simp [tail, Functor.map, Except.map] at drawn
          subst commands
          obtain ⟨valid, bound⟩ := ih _ _ tail
          exact ⟨by simp [traceValid, enabled, valid], by simp; omega⟩

/-- Decode and admit a complete finite trace before any fixture is opened.
Raw and executable commands may have different representations; rejection never
returns an executable prefix. Host decoder purity/termination are premises. -/
def prepareTrace (model : TraceModel State Command Reply) (normalize : Raw → Option Command) :
    State → List Raw → Option (List Command)
  | _, [] => some []
  | state, raw :: rest => do
      let command ← normalize raw
      if model.enabled state command then
        let tail ← prepareTrace model normalize (model.advance state command).1 rest
        pure (command :: tail)
      else none

/-- Successful preparation preserves every input position, decoded order, and
state-dependent admission. No consumer can run against its unnormalized input. -/
theorem prepareTrace_sound (model : TraceModel State Command Reply) (normalize : Raw → Option Command)
    (raws : List Raw) (state : State) (commands : List Command)
    (prepared : prepareTrace model normalize state raws = some commands) :
    traceValid model state commands = true ∧ commands.length = raws.length ∧
      commands = raws.filterMap normalize := by
  induction raws generalizing state commands with
  | nil => simp [prepareTrace] at prepared; subst commands; simp [traceValid]
  | cons raw rest ih =>
    cases decoded : normalize raw with
    | none => simp [prepareTrace, decoded] at prepared
    | some command =>
      cases enabled : model.enabled state command with
      | false => simp [prepareTrace, decoded, enabled] at prepared
      | true =>
        cases tail : prepareTrace model normalize (model.advance state command).1 rest with
        | none => simp [prepareTrace, decoded, enabled, tail] at prepared
        | some suffix =>
          simp [prepareTrace, decoded, enabled, tail] at prepared
          subst commands
          obtain ⟨valid, size, order⟩ := ih _ _ tail
          exact ⟨by simp [traceValid, enabled, valid], by simp [size], by simp [decoded, order]⟩

/-- Already normalized valid traces use the identity decoder without changing
command data. This is the typed facade's existing one-boundary validation path. -/
theorem prepareTrace_identity (model : TraceModel State Command Reply) (commands : List Command)
    (state : State) (valid : traceValid model state commands = true) :
    prepareTrace model some state commands = some commands := by
  induction commands generalizing state with
  | nil => rfl
  | cons command rest ih =>
    simp only [traceValid, Bool.and_eq_true] at valid
    simp [prepareTrace, valid.1, ih _ valid.2]

/-- Canonical step replies/observations; expected domain refusals are Reply data. -/
def traceObservations (step : State → Command → State × Reply) (observe : State → Observation) :
    State → List Command → List (Reply × Observation)
  | _, [] => []
  | state, command :: rest =>
      let next := step state command
      (next.2, observe next.1) :: traceObservations step observe next.1 rest

/-- The observation handoff consumes exactly the successfully prepared list.
Normalization is not rerun during execution; wrappers are opaque command data. -/
theorem prepared_observations (model : TraceModel State Command Reply)
    (normalize : Raw → Option Command) (step : State → Command → State × Reply)
    (observe : State → Observation) (raws : List Raw) (commands : List Command) (state : State)
    (prepared : prepareTrace model normalize state raws = some commands) :
    (prepareTrace model normalize state raws).map (traceObservations step observe state) =
      some (traceObservations step observe state commands) := by simp [prepared]

/-- An adapter's step simulation lifts to the complete ordered valid trace.
The relation must account for ownership, generation and every compared index. -/
theorem trace_simulation (model : TraceModel State Command Reply)
    (actualStep : Actual → Command → Actual × Reply)
    (observeModel : State → Observation) (observeActual : Actual → Observation)
    (related : State → Actual → Prop)
    (observed : ∀ state actual, related state actual → observeModel state = observeActual actual)
    (simulation : ∀ state actual command, related state actual → model.enabled state command = true →
      (model.advance state command).2 = (actualStep actual command).2 ∧
        related (model.advance state command).1 (actualStep actual command).1)
    (commands : List Command) (state : State) (actual : Actual)
    (current : related state actual) (valid : traceValid model state commands = true) :
    traceObservations model.advance observeModel state commands =
      traceObservations actualStep observeActual actual commands := by
  induction commands generalizing state actual with
  | nil => rfl
  | cons command rest ih =>
    have both : model.enabled state command = true ∧
        traceValid model (model.advance state command).1 rest = true := by
      simpa only [traceValid, Bool.and_eq_true] using valid
    obtain ⟨enabled, tail⟩ := both
    obtain ⟨reply, next⟩ := simulation state actual command current enabled
    simp only [traceObservations]
    rw [reply, observed _ _ next, ih _ _ next tail]

/-- The first differing element is reported before later dependent execution. -/
def firstDifference [DecidableEq Value] : List Value → List Value → Option Nat
  | [], [] => none
  | left :: ls, right :: rs => if left = right then (firstDifference ls rs).map Nat.succ else some 0
  | _, _ => some 0

/-- A complete successful comparison is equivalent to equal finite observations. -/
theorem firstDifference_none [DecidableEq Value] (left right : List Value) :
    firstDifference left right = none ↔ left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp [firstDifference]
  | cons value rest ih =>
    cases right with
    | nil => simp [firstDifference]
    | cons other tail =>
      by_cases same : value = other <;> simp [firstDifference, same, ih]

/-- Concrete replay first reuses stamp admission, then checks the entire witness.
There is no PRNG input; evaluation remains delayed until both gates succeed. -/
def replayTrace [DecidableEq Stamp] (captured current : Stamp) (valid evaluate : List Command → Bool)
    (commands : List Command) : Option Bool :=
  match admit captured current commands with
  | none => none
  | some witness => if valid witness then some (evaluate witness) else none

/-- Specification revisions reject concrete replay before witness execution. -/
theorem replayTrace_stale [DecidableEq Stamp] (captured current : Stamp)
    (valid evaluate : List Command → Bool) (commands : List Command) (changed : captured ≠ current) :
    replayTrace captured current valid evaluate commands = none := by simp [replayTrace, admit, changed]

/-- A current valid false witness reproduces independently of seed selection. -/
theorem replayTrace_failed [DecidableEq Stamp] (stamp : Stamp) (valid evaluate : List Command → Bool)
    (commands : List Command) (domain : valid commands = true) (failure : evaluate commands = false) :
    replayTrace stamp stamp valid evaluate commands = some false := by
  simp [replayTrace, admit, domain, failure]

/-- Select a logical producer ID from current retained handles. A trace step
number is only a lower bound, since a supplied prefix may contain arbitrary IDs. -/
def freshHandle (start : Nat) (used : List Nat) : Nat :=
  used.foldl (fun next handle => max next (handle + 1)) start

/-- Fresh selection preserves the caller's monotone lower bound. -/
theorem freshHandle_lower (start : Nat) (used : List Nat) : start ≤ freshHandle start used := by
  induction used generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
    change start ≤ freshHandle (max start (head + 1)) tail
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Every retained producer is strictly below the selected new handle, including
IDs larger than the current step count and IDs retained across source epochs. -/
theorem freshHandle_gt (start : Nat) (used : List Nat) (handle : Nat) (member : handle ∈ used) :
    handle < freshHandle start used := by
  induction used generalizing start with
  | nil => simp at member
  | cons head tail ih =>
    change handle < freshHandle (max start (head + 1)) tail
    rcases List.mem_cons.mp member with same | later
    · subst handle
      have lower := freshHandle_lower (max start (head + 1)) tail
      have upper := Nat.le_max_right start (head + 1)
      omega
    · exact ih _ later

/-- Selection cannot recreate any still-retained logical producer. -/
theorem freshHandle_not_mem (start : Nat) (used : List Nat) : freshHandle start used ∉ used := by
  intro member
  have impossible := freshHandle_gt start used _ member
  omega

/-- A finite observation of a lazy child iterator records only forced values.
EOF consumes a pull but is not a shrink attempt; no lookahead happens at zero fuel. -/
structure ForcedChildren (Value : Type) where
  values : List Value
  pulls : Nat
  exhausted : Bool

/-- Pure iterator approximation; arbitrary host callback termination remains a
premise, while the number of next requests is bounded independently of the tail. -/
def forceChildren (next : Nat → Option Value) : Nat → Nat → ForcedChildren Value
  | 0, _ => ⟨[], 0, false⟩
  | fuel + 1, offset => match next offset with
    | none => ⟨[], 1, true⟩
    | some value =>
      let rest := forceChildren next fuel (offset + 1)
      ⟨value :: rest.values, rest.pulls + 1, rest.exhausted⟩

/-- No unused iterator element is requested after the specified pull budget. -/
theorem forceChildren_bounded (next : Nat → Option Value) (fuel offset : Nat) :
    (forceChildren next fuel offset).pulls ≤ fuel := by
  induction fuel generalizing offset with
  | zero => simp [forceChildren]
  | succ fuel ih =>
    cases chosen : next offset <;> simp only [forceChildren, chosen]
    · omega
    · have bounded := ih (offset + 1); omega

/-- Every returned value corresponds to a pull, and observed EOF is exactly one
additional pull. This justifies conservative minimality at the budget boundary. -/
theorem forceChildren_accounting (next : Nat → Option Value) (fuel offset : Nat) :
    (forceChildren next fuel offset).pulls =
      (forceChildren next fuel offset).values.length +
        (if (forceChildren next fuel offset).exhausted then 1 else 0) := by
  induction fuel generalizing offset with
  | zero => rfl
  | succ fuel ih =>
    cases chosen : next offset <;> simp only [forceChildren, chosen]
    · rfl
    · have tail := ih (offset + 1)
      simp only [List.length_cons]
      omega

/-- Mapping preserves the original preimage even when the function is lossy. -/
theorem mapped_candidate_preimage (transform : Input → Output) (parents : List Input)
    (value : Output) (member : value ∈ parents.map transform) :
    ∃ original ∈ parents, transform original = value := List.mem_map.mp member

/-- A finite dependent-bind prefix retains each selected parent alongside the
child proof receipt. The public generated value may hide this private provenance. -/
def dependentCandidates (parents : List Parent) (select : Parent → Nat → List Child)
    (seed : Nat) : List (Parent × Child) :=
  parents.flatMap fun parent => (select parent seed).map (parent, ·)

/-- Every dependent child still satisfies its original parent's domain relation. -/
theorem dependentCandidates_relation (parents : List Parent) (select : Parent → Nat → List Child)
    (seed : Nat) (relation : Parent → Child → Prop)
    (valid : ∀ parent ∈ parents, ∀ child ∈ select parent seed, relation parent child)
    (entry : Parent × Child) (member : entry ∈ dependentCandidates parents select seed) :
    relation entry.1 entry.2 := by
  obtain ⟨parent, present, childMember⟩ := List.mem_flatMap.mp member
  obtain ⟨child, selected, same⟩ := List.mem_map.mp childMember
  cases same
  exact valid parent present child selected

/-- Adding newly observed sources never authorizes an already stale observation. -/
theorem stale_observation_retained (current : Source → Bool) (past more : List Source)
    (stale : past.all current = false) : (more ++ past).all current = false := by
  simp [List.all_append, stale]

/-- Finite observed events distinguish a returned proposal whose callback failed
from an iterator exception that produced no proposal. Restarts remain in order. -/
inductive ShrinkEvent (Value Cause : Type) where
  | candidate (value : Value)
  | callbackError (value : Value) (cause : Cause)
  | iteratorError (cause : Cause)

/-- Only fully evaluated candidates may influence the confirmed witness. The
receipt also retains charged work and the original first interruption. -/
structure ShrinkAudit (Value Cause : Type) where
  completed : List Value
  attempts : Nat
  interruption : Option Cause

/-- Observe at most the shared attempt budget and stop at the first exception.
A failed returned proposal is charged but is never added to completed. -/
def auditShrinks : Nat → List (ShrinkEvent Value Cause) → ShrinkAudit Value Cause
  | 0, _ => ⟨[], 0, none⟩
  | _ + 1, [] => ⟨[], 0, none⟩
  | fuel + 1, .candidate value :: rest =>
      let tail := auditShrinks fuel rest
      ⟨value :: tail.completed, tail.attempts + 1, tail.interruption⟩
  | _ + 1, .callbackError _ cause :: _ => ⟨[], 1, some cause⟩
  | _ + 1, .iteratorError cause :: _ => ⟨[], 0, some cause⟩

/-- Every completed candidate is charged, including refused candidates, and the
first interruption cannot reset the attempt accounting to zero. -/
theorem auditShrinks_budget (fuel : Nat) (events : List (ShrinkEvent Value Cause)) :
    (auditShrinks fuel events).completed.length ≤ (auditShrinks fuel events).attempts ∧
    (auditShrinks fuel events).attempts ≤ fuel := by
  induction fuel generalizing events with
  | zero => simp [auditShrinks]
  | succ fuel ih =>
    cases events with
    | nil => simp [auditShrinks]
    | cons event rest =>
      cases event with
      | candidate value =>
        obtain ⟨charged, bound⟩ := ih rest
        simp only [auditShrinks, List.length_cons]
        constructor <;> omega
      | callbackError value cause => simp [auditShrinks]
      | iteratorError cause => simp [auditShrinks]

/-- Exception receipts reuse the established admission/descent engine. With a
valid false initial witness, earlier confirmations survive the interruption;
error data itself is never treated as a smaller false candidate. -/
theorem interrupted_shrink_preserves (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best : Value) (events : List (ShrinkEvent Value Cause))
    (domain : valid best = true) (failure : fails best = true) :
    let receipt := auditShrinks fuel events
    let witness := (shrink valid fails measure fuel best receipt.completed).1
    valid witness = true ∧ fails witness = true ∧ measure witness ≤ measure best ∧
      receipt.attempts ≤ fuel := by
  obtain ⟨v, f, descent⟩ := shrink_preserves valid fails measure fuel best
    (auditShrinks fuel events).completed domain failure
  exact ⟨v, f, descent, (auditShrinks_budget fuel events).2⟩

/-- A callback error consumes its proposal but keeps the previously confirmed
witness. The unevaluated suffix and failing proposal cannot be installed. -/
theorem callback_error_retains (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best pending : Value) (cause : Cause) (rest : List (ShrinkEvent Value Cause)) :
    let receipt := auditShrinks (fuel + 1) (.callbackError pending cause :: rest)
    receipt.attempts = 1 ∧ receipt.interruption = some cause ∧
      (shrink valid fails measure (fuel + 1) best receipt.completed).1 = best := by
  simp [auditShrinks, shrink]


/-- Only effective generated trials contribute labels; shrink probes have no event here. -/
structure TrialLedger (Label : Type) where
  attempts : Nat := 0
  accepted : Nat := 0
  discarded : Nat := 0
  labels : List Label := []

/-- A trial either contributes effective coverage or consumes discard budget. -/
def recordTrial (ledger : TrialLedger Label) (eligible : Bool) (labels : List Label) : TrialLedger Label :=
  if eligible then { ledger with attempts := ledger.attempts + 1, accepted := ledger.accepted + 1, labels := ledger.labels ++ labels }
  else { ledger with attempts := ledger.attempts + 1, discarded := ledger.discarded + 1 }

/-- Successful generation accounting is conserved independently of classification. -/
theorem recordTrial_accounting (ledger : TrialLedger Label) (eligible : Bool) (labels : List Label)
    (balanced : ledger.attempts = ledger.accepted + ledger.discarded) :
    (recordTrial ledger eligible labels).attempts =
      (recordTrial ledger eligible labels).accepted + (recordTrial ledger eligible labels).discarded := by
  cases eligible <;> simp [recordTrial] <;> omega

/-- Discarded inputs never inflate classification coverage. -/
theorem discarded_labels (ledger : TrialLedger Label) (labels : List Label) :
    (recordTrial ledger false labels).labels = ledger.labels := rfl

/-- Coverage thresholds are application admission, not a probability theorem. -/
def coverageAdmitted [DecidableEq Label] (requested : Nat) (required : List (Label × Nat))
    (ledger : TrialLedger Label) : Prop :=
  0 < requested ∧ ledger.accepted = requested ∧ ∀ entry ∈ required, entry.2 ≤ ledger.labels.count entry.1

/-- A run with no effective trials cannot pass, even with empty requirements. -/
theorem all_discard_refused [DecidableEq Label] (required : List (Label × Nat))
    (ledger : TrialLedger Label) (empty : ledger.accepted = 0) :
    ¬ coverageAdmitted requested required ledger := by
  intro h
  obtain ⟨positive, enough, _⟩ := h
  omega

/-- Every admitted run satisfies every declared minimum effective count. -/
theorem coverage_threshold [DecidableEq Label] {ledger : TrialLedger Label}
    {required : List (Label × Nat)} {entry : Label × Nat}
    (admitted : coverageAdmitted requested required ledger)
    (member : entry ∈ required) : entry.2 ≤ ledger.labels.count entry.1 := admitted.2.2 entry member

/-- Finite event auditing records only generation events, never shrink probes. -/
def auditTrials (ledger : TrialLedger Label) (events : List (Bool × List Label)) : TrialLedger Label :=
  events.foldl (fun state event => recordTrial state event.1 event.2) ledger

/-- Each audited generation consumes exactly one trial, regardless of eligibility. -/
theorem auditTrials_attempts (events : List (Bool × List Label)) (ledger : TrialLedger Label) :
    (auditTrials ledger events).attempts = ledger.attempts + events.length := by
  induction events generalizing ledger with
  | nil => simp [auditTrials]
  | cons event rest ih =>
    simp only [auditTrials, List.foldl_cons]
    rw [show List.foldl (fun state event => recordTrial state event.1 event.2)
      (recordTrial ledger event.1 event.2) rest = auditTrials (recordTrial ledger event.1 event.2) rest from rfl]
    rw [ih]
    cases event.1 <;> simp [recordTrial] <;> omega

/-- A bounded generation prefix cannot consume more than its declared trial budget. -/
theorem bounded_trials (events : List (Bool × List Label)) (ledger : TrialLedger Label) (budget : Nat) :
    (auditTrials ledger (events.take budget)).attempts ≤ ledger.attempts + budget := by
  rw [auditTrials_attempts]
  exact Nat.add_le_add_left (List.length_take_le _ _) _

/-- Portable replay carries application identity and finite encoded data only. -/
structure ReplayEnvelope (Identity Encoded : Type) where
  identity : Identity
  payload : Encoded

/-- Identity admission precedes application decoding and fixture construction. -/
def decodeReplay [DecidableEq Identity] (expected : Identity) (decode : Encoded → Option Value)
    (envelope : ReplayEnvelope Identity Encoded) : Option Value :=
  if envelope.identity = expected then decode envelope.payload else none

/-- A changed protocol cannot decode an old witness. -/
theorem replay_identity_refused [DecidableEq Identity] (decode : Encoded → Option Value)
    (envelope : ReplayEnvelope Identity Encoded) (changed : envelope.identity ≠ expected) :
    decodeReplay expected decode envelope = none := by simp [decodeReplay, changed]

/-- Codec recovery is conditional on the application's explicit round-trip law. -/
theorem replay_roundtrip [DecidableEq Identity] (encode : Value → Encoded)
    (decode : Encoded → Option Value) (law : ∀ value, decode (encode value) = some value)
    (identity : Identity) (value : Value) :
    decodeReplay identity decode ⟨identity, encode value⟩ = some value := by
  simp [decodeReplay, law]

/-- Identity refusal propagates without admitting a fixture result. -/
theorem replay_refused_before_fixture [DecidableEq Identity] (decode : Encoded → Option Value)
    (fixture : Value → Option Result) (envelope : ReplayEnvelope Identity Encoded)
    (changed : envelope.identity ≠ expected) :
    (decodeReplay expected decode envelope).bind fixture = none := by
  simp [replay_identity_refused decode envelope changed]

/-- A bounded function is an explicit argument-row to result-tuple table. -/
def lookupFunction [DecidableEq Input] (table : List (Input × Output)) (input : Input) : Option Output :=
  match table with
  | [] => none
  | (key, value) :: rest => if input = key then some value else lookupFunction rest input

/-- An absent argument row is refused rather than assigned a fallback result. -/
theorem unknown_function_row [DecidableEq Input] (table : List (Input × Output))
    (absent : ∀ entry ∈ table, input ≠ entry.1) : lookupFunction table input = none := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    simp only [lookupFunction]
    rw [if_neg (absent entry (by simp))]
    apply ih
    intro row member
    exact absent row (by simp [member])

/-- Result-only shrinking preserves lookup keys and transforms their selected result. -/
theorem mapped_function_lookup [DecidableEq Input] (table : List (Input × Output))
    (transform : Output → Smaller) :
    lookupFunction (table.map (fun entry => (entry.1, transform entry.2))) input =
      (lookupFunction table input).map transform := by
  induction table with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, lookupFunction]
    split <;> simp_all


/-- The report vocabulary is retained when translating into standard unit checks. -/
inductive CheckStatus where
  | passed | failed | error | stale | exhausted | unsupported | coverage
  deriving DecidableEq, Repr

/-- Diagnostic arguments and the original cause are data, not executable callbacks. -/
structure CheckDiagnostics (Value Cause : Type) where
  status : CheckStatus
  current : Bool
  arguments : List (String × Value)
  cause : Option Cause

/-- Formerly passing evidence must still be current when a delayed check is asserted. -/
def checkedStatus (status : CheckStatus) (current : Bool) : CheckStatus :=
  if status = .passed ∧ current = false then .stale else status

/-- Standard checks have two outcomes; their failure retains the full PBT diagnosis. -/
def admitCheck (diagnostics : CheckDiagnostics Value Cause) : Except (CheckDiagnostics Value Cause) Unit :=
  let admitted := { diagnostics with status := checkedStatus diagnostics.status diagnostics.current }
  if admitted.status = .passed then .ok () else .error admitted

/-- A standard successful check requires both a passed report and live sources. -/
theorem admitCheck_ok (diagnostics : CheckDiagnostics Value Cause) :
    admitCheck diagnostics = .ok () ↔ diagnostics.status = .passed ∧ diagnostics.current = true := by
  cases diagnostics with
  | mk status current arguments cause =>
    cases status <;> cases current <;> simp [admitCheck, checkedStatus]

/-- Coverage, exhaustion, unsupported generation and callback errors are not falsification. -/
theorem checkedStatus_preserves_nonpass (status : CheckStatus) (current : Bool)
    (nonpass : status ≠ .passed) : checkedStatus status current = status := by
  simp [checkedStatus, nonpass]

/-- Diagnostics preserve original exception identity and named argument values. -/
theorem admitCheck_preserves (diagnostics failure : CheckDiagnostics Value Cause)
    (refused : admitCheck diagnostics = .error failure) :
    failure.cause = diagnostics.cause ∧ failure.arguments = diagnostics.arguments := by
  simp only [admitCheck] at refused
  split at refused
  · contradiction
  · cases refused
    exact ⟨rfl, rfl⟩

/-- Product admission checks exact row shape and every argument's own fixed domain. -/
def productDomain (domains : List (Value → Bool)) (values : List Value) : Bool :=
  match domains, values with
  | [], [] => true
  | domain :: rest, value :: tail => domain value && productDomain rest tail
  | _, _ => false

/-- A valid row has no missing/extra positions and satisfies each component domain. -/
theorem productDomain_sound (domains : List (Value → Bool)) (values : List Value)
    (accepted : productDomain domains values = true) :
    domains.length = values.length ∧
      ∀ entry ∈ domains.zip values, entry.1 entry.2 = true := by
  induction domains generalizing values with
  | nil =>
    cases values with
    | nil => exact ⟨rfl, by simp⟩
    | cons value rest => simp [productDomain] at accepted
  | cons domain rest ih =>
    cases values with
    | nil => simp [productDomain] at accepted
    | cons value tail =>
      simp only [productDomain, Bool.and_eq_true] at accepted
      obtain ⟨length, members⟩ := ih tail accepted.2
      refine ⟨by simp [length], ?_⟩
      intro entry member
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact accepted.1
      · exact members entry member

/-- The diagnostic binding count matches every admitted generated argument row. -/
theorem productDomain_length (domains : List (Value → Bool)) (values : List Value)
    (accepted : productDomain domains values = true) : domains.length = values.length :=
  (productDomain_sound domains values accepted).1

/-- Finite offset generation represents the interval used by characters and octets. -/
def intervalValue (lower offset : Nat) : Nat := lower + offset

/-- Draws stay inside their explicit inclusive interval, without rejection retries. -/
theorem intervalValue_bounds (lower upper offset : Nat)
    (ordered : lower ≤ upper) (bounded : offset ≤ upper - lower) :
    lower ≤ intervalValue lower offset ∧ intervalValue lower offset ≤ upper := by
  simp only [intervalValue]
  omega

/-- Shrinking an interval offset preserves membership and strictly decreases rank. -/
theorem intervalValue_shrink (lower upper offset smaller : Nat)
    (ordered : lower ≤ upper) (bounded : offset ≤ upper - lower) (decreases : smaller < offset) :
    lower ≤ intervalValue lower smaller ∧ intervalValue lower smaller ≤ upper ∧
      intervalValue lower smaller < intervalValue lower offset := by
  simp only [intervalValue]
  omega

/-- Unicode scalar ranks exclude the surrogate gap while preserving order. -/
def scalarCode (rank : Nat) : Nat := if rank < 0xd800 then rank else rank + 0x800

/-- Every bounded scalar rank becomes a valid Unicode scalar, including both boundaries. -/
theorem scalarCode_valid (rank : Nat) (bounded : rank < 0x10f800) :
    scalarCode rank ≤ 0x10ffff ∧ (scalarCode rank < 0xd800 ∨ 0xdfff < scalarCode rank) := by
  unfold scalarCode
  split <;> omega

/-- Scalar rank reduction cannot cross into the surrogate gap or reverse ordering. -/
theorem scalarCode_strict (left right : Nat) (smaller : left < right) :
    scalarCode left < scalarCode right := by
  unfold scalarCode
  split <;> split <;> omega

/-- Sequence generation admits a required prefix plus a bounded size-controlled suffix. -/
def dataLength (minimum _size _capacity offset : Nat) : Nat := minimum + offset

/-- Required byte widths remain valid even at generator size zero. -/
theorem dataLength_bounds (minimum size capacity offset : Nat)
    (bounded : offset ≤ min size capacity) :
    minimum ≤ dataLength minimum size capacity offset ∧
      dataLength minimum size capacity offset ≤ minimum + capacity := by
  simp only [dataLength]
  have := (Nat.le_min.mp bounded).2
  omega

/-- A fixed width selects exactly that width regardless of the size hint. -/
theorem dataLength_fixed (minimum size offset : Nat) (bounded : offset ≤ min size 0) :
    dataLength minimum size 0 offset = minimum := by
  simp only [dataLength]
  simp at bounded
  omega

/-- Carrier mappings preserve domain membership under their stated representation law.
This is conditional: it does not certify Gerbil's runtime encoders or reader. -/
theorem dataCarrier_domain (valid : Value → Prop) (packedValid : Carrier → Prop)
    (pack : List Value → Carrier)
    (law : ∀ values, (∀ value ∈ values, valid value) → packedValid (pack values))
    (values : List Value) (members : ∀ value ∈ values, valid value) :
    packedValid (pack values) := law values members

end LeanPoo.Functional.PropertyTesting
