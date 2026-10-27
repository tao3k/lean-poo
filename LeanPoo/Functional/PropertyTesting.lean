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

/-- Canonical step replies/observations; expected domain refusals are Reply data. -/
def traceObservations (step : State → Command → State × Reply) (observe : State → Observation) :
    State → List Command → List (Reply × Observation)
  | _, [] => []
  | state, command :: rest =>
      let next := step state command
      (next.2, observe next.1) :: traceObservations step observe next.1 rest

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

end LeanPoo.Functional.PropertyTesting
