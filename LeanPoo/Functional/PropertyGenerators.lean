import LeanPoo.Functional.PropertyTesting

/-! Finite generator composition laws. Offsets, policies and callbacks are explicit
inputs; these laws do not establish host PRNG quality or callback termination. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Observer union compares stable source identities, never current truth values. -/
def mergeSources [DecidableEq Source] (left right : List Source) : List Source :=
  (left ++ right).eraseDups

/-- Identity deduplication retains every old or newly visited source. -/
theorem mergeSources_mem [DecidableEq Source] (source : Source) (left right : List Source) :
    source ∈ mergeSources left right ↔ source ∈ left ∨ source ∈ right := by
  simp [mergeSources]

/-- Flattening guards cannot authorize a stale old branch with fresh newer metadata. -/
theorem mergeSources_current [DecidableEq Source] (current : Source → Bool) (left right : List Source) :
    (mergeSources left right).all current = true ↔ left.all current = true ∧ right.all current = true := by
  simp [List.all_eq_true, mergeSources_mem, or_imp, forall_and]

/-- Sharing an already-owned source list retains the same freshness judgment. -/
theorem mergeSources_shared_current [DecidableEq Source] (current : Source → Bool)
    (sources : List Source) :
    (mergeSources sources sources).all current = true ↔ sources.all current = true := by
  simpa using mergeSources_current current sources sources

/-- An empty owner adds no authority and removes no earlier epoch. -/
theorem mergeSources_empty_current [DecidableEq Source] (current : Source → Bool)
    (sources : List Source) :
    (mergeSources sources []).all current = true ↔ sources.all current = true := by
  simpa using mergeSources_current current sources []

/-- Select a weighted interval. Zero-weight branches have no possible offset. -/
def weightedChoice : List (Nat × Value) → Nat → Option Value
  | [], _ => none
  | (weight, value) :: rest, offset =>
    if offset < weight then some value else weightedChoice rest (offset - weight)

/-- Every selected value belongs to a positive-weight branch of the captured table. -/
theorem weightedChoice_member (entries : List (Nat × Value)) (offset : Nat) (value : Value)
    (selected : weightedChoice entries offset = some value) :
    ∃ weight, (weight, value) ∈ entries ∧ 0 < weight := by
  induction entries generalizing offset with
  | nil => simp [weightedChoice] at selected
  | cons head rest ih =>
    obtain ⟨weight, candidate⟩ := head
    simp only [weightedChoice] at selected
    split at selected
    next inside =>
      have same : candidate = value := Option.some.inj selected
      subst candidate
      exact ⟨weight, List.mem_cons_self, by omega⟩
    next outside =>
      obtain ⟨w, member, positive⟩ := ih _ selected
      exact ⟨w, List.mem_cons_of_mem _ member, positive⟩

/-- A valid offset in a finite positive total cannot fall out of the table. -/
theorem weightedChoice_exists (entries : List (Nat × Value)) (offset : Nat)
    (bounded : offset < (entries.map Prod.fst).sum) :
    ∃ value, weightedChoice entries offset = some value := by
  induction entries generalizing offset with
  | nil => simp at bounded
  | cons head rest ih =>
    obtain ⟨weight, value⟩ := head
    by_cases inside : offset < weight
    · exact ⟨value, by simp [weightedChoice, inside]⟩
    · have remaining : offset - weight < (rest.map Prod.fst).sum := by
        simp only [List.map_cons, List.sum_cons] at bounded
        omega
      obtain ⟨candidate, selected⟩ := ih _ remaining
      exact ⟨candidate, by simpa [weightedChoice, inside] using selected⟩

/-- Trial logs retain the actual size passed to the draw, not just its policy. -/
def scheduledSamples (draw : Seed → Nat → Value × Seed) (policy : Nat → Nat) :
    Nat → Nat → Seed → List (Nat × Value)
  | 0, _, _ => []
  | count + 1, trial, seed =>
    let size := policy trial
    let (value, next) := draw seed size
    (size, value) :: scheduledSamples draw policy count (trial + 1) next

/-- Scheduling changes sizes without silently changing the accepted trial count. -/
theorem scheduledSamples_length (draw : Seed → Nat → Value × Seed) (policy : Nat → Nat)
    (count trial : Nat) (seed : Seed) : (scheduledSamples draw policy count trial seed).length = count := by
  induction count generalizing trial seed with
  | zero => rfl
  | succ count ih => simp [scheduledSamples, ih]

/-- Every logged size has a trial owner inside this run's finite range. -/
theorem scheduledSamples_size (draw : Seed → Nat → Value × Seed) (policy : Nat → Nat)
    (count trial size : Nat) (seed : Seed) (value : Value)
    (member : (size, value) ∈ scheduledSamples draw policy count trial seed) :
    ∃ owner, trial ≤ owner ∧ owner < trial + count ∧ size = policy owner := by
  induction count generalizing trial seed with
  | zero => simp [scheduledSamples] at member
  | succ count ih =>
    simp only [scheduledSamples, List.mem_cons] at member
    rcases member with first | later
    · have sizeEq := congrArg Prod.fst first
      exact ⟨trial, Nat.le_refl _, by omega, sizeEq⟩
    · obtain ⟨owner, lower, upper, sizeEq⟩ := ih _ _ later
      exact ⟨owner, by omega, by omega, sizeEq⟩

/-- Controlled delayed construction spends a token before each pure step. -/
def resolveDelayed (step : State → Sum Value State) : Nat → State → Option Value × Nat
  | 0, _ => (none, 0)
  | fuel + 1, state => match step state with
    | .inl value => (some value, 1)
    | .inr next =>
      let result := resolveDelayed step fuel next
      (result.1, result.2 + 1)

/-- Even a cyclic constructor cannot spend more than its force allowance. -/
theorem resolveDelayed_budget (step : State → Sum Value State) (fuel : Nat) (state : State) :
    (resolveDelayed step fuel state).2 ≤ fuel := by
  induction fuel generalizing state with
  | zero => simp [resolveDelayed]
  | succ fuel ih =>
    cases chosen : step state with
    | inl value => simp [resolveDelayed, chosen]
    | inr next => simpa [resolveDelayed, chosen] using Nat.succ_le_succ (ih next)

/-- Zero allowance does not observe the delayed callback. -/
theorem resolveDelayed_zero (step : State → Sum Value State) (state : State) :
    resolveDelayed step 0 state = (none, 0) := rfl

/-- A pruned child carries no value and must not invoke selectors/properties. -/
inductive SampleProposal (Value : Type) where
  | value : Value → SampleProposal Value
  | pruned : SampleProposal Value

/-- Both value and pruned proposals spend a token from the same shrink budget. -/
def shrinkProposals (valid fails : Value → Bool) (measure : Value → Nat) :
    Nat → Value → List (SampleProposal Value) → Value × Nat
  | 0, best, _ => (best, 0)
  | _ + 1, best, [] => (best, 0)
  | fuel + 1, best, proposal :: rest =>
    let next := match proposal with
      | .pruned => best
      | .value candidate => if admissible valid fails measure best candidate then candidate else best
    let result := shrinkProposals valid fails measure fuel next rest
    (result.1, result.2 + 1)

/-- Rejected filter proposals cannot evade the consumer's finite attempt quota. -/
theorem shrinkProposals_budget (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best : Value) (proposals : List (SampleProposal Value)) :
    (shrinkProposals valid fails measure fuel best proposals).2 ≤ fuel := by
  induction fuel generalizing best proposals with
  | zero => simp [shrinkProposals]
  | succ fuel ih =>
    cases proposals with
    | nil => simp [shrinkProposals]
    | cons proposal rest =>
      simpa only [shrinkProposals] using Nat.succ_le_succ (ih _ rest)

/-- Pruning and exhaustion retain the last admitted valid false witness. -/
theorem shrinkProposals_preserves (valid fails : Value → Bool) (measure : Value → Nat)
    (fuel : Nat) (best : Value) (proposals : List (SampleProposal Value))
    (domain : valid best = true) (failure : fails best = true) :
    let result := (shrinkProposals valid fails measure fuel best proposals).1
    valid result = true ∧ fails result = true ∧ measure result ≤ measure best := by
  induction fuel generalizing best proposals with
  | zero => exact ⟨domain, failure, Nat.le_refl _⟩
  | succ fuel ih =>
    cases proposals with
    | nil => exact ⟨domain, failure, Nat.le_refl _⟩
    | cons proposal rest =>
      cases proposal with
      | pruned => simpa only [shrinkProposals] using ih best rest domain failure
      | value candidate =>
        simp only [shrinkProposals]
        split
        next accepted =>
          obtain ⟨v, smaller, f⟩ := admissible_sound valid fails measure best candidate accepted
          obtain ⟨rv, rf, bounded⟩ := ih candidate rest v f
          exact ⟨rv, rf, Nat.le_trans bounded (Nat.le_of_lt smaller)⟩
        next refused => exact ih best rest domain failure

/-- Reference regeneration expands the same child seed for every visited parent.
Each child receives an independent initial state and may fail explicitly. -/
def regenerateSeed (expand : Seed → State) (run : Input → State → Except Error (Value × State))
    (seed : Seed) : List Input → Except Error (List (Value × State))
  | [] => .ok []
  | input :: rest => do
    let result ← run input (expand seed)
    let later ← regenerateSeed expand run seed rest
    pure (result :: later)

/-- Checkpoint replay restores a fresh source state for every child; it never
threads an earlier child's consumed state into a sibling. -/
def regenerateCheckpoint (restore : State → State)
    (run : Input → State → Except Error (Value × State)) (checkpoint : State) :
    List Input → Except Error (List (Value × State))
  | [] => .ok []
  | input :: rest => do
    let result ← run input (restore checkpoint)
    let later ← regenerateCheckpoint restore run checkpoint rest
    pure (result :: later)

/-- Under the standard state-restore law, checkpoint reuse preserves every
returned value, consumed state and first failure, even for variable-length draws.
The restore law is an explicit host obligation, exercised by Scheme regression. -/
theorem regenerateCheckpoint_eq (expand : Seed → State) (restore : State → State)
    (run : Input → State → Except Error (Value × State)) (seed : Seed) (checkpoint : State)
    (restored : restore checkpoint = expand seed) (inputs : List Input) :
    regenerateCheckpoint restore run checkpoint inputs = regenerateSeed expand run seed inputs := by
  induction inputs with
  | nil => rfl
  | cons input rest ih => simp [regenerateCheckpoint, regenerateSeed, restored, ih]

/-- A checkpoint table stores deterministic initial states, never consumed sources. -/
def cachedSeedState (expand : Seed → State) (cache : Seed → Option State) (seed : Seed) : State :=
  match cache seed with
  | some state => state
  | none => expand seed

/-- Reusing preparation is sound only while every entry names its own seed state. -/
theorem cachedSeedState_eq (expand : Seed → State) (cache : Seed → Option State)
    (sound : ∀ seed state, cache seed = some state → state = expand seed) (seed : Seed) :
    cachedSeedState expand cache seed = expand seed := by
  cases found : cache seed with
  | none => simp [cachedSeedState, found]
  | some state => simpa [cachedSeedState, found] using sound seed state found

/-- Inserting a newly expanded checkpoint preserves the seed/state invariant. -/
theorem cachedSeedState_insert_sound [DecidableEq Seed] (expand : Seed → State)
    (cache : Seed → Option State)
    (sound : ∀ seed state, cache seed = some state → state = expand seed) (seed : Seed) :
    ∀ key state, (if key = seed then some (expand seed) else cache key) = some state →
      state = expand key := by
  intro key state found
  by_cases same : key = seed
  · subst key
    simpa using (Option.some.inj (by simpa using found)).symm
  · exact sound key state (by simpa [same] using found)

/-- Repeated branch visits require at most one seed expansion per owned bind.
This is an operation-count bound, not a GC or elapsed-time theorem. -/
def checkpointExpansions (visits : Nat) : Nat := if visits = 0 then 0 else 1

/-- Zero visits do no work; every positive visit count admits one shared expansion. -/
theorem checkpointExpansions_le (visits : Nat) : checkpointExpansions visits ≤ visits := by
  unfold checkpointExpansions
  split <;> omega

/-- Delete a contiguous block while retaining the actual elements on both sides. -/
def deleteBlock (values : List Value) (start width : Nat) : List Value :=
  values.take start ++ values.drop (start + width)

/-- A bounded block deletion has the exact structural cost decrease. -/
theorem deleteBlock_length (values : List Value) (start width : Nat)
    (within : start + width ≤ values.length) :
    (deleteBlock values start width).length + width = values.length := by
  simp only [deleteBlock, List.length_append, List.length_take, List.length_drop]
  omega

/-- Minimum lengths and strict descent hold for every emitted nonempty block. -/
theorem deleteBlock_bounds (values : List Value) (start width minimum : Nat)
    (within : start + width ≤ values.length) (positive : 0 < width)
    (allowed : width ≤ values.length - minimum) (inhabited : minimum ≤ values.length) :
    minimum ≤ (deleteBlock values start width).length ∧
      (deleteBlock values start width).length < values.length := by
  have := deleteBlock_length values start width within
  omega

/-- Structural deletion introduces no new elements and preserves their order. -/
theorem deleteBlock_sublist (values : List Value) (start width : Nat) :
    (deleteBlock values start width).Sublist values := by
  unfold deleteBlock
  have suffix := List.drop_sublist width (values.drop start)
  simpa only [List.drop_drop, List.take_append_drop] using
    (List.Sublist.refl (values.take start)).append suffix

/-- Applying deletion to retained preimages commutes with mapping a carrier. -/
theorem deleteBlock_map (values : List Value) (pack : Value → Other) (start width : Nat) :
    deleteBlock (values.map pack) start width = (deleteBlock values start width).map pack := by
  simp [deleteBlock, List.map_take, List.map_drop]

/-- A deleted branch's historical observers remain part of descendant ownership. -/
theorem retainedSources_keep_deleted [DecidableEq Source] (original retained : List Source)
    (source : Source) (observed : source ∈ original) : source ∈ mergeSources original retained := by
  exact (mergeSources_mem source original retained).2 (Or.inl observed)

/-- A replay stage checks provenance before a callback, preserves its exception,
and checks provenance again after a normal return. `none` means stale;
`some cause` retains the application exception. Observers and callbacks are
assumed terminating. This finite model makes no host port-rollback claim. -/
def replayStage (before after : Bool) (action : Unit → Except Cause Value) :
    Except (Option Cause) Value :=
  if before then
    match action () with
    | .error cause => .error (some cause)
    | .ok value => if after then .ok value else .error none
  else .error none

/-- Refusal before the callback does not depend on its result. -/
theorem replayStage_preflight (after : Bool) (action : Unit → Except Cause Value) :
    replayStage false after action = .error none := rfl

/-- A callback exception survives a later provenance change with the same cause. -/
theorem replayStage_cause (after : Bool) (cause : Cause) :
    replayStage true after (fun _ => (.error cause : Except Cause Value)) =
      .error (some cause) := rfl

/-- A normally returning encoder or decoder cannot authorize stale data. -/
theorem replayStage_stale (value : Value) :
    replayStage true false (fun _ => (.ok value : Except Cause Value)) = .error none := rfl

/-- Source-current preparation preserves the exact returned value. -/
theorem replayStage_current (value : Value) :
    replayStage true true (fun _ => (.ok value : Except Cause Value)) = .ok value := rfl

/-- Preparation refusal skips the delivery/property continuation. Delivery here
is an abstract action, not a transaction over an operating-system port. -/
theorem replayStage_refused_before_delivery (before after : Bool)
    (prepare : Unit → Except Cause Value)
    (deliver : Value → Except (Option Cause) Other) (cause : Option Cause)
    (refused : replayStage before after prepare = .error cause) :
    (replayStage before after prepare >>= deliver) = .error cause := by
  rw [refused]
  rfl

end LeanPoo.Functional.PropertyTesting
