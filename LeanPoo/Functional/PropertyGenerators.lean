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

/-- Admission consumes one guarded Boolean judgment. A false judgment is a
concrete-witness refusal; a stale/error judgment retains its distinct cause. -/
def admitWitness (judgment : Except (Option Cause) Bool) (invalid : Cause)
    (next : Unit → Except (Option Cause) Value) : Except (Option Cause) Value :=
  match judgment with
  | .error cause => .error cause
  | .ok false => .error (some invalid)
  | .ok true => next ()

/-- Concrete replay shares precondition/domain/property admission and does not
perform generation, shrinking or trial classification. Each callback may be
wrapped in `replayStage`; callbacks and source observers must terminate. -/
def checkWitness (eligible domain evaluate : Unit → Except (Option Cause) Bool)
    (invalid : Cause) : Except (Option Cause) Bool :=
  admitWitness (eligible ()) invalid (fun _ => admitWitness (domain ()) invalid evaluate)

/-- An excluded value cannot enter domain recognition or the property fixture. -/
theorem checkWitness_ineligible (domain evaluate : Unit → Except (Option Cause) Bool)
    (invalid : Cause) : checkWitness (fun _ => .ok false) domain evaluate invalid =
      .error (some invalid) := rfl

/-- A domain refusal cannot execute the property. -/
theorem checkWitness_outside (evaluate : Unit → Except (Option Cause) Bool) (invalid : Cause) :
    checkWitness (fun _ => .ok true) (fun _ => .ok false) evaluate invalid =
      .error (some invalid) := rfl

/-- A changed source in precondition evaluation skips every later callback. -/
theorem checkWitness_stale (domain evaluate : Unit → Except (Option Cause) Bool)
    (invalid : Cause) : checkWitness (fun _ => .error none) domain evaluate invalid =
      .error none := rfl

/-- An application exception in domain evaluation retains its exact cause. -/
theorem checkWitness_cause (evaluate : Unit → Except (Option Cause) Bool)
    (invalid cause : Cause) : checkWitness (fun _ => .ok true)
      (fun _ => .error (some cause)) evaluate invalid = .error (some cause) := rfl

/-- Admitted concrete replay returns the property's Boolean directly, without
any generation coverage threshold turning that result into a run status. -/
theorem checkWitness_admitted (evaluate : Unit → Except (Option Cause) Bool) (invalid : Cause) :
    checkWitness (fun _ => .ok true) (fun _ => .ok true) evaluate invalid = evaluate () := rfl

/-- A generator callback returns its value and resulting source/random state.
A failed stage preserves its original cause; freshness is checked before use
and after a normal return. No rollback of already executed host effects is claimed. -/
def guardedGeneration (live : State → Bool) (run : State → Except Cause (Value × State))
    (state : State) : Except (Option Cause) (Value × State) :=
  if live state then
    match run state with
    | .error cause => .error (some cause)
    | .ok result => if live result.2 then .ok result else .error none
  else .error none

/-- An already stale producer does not evaluate its callback. -/
theorem guardedGeneration_preflight (live : State → Bool)
    (run : State → Except Cause (Value × State)) (state : State) (stale : live state = false) :
    guardedGeneration live run state = .error none := by simp [guardedGeneration, stale]

/-- A callback that revises its sources cannot deliver a value to a selector. -/
theorem guardedGeneration_revised (live : State → Bool) (state next : State) (value : Value)
    (before : live state = true) (after : live next = false) :
    guardedGeneration live (fun _ => (.ok (value, next) : Except Cause (Value × State))) state =
      .error none := by simp [guardedGeneration, before, after]

/-- Exceptions keep their cause even if later source checks would fail. -/
theorem guardedGeneration_cause (live : State → Bool) (state : State) (cause : Cause)
    (before : live state = true) :
    guardedGeneration live (fun _ => (.error cause : Except Cause (Value × State))) state =
      .error (some cause) := by simp [guardedGeneration, before]

/-- Successful admission changes neither the callback value nor its resulting
state, including a captured child seed. It does not make any claim of PRNG quality. -/
theorem guardedGeneration_state (live : State → Bool) (state next : State) (value : Value)
    (before : live state = true) (after : live next = true) :
    guardedGeneration live (fun _ => (.ok (value, next) : Except Cause (Value × State))) state =
      .ok (value, next) := by simp [guardedGeneration, before, after]

/-- Refusing an intermediate stage skips all dependent selection/drawing. -/
theorem guardedGeneration_refused (live : State → Bool)
    (run : State → Except Cause (Value × State)) (state : State)
    (next : Value × State → Except (Option Cause) Other) (cause : Option Cause)
    (refused : guardedGeneration live run state = .error cause) :
    (guardedGeneration live run state >>= next) = .error cause := by rw [refused]; rfl

/-- Finite hash generation considers each declared key once and caps the retained
subset by size. Ordering is the key-domain order, not host hash iteration order. -/
def selectedHashKeys (keys : List Key) (choose : Key → Bool) (size : Nat) : List Key :=
  (keys.filter choose).take size

/-- Selection introduces no key and preserves the declared relative order. -/
theorem selectedHashKeys_sublist (keys : List Key) (choose : Key → Bool) (size : Nat) :
    (selectedHashKeys keys choose size).Sublist keys :=
  (List.take_sublist size _).trans List.filter_sublist

/-- Both size and the admitted finite domain bound the number of value draws. -/
theorem selectedHashKeys_bounds (keys : List Key) (choose : Key → Bool) (size : Nat) :
    (selectedHashKeys keys choose size).length ≤ size ∧
      (selectedHashKeys keys choose size).length ≤ keys.length := by
  constructor
  · simpa [selectedHashKeys, List.length_take] using Nat.min_le_left size ((keys.filter choose).length)
  · exact (selectedHashKeys_sublist keys choose size).length_le

/-- Duplicate-free domain admission makes packing collision-free without
repeating duplicate searches on every structural/value shrink. -/
theorem selectedHashKeys_nodup (keys : List Key) (choose : Key → Bool) (size : Nat)
    (unique : keys.Nodup) : (selectedHashKeys keys choose size).Nodup :=
  (selectedHashKeys_sublist keys choose size).nodup unique

/-- The finite association model packs one sampled value per retained key.
Host HashTable equality/hash compatibility and stable keys are explicit premises. -/
def hashEntries (keys : List Key) (value : Key → Value) : List (Key × Value) :=
  keys.map (fun key => (key, value key))

/-- Finite lookup preserves present false-like values rather than using them as
absence. Correspondence to Gerbil's HashTable protocol is a host obligation. -/
theorem hashEntries_lookup [DecidableEq Key] (keys : List Key) (value : Key → Value) (key : Key) :
    lookupFunction (hashEntries keys value) key = if key ∈ keys then some (value key) else none := by
  induction keys with
  | nil => simp [hashEntries, lookupFunction]
  | cons head rest ih =>
    by_cases same : key = head
    · subst head; simp [hashEntries, lookupFunction]
    · simpa [hashEntries, lookupFunction, same] using ih

/-- Structural shrinking retains the exact remaining key/value pairs. -/
theorem hashEntries_delete (keys : List Key) (value : Key → Value) (start width : Nat) :
    deleteBlock (hashEntries keys value) start width = hashEntries (deleteBlock keys start width) value := by
  exact deleteBlock_map keys (fun key => (key, value key)) start width

/-- Value transformation changes no key; validated Function wrappers use this
same representation law under their own validation/observation premises. -/
theorem hashEntries_map (keys : List Key) (value : Key → Value) (transform : Value → Other) :
    (hashEntries keys value).map (fun entry => (entry.1, transform entry.2)) =
      hashEntries keys (fun key => transform (value key)) := by simp [hashEntries, List.map_map]

/-- Finite enumeration keeps declaration positions as the generator preimage. -/
def enumChoice (domain : List Value) (index : Nat) : Option Value := domain[index]?

/-- A declared simplification rank uses the first equal occurrence, as Enum does. -/
def enumRank [BEq Value] (domain : List Value) (value : Value) : Nat := domain.idxOf value

/-- Every successfully selected position stays inside the finite domain. -/
theorem enumChoice_member (domain : List Value) (index : Nat) (value : Value)
    (selected : enumChoice domain index = some value) : value ∈ domain :=
  List.mem_of_getElem? selected

/-- Invalid positions refuse rather than inventing a fallback value. -/
theorem enumChoice_outside (domain : List Value) (index : Nat)
    (outside : domain.length ≤ index) : enumChoice domain index = none := by
  simp [enumChoice, List.getElem?_eq_none outside]

/-- Equal duplicates can only lower the canonical rank of a selected position. -/
theorem enumRank_le_index [BEq Value] [LawfulBEq Value]
    (domain : List Value) (index : Nat) (value : Value)
    (selected : enumChoice domain index = some value) : enumRank domain value ≤ index := by
  induction domain generalizing index with
  | nil => simp [enumChoice] at selected
  | cons head tail ih =>
    cases index with
    | zero =>
      have same : head = value := by simpa [enumChoice] using selected
      subst value
      simp [enumRank]
    | succ index =>
      have tailSelected : enumChoice tail index = some value := by
        simpa [enumChoice] using selected
      have lower := ih index tailSelected
      simp only [enumRank, List.idxOf_cons]
      split <;> simp only [enumRank] at lower <;> omega

/-- Selecting any earlier position strictly lowers the first-occurrence rank,
even when the declaration contains equal duplicate payloads. -/
theorem enumRank_descent [BEq Value] [LawfulBEq Value]
    (domain : List Value) (best candidate : Value) (index : Nat)
    (earlier : index < enumRank domain best)
    (selected : enumChoice domain index = some candidate) :
    candidate ∈ domain ∧ enumRank domain candidate < enumRank domain best := by
  exact ⟨enumChoice_member domain index candidate selected,
    Nat.lt_of_le_of_lt (enumRank_le_index domain index candidate selected) earlier⟩

/-- Dependency repair after a retained block deletion uses the same retirement. -/
def repairedBlock (model : TraceModel State Command Reply) (state : State)
    (commands : List Command) (start width : Nat) : List Command :=
  retire model state (deleteBlock commands start width)

/-- Block retirement cannot introduce or reorder retained command identities. -/
theorem repairedBlock_sublist (model : TraceModel State Command Reply) (state : State)
    (commands : List Command) (start width : Nat) :
    (repairedBlock model state commands start width).Sublist commands :=
  (retire_sublist model _ state).trans (deleteBlock_sublist commands start width)

/-- Every retained block proposal satisfies all state-dependent preconditions. -/
theorem repairedBlock_valid (model : TraceModel State Command Reply) (state : State)
    (commands : List Command) (start width : Nat) :
    traceValid model state (repairedBlock model state commands start width) = true :=
  retire_valid model _ state

/-- Repair may retire more commands, but cannot undo a block's length decrease. -/
theorem repairedBlock_length (model : TraceModel State Command Reply) (state : State)
    (commands : List Command) (start width : Nat) (within : start + width ≤ commands.length) :
    (repairedBlock model state commands start width).length + width ≤ commands.length := by
  have repaired := (retire_sublist model (deleteBlock commands start width) state).length_le
  have deleted := deleteBlock_length commands start width within
  change (retire model state (deleteBlock commands start width)).length + width ≤ commands.length
  omega

/-- Every command has positive structural cost, independently of parameter weight. -/
theorem traceWeight_length (weight : Command → Nat) (commands : List Command) :
    commands.length ≤ traceWeight weight commands := by
  induction commands with
  | nil => simp [traceWeight]
  | cons head tail ih => simp only [List.length_cons, traceWeight]; omega

/-- Nonempty block deletion and dependency retirement strictly lower total cost. -/
theorem repairedBlock_smaller (model : TraceModel State Command Reply) (state : State)
    (weight : Command → Nat) (commands : List Command) (start width : Nat)
    (within : start + width ≤ commands.length) (positive : 0 < width) :
    traceWeight weight (repairedBlock model state commands start width) < traceWeight weight commands := by
  apply retire_smaller
  have first := congrArg (traceWeight weight) (List.take_append_drop start commands)
  have second := congrArg (traceWeight weight) (List.take_append_drop width (commands.drop start))
  simp only [traceWeight_append] at first second
  have middle := traceWeight_length weight ((commands.drop start).take width)
  have length : ((commands.drop start).take width).length = width := by
    simp only [List.length_take, List.length_drop]
    omega
  simp only [deleteBlock, traceWeight_append]
  simp only [List.drop_drop] at second
  omega

/-- Ordered product callbacks reuse the same before/after source boundary.
A refused stage never evaluates any callback in the remaining product. -/
def guardedStages (live : State → Bool) :
    List (State → Except Cause (Value × State)) → State → Except (Option Cause) (List Value × State)
  | [], state => .ok ([], state)
  | run :: rest, state =>
      match guardedGeneration live run state with
      | .error cause => .error cause
      | .ok (value, next) => match guardedStages live rest next with
        | .error cause => .error cause
        | .ok (values, final) => .ok (value :: values, final)

/-- A normal return that invalidates any captured field source stops the product. -/
theorem guardedStages_revised (live : State → Bool) (state next : State) (value : Value)
    (rest : List (State → Except Cause (Value × State)))
    (before : live state = true) (after : live next = false) :
    guardedStages live ((fun _ => .ok (value, next)) :: rest) state = .error none := by
  simp [guardedStages, guardedGeneration_revised live state next value before after]

/-- A field callback's exception survives without observing or evaluating its tail. -/
theorem guardedStages_cause (live : State → Bool) (state : State) (cause : Cause)
    (rest : List (State → Except Cause (Value × State))) (before : live state = true) :
    guardedStages live ((fun _ => .error cause) :: rest) state = .error (some cause) := by
  simp [guardedStages, guardedGeneration_cause live state cause before]

/-- Refusal at an arbitrary successful prefix remains refusal after composition. -/
theorem guardedStages_prefix (live : State → Bool)
    (left right : List (State → Except Cause (Value × State))) (state : State)
    (cause : Option Cause) (refused : guardedStages live left state = .error cause) :
    guardedStages live (left ++ right) state = .error cause := by
  induction left generalizing state with
  | nil => simp [guardedStages] at refused
  | cons run rest ih =>
    cases first : guardedGeneration live run state with
    | error error => simpa [guardedStages, first] using refused
    | ok pair =>
      obtain ⟨value, next⟩ := pair
      cases tail : guardedStages live rest next with
      | ok result => simp [guardedStages, first, tail] at refused
      | error error =>
        have same : error = cause := by simpa [guardedStages, first, tail] using refused
        subst error
        simp [guardedStages, first, ih next tail]

/-- Shrinking interprets a stable exclusion as non-falsification; source refusal
is distinct and must occur before a property callback can run. -/
def guardedShrinkPolicy (live : State → Bool)
    (eligible : State → Except Cause (Bool × State))
    (evaluate : State → Except (Option Cause) (Bool × State)) (state : State) :
    Except (Option Cause) (Bool × State) :=
  match guardedGeneration live eligible state with
  | .error cause => .error cause
  | .ok (allowed, next) => if allowed then evaluate next else .ok (true, next)

/-- Both true and false policy returns refuse if their source epoch changed. -/
theorem guardedShrinkPolicy_revised (live : State → Bool) (state next : State)
    (allowed : Bool) (evaluate : State → Except (Option Cause) (Bool × State))
    (before : live state = true) (after : live next = false) :
    guardedShrinkPolicy live (fun _ => .ok (allowed, next)) evaluate state = .error none := by
  simp [guardedShrinkPolicy, guardedGeneration_revised live state next allowed before after]

/-- Stable exclusion skips the property without becoming a smaller false witness. -/
theorem guardedShrinkPolicy_excluded (live : State → Bool) (state next : State)
    (evaluate : State → Except (Option Cause) (Bool × State))
    (before : live state = true) (after : live next = true) :
    guardedShrinkPolicy live (fun _ => .ok (false, next)) evaluate state = .ok (true, next) := by
  simp [guardedShrinkPolicy, guardedGeneration_state live state next false before after]

/-- Stable admission leaves the property result and its original cause unchanged. -/
theorem guardedShrinkPolicy_admitted (live : State → Bool) (state next : State)
    (evaluate : State → Except (Option Cause) (Bool × State))
    (before : live state = true) (after : live next = true) :
    guardedShrinkPolicy live (fun _ => .ok (true, next)) evaluate state = evaluate next := by
  simp [guardedShrinkPolicy, guardedGeneration_state live state next true before after]

/-- A policy exception cannot be reinterpreted as exclusion or falsification. -/
theorem guardedShrinkPolicy_cause (live : State → Bool) (state : State) (cause : Cause)
    (evaluate : State → Except (Option Cause) (Bool × State)) (before : live state = true) :
    guardedShrinkPolicy live (fun _ => .error cause) evaluate state = .error (some cause) := by
  simp [guardedShrinkPolicy, guardedGeneration_cause live state cause before]

/-- Portable handoff has distinct confirmation, encoding and delivery stages.
Source state includes the codec and application epochs. Delivery is an abstract
port action: its effects are not rolled back if its trailing check refuses. -/
def guardedHandoff (live : State → Bool)
    (confirm : State → Except Cause (Unit × State))
    (encode : State → Except Cause (Payload × State))
    (deliver : Payload → State → Except Cause (Output × State)) (state : State) :
    Except (Option Cause) (Output × State) :=
  match guardedGeneration live confirm state with
  | .error cause => .error cause
  | .ok (_, confirmed) => match guardedGeneration live encode confirmed with
    | .error cause => .error cause
    | .ok (payload, encoded) => guardedGeneration live (deliver payload) encoded

/-- A stale preflight invokes no confirmation, encoder or port action. -/
theorem guardedHandoff_preflight (live : State → Bool)
    (confirm : State → Except Cause (Unit × State))
    (encode : State → Except Cause (Payload × State))
    (deliver : Payload → State → Except Cause (Output × State)) (state : State)
    (stale : live state = false) : guardedHandoff live confirm encode deliver state = .error none := by
  simp [guardedHandoff, guardedGeneration_preflight live confirm state stale]

/-- Reconfirmation may change codec metadata without changing the witness domain;
its trailing refusal must skip the encoder and every port effect. -/
theorem guardedHandoff_confirm_revised (live : State → Bool) (state next : State)
    (encode : State → Except Cause (Payload × State))
    (deliver : Payload → State → Except Cause (Output × State))
    (before : live state = true) (after : live next = false) :
    guardedHandoff live (fun _ => .ok ((), next)) encode deliver state = .error none := by
  simp [guardedHandoff, guardedGeneration_revised live state next () before after]

/-- Confirmation errors retain their own cause even when later sources are stale. -/
theorem guardedHandoff_confirm_cause (live : State → Bool) (state : State) (cause : Cause)
    (encode : State → Except Cause (Payload × State))
    (deliver : Payload → State → Except Cause (Output × State)) (before : live state = true) :
    guardedHandoff live (fun _ => .error cause) encode deliver state = .error (some cause) := by
  simp [guardedHandoff, guardedGeneration_cause live state cause before]

/-- A normally returning stale encoder cannot authorize delivery. -/
theorem guardedHandoff_encode_revised (live : State → Bool) (state next : State) (payload : Payload)
    (deliver : Payload → State → Except Cause (Output × State))
    (before : live state = true) (after : live next = false) :
    guardedHandoff live (fun _ => .ok ((), state)) (fun _ => .ok (payload, next)) deliver state =
      .error none := by
  simp [guardedHandoff, guardedGeneration_state live state state () before before,
    guardedGeneration_revised live state next payload before after]

/-- An encoding exception remains the original cause, without delivery. -/
theorem guardedHandoff_encode_cause (live : State → Bool) (state : State) (cause : Cause)
    (deliver : Payload → State → Except Cause (Output × State)) (before : live state = true) :
    guardedHandoff live (fun _ => .ok ((), state)) (fun _ => .error cause) deliver state =
      .error (some cause) := by
  simp [guardedHandoff, guardedGeneration_state live state state () before before,
    guardedGeneration_cause live state cause before]

/-- Stable preparation hands the exact payload to the unchanged guarded port action. -/
theorem guardedHandoff_delivery (live : State → Bool) (state confirmed encoded : State)
    (payload : Payload) (deliver : Payload → State → Except Cause (Output × State))
    (before : live state = true) (checked : live confirmed = true) (prepared : live encoded = true) :
    guardedHandoff live (fun _ => .ok ((), confirmed)) (fun _ => .ok (payload, encoded)) deliver state =
      guardedGeneration live (deliver payload) encoded := by
  simp [guardedHandoff, guardedGeneration_state live state confirmed () before checked,
    guardedGeneration_state live confirmed encoded payload checked prepared]

/-- A port exception is preserved after successful confirmation and encoding.
The host may already have emitted a prefix: this is not a rollback theorem. -/
theorem guardedHandoff_delivery_cause (live : State → Bool) (state : State)
    (payload : Payload) (cause : Cause) (before : live state = true) :
    guardedHandoff live (fun _ => .ok ((), state)) (fun _ => .ok (payload, state))
      (fun _ _ => (.error cause : Except Cause (Output × State))) state = .error (some cause) := by
  simp [guardedHandoff_delivery live state state state payload _ before before before,
    guardedGeneration_cause live state cause before]

/-- Rebuilt dependent nodes keep the old origin plus newly inspected parent/child leaves. -/
def rebuiltSources [DecidableEq Source] (original parent child : List Source) : List Source :=
  mergeSources (mergeSources original parent) child

/-- Rebuilding never forgets an observed source or invents a new one. -/
theorem rebuiltSources_mem [DecidableEq Source] (source : Source) (original parent child : List Source) :
    source ∈ rebuiltSources original parent child ↔
      source ∈ original ∨ source ∈ parent ∨ source ∈ child := by
  simp [rebuiltSources, mergeSources_mem, or_assoc]

/-- A fresh regenerated branch cannot compensate for an invalid old origin. -/
theorem rebuiltSources_current [DecidableEq Source] (current : Source → Bool)
    (original parent child : List Source) :
    (rebuiltSources original parent child).all current = true ↔
      original.all current = true ∧ parent.all current = true ∧ child.all current = true := by
  simp only [rebuiltSources, mergeSources_current, and_assoc]

/-- Separately retained descendants continue to refuse the original stale epoch. -/
theorem rebuiltSources_stale [DecidableEq Source] (current : Source → Bool)
    (original parent child : List Source) (stale : original.all current = false) :
    (rebuiltSources original parent child).all current = false := by
  cases outcome : (rebuiltSources original parent child).all current with
  | false => rfl
  | true =>
    have owned := (rebuiltSources_current current original parent child).mp outcome
    simp [stale] at owned

/-- One resumed standard iterator pull has the same guarded callback semantics.
`none` is EOF; returning EOF still requires a successful trailing source check. -/
def guardedPull (sources : List Source) (live : State → Source → Bool)
    (resume : State → Except Cause (Option Value × State)) (state : State) :
    Except (Option Cause) (Option Value × State) :=
  guardedGeneration (fun state => sources.all (live state)) resume state

/-- A stale paused iterator cannot resume its producer or selector effects. -/
theorem guardedPull_preflight (sources : List Source) (live : State → Source → Bool)
    (resume : State → Except Cause (Option Value × State)) (state : State)
    (stale : sources.all (live state) = false) :
    guardedPull sources live resume state = .error none := by
  exact guardedGeneration_preflight _ resume state stale

/-- A source revision during EOF cannot certify exhaustion of a shrink neighborhood. -/
theorem guardedPull_eof_revised (sources : List Source) (live : State → Source → Bool)
    (state next : State) (before : sources.all (live state) = true)
    (after : sources.all (live next) = false) :
    guardedPull sources live (fun _ => (.ok (none, next) : Except Cause (Option Value × State))) state =
      .error none := by
  exact guardedGeneration_revised _ state next none before after

/-- A pull exception keeps its exact cause rather than becoming stale EOF. -/
theorem guardedPull_cause (sources : List Source) (live : State → Source → Bool)
    (state : State) (cause : Cause) (before : sources.all (live state) = true) :
    guardedPull sources live (fun _ => (.error cause : Except Cause (Option Value × State))) state =
      .error (some cause) := by
  exact guardedGeneration_cause _ state cause before

/-- Successful guarded pulls preserve the exact yielded value or EOF and state. -/
theorem guardedPull_stable (sources : List Source) (live : State → Source → Bool)
    (state next : State) (value : Option Value) (before : sources.all (live state) = true)
    (after : sources.all (live next) = true) :
    guardedPull sources live (fun _ => (.ok (value, next) : Except Cause (Option Value × State))) state =
      .ok (value, next) := by
  exact guardedGeneration_state _ state next value before after

/-- With no owned/inherited observers the ordinary iterator loop is equivalent;
source-free fast paths never mean that a merely currently-true guard is immutable. -/
theorem guardedPull_empty (live : State → Source → Bool)
    (resume : State → Except Cause (Option Value × State)) (state : State) :
    guardedPull [] live resume state =
      match resume state with
      | .error cause => .error (some cause)
      | .ok result => .ok result := by
  unfold guardedPull guardedGeneration
  cases resume state <;> rfl

/-- An independent product proposal replaces one retained preimage. Its external
draw state is passed through unchanged; dependent regeneration remains `bind`. -/
def retainedProductStep (roots : List Value) (index : Nat) (child : Value) (state : State) :
    List Value × State := (roots.set index child, state)

/-- Coordinate shrinking cannot change the admitted fixed product width. -/
theorem retainedProductStep_length (roots : List Value) (index : Nat) (child : Value) (state : State) :
    (retainedProductStep roots index child state).1.length = roots.length := by
  simp [retainedProductStep]

/-- An in-range proposal installs exactly the chosen retained child. -/
theorem retainedProductStep_selected (roots : List Value) (index : Nat) (child : Value)
    (state : State) (within : index < roots.length) :
    (retainedProductStep roots index child state).1[index]? = some child := by
  simp [retainedProductStep, within]

/-- Every other coordinate keeps its actual preimage, not a regenerated equal value. -/
theorem retainedProductStep_sibling (roots : List Value) (index other : Nat) (child : Value)
    (state : State) (different : index ≠ other) :
    (retainedProductStep roots index child state).1[other]? = roots[other]? := by
  simp [retainedProductStep, List.getElem?_set_ne different]

/-- Carrier mapping commutes with replacing a retained coordinate. -/
theorem retainedProductStep_map (roots : List Value) (pack : Value → Other)
    (index : Nat) (child : Value) (state : State) :
    (retainedProductStep (roots.map pack) index (pack child) state).1 =
      (retainedProductStep roots index child state).1.map pack := by
  simp [retainedProductStep]

/-- Independent coordinate updates commute; neither replaces an unrelated field. -/
theorem retainedProductStep_commute (roots : List Value) (left right : Nat)
    (first second : Value) (state : State) (different : left ≠ right) :
    retainedProductStep (retainedProductStep roots left first state).1 right second state =
      retainedProductStep (retainedProductStep roots right second state).1 left first state := by
  simp only [retainedProductStep, List.set_comm first second different]

/-- Repeated observation does not draw, initialize or advance a sibling's state. -/
theorem retainedProductStep_state (roots : List Value) (index : Nat) (child : Value) (state : State) :
    (retainedProductStep roots index child state).2 = state := rfl

/-- An empty product has no coordinate to replace. -/
theorem retainedProductStep_empty (index : Nat) (child : Value) (state : State) :
    retainedProductStep [] index child state = ([], state) := by
  simp [retainedProductStep]

/-- The existing sum measure strictly decreases when the selected preimage does.
The supplied child relation remains the generator's explicit responsibility. -/
theorem retainedProductStep_descent (roots : List Value) (measure : Value → Nat)
    (index : Nat) (child : Value) (state : State) (within : index < roots.length)
    (smaller : measure child < measure roots[index]) :
    ((retainedProductStep roots index child state).1.map measure).sum < (roots.map measure).sum := by
  simp only [retainedProductStep]
  induction roots generalizing index with
  | nil => simp at within
  | cons head tail ih =>
    cases index with
    | zero => simpa using Nat.add_lt_add_right smaller (tail.map measure).sum
    | succ index =>
      have h := ih index (by simpa using within) (by simpa using smaller)
      simpa using Nat.add_lt_add_left h (measure head)

/-- Demand one supplied input by descriptor identity. Successful preparation is
reused; a missing entry invokes only that descriptor's derivation. Source guards
remain outside this finite promise model, as in `guardedGeneration`. -/
def demandInput [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) : Except Cause (Value × List (Key × Value)) :=
  match prepared.lookup key with
  | some value => .ok (value, prepared)
  | none => match derive key with
    | .error cause => .error cause
    | .ok value => .ok (value, (key, value) :: prepared)

/-- Prepare exactly the selected, supplied input row in order. Prior successful
entries survive a later refusal; no unselected or omitted Type is demanded. -/
def demandInputs [DecidableEq Key] (derive : Key → Except Cause Value)
    (inputs : List Key) (prepared : List (Key × Value)) :
    Except Cause (List Value) × List (Key × Value) :=
  match inputs with
  | [] => (.ok [], prepared)
  | key :: rest => match demandInput derive key prepared with
    | .error cause => (.error cause, prepared)
    | .ok (value, next) =>
      let (result, final) := demandInputs derive rest next
      (result.map (value :: ·), final)

/-- A dormant cached input never invokes its constructor again. -/
theorem demandInput_cached [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) (value : Value)
    (cached : prepared.lookup key = some value) :
    demandInput derive key prepared = .ok (value, prepared) := by
  simp [demandInput, cached]

/-- A selected unsupported input keeps the exact cause; no Type fallback exists. -/
theorem demandInput_error [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) (cause : Cause)
    (missing : prepared.lookup key = none) (refused : derive key = .error cause) :
    demandInput derive key prepared = .error cause := by
  simp [demandInput, missing, refused]

/-- Successful demand retains the exact generator and makes it reusable. -/
theorem demandInput_prepared [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) (value : Value)
    (missing : prepared.lookup key = none) (admitted : derive key = .ok value) :
    demandInput derive key prepared = .ok (value, (key, value) :: prepared) := by
  simp [demandInput, missing, admitted]

/-- Demand depends only on this descriptor, never another declared input's hook. -/
theorem demandInput_local [DecidableEq Key] (left right : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) (same : left key = right key) :
    demandInput left key prepared = demandInput right key prepared := by
  simp [demandInput, same]

/-- A call with no supplied fields cannot force any generator. -/
theorem demandInputs_empty [DecidableEq Key] (derive : Key → Except Cause Value)
    (prepared : List (Key × Value)) : demandInputs derive [] prepared = (.ok [], prepared) := rfl

/-- Repeated positional/optional/keyword/rest occurrences share one preparation. -/
theorem demandInputs_repeated [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (value : Value) (admitted : derive key = .ok value) :
    demandInputs derive [key, key] [] = (.ok [value, value], [(key, value)]) := by
  simp [demandInputs, demandInput, admitted, Except.map]

/-- Failure suppresses all later constructor demands and preserves earlier entries. -/
theorem demandInputs_stop [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (rest : List Key) (prepared : List (Key × Value)) (cause : Cause)
    (missing : prepared.lookup key = none) (refused : derive key = .error cause) :
    demandInputs derive (key :: rest) prepared = (.error cause, prepared) := by
  simp [demandInputs, demandInput_error derive key prepared cause missing refused]

/-- A retained successful promise can be reused without even a viable constructor. -/
theorem demandInputs_cached_single [DecidableEq Key] (derive : Key → Except Cause Value)
    (key : Key) (prepared : List (Key × Value)) (value : Value)
    (cached : prepared.lookup key = some value) :
    demandInputs derive [key] prepared = (.ok [value], prepared) := by
  simp [demandInputs, demandInput_cached derive key prepared value cached, Except.map]

end LeanPoo.Functional.PropertyTesting
