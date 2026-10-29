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

end LeanPoo.Functional.PropertyTesting
