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

end LeanPoo.Functional.PropertyTesting
