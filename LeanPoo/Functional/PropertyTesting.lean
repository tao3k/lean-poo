import LeanPoo.Functional.FunctionSignature

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

end LeanPoo.Functional.PropertyTesting
