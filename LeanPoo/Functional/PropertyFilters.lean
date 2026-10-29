import LeanPoo.Functional.PropertyProducts

/-! Finite rejection sampling. Draws explicitly receive the entire inherited
source directory; faithful host scope and pure observers remain premises. -/
namespace LeanPoo.Functional.PropertyTesting

/-- One retry guards drawing with its history, then guards the predicate with
both old and newly observed leaves. A rejected value still returns its owners. -/
def filterTrial [DecidableEq Source] (live : State → Source → Bool)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State))
    (owned : List Source) (state : State) :
    Except (Option Cause) ((Option Value × List Source) × State) :=
  match guardedGeneration (fun state => owned.all (live state)) (draw owned) state with
  | .error cause => .error cause
  | .ok ((value, observed), next) =>
    let visited := mergeSources owned observed
    match guardedGeneration (fun state => visited.all (live state)) (accept value) next with
    | .error cause => .error cause
    | .ok (keep, checked) => .ok ((if keep then some value else none, visited), checked)

/-- Rejection consumes one local token. The cost counts generator entries, not
inner callbacks, observer calls, host allocations, or CPU time. -/
def filterTrials [DecidableEq Source] (live : State → Source → Bool) (exhausted : Cause)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) :
    Nat → List Source → State → Except (Option Cause) (Value × State) × Nat
  | fuel, owned, state =>
    if owned.all (live state) then
      match fuel with
      | 0 => (.error (some exhausted), 0)
      | fuel + 1 => match filterTrial live draw accept owned state with
        | .error cause => (.error cause, 1)
        | .ok ((some value, _), next) => (.ok (value, next), 1)
        | .ok ((none, visited), next) =>
          let result := filterTrials live exhausted draw accept fuel visited next
          (result.1, result.2 + 1)
    else (.error none, 0)

/-- Obsolete history refuses before invoking the next draw. -/
theorem filterTrial_preflight [DecidableEq Source] (live : State → Source → Bool)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) (owned : List Source) (state : State)
    (stale : owned.all (live state) = false) : filterTrial live draw accept owned state = .error none := by
  simp [filterTrial, guardedGeneration, stale]

/-- Revision of a rejected owner during a later draw suppresses the predicate. -/
theorem filterTrial_revised [DecidableEq Source] (live : State → Source → Bool)
    (owned observed : List Source) (state next : State) (value : Value)
    (accept : Value → State → Except Cause (Bool × State))
    (before : owned.all (live state) = true) (after : owned.all (live next) = false) :
    filterTrial live (fun _ _ => .ok ((value, observed), next)) accept owned state = .error none := by
  simp [filterTrial, guardedGeneration, before, after]

/-- A draw exception remains exact and does not enter filtering or retry. -/
theorem filterTrial_cause [DecidableEq Source] (live : State → Source → Bool)
    (owned : List Source) (state : State) (cause : Cause)
    (accept : Value → State → Except Cause (Bool × State)) (before : owned.all (live state) = true) :
    filterTrial live (fun _ _ => .error cause) accept owned state = .error (some cause) := by
  simp [filterTrial, guardedGeneration, before]

/-- Stable rejection retains the union, including the original rejected epoch. -/
theorem filterTrial_reject [DecidableEq Source] (live : State → Source → Bool)
    (owned observed : List Source) (state : State) (value : Value)
    (before : owned.all (live state) = true)
    (visited : (mergeSources owned observed).all (live state) = true) :
    filterTrial (Cause := Cause) live (fun _ _ => .ok ((value, observed), state))
      (fun _ _ => .ok (false, state)) owned state = .ok ((none, mergeSources owned observed), state) := by
  simp [filterTrial, guardedGeneration, before, visited]

/-- Accepted trees retain rejected and newly observed owners as well as the
exact value; filtering cannot refresh an earlier epoch by changing branches. -/
theorem filterTrial_accept [DecidableEq Source] (live : State → Source → Bool)
    (owned observed : List Source) (state : State) (value : Value)
    (before : owned.all (live state) = true)
    (visited : (mergeSources owned observed).all (live state) = true) :
    filterTrial (Cause := Cause) live (fun _ _ => .ok ((value, observed), state))
      (fun _ _ => .ok (true, state)) owned state = .ok ((some value, mergeSources owned observed), state) := by
  simp [filterTrial, guardedGeneration, before, visited]

/-- The zero budget performs no generator entry and retains source refusal
priority over exhaustion. -/
theorem filterTrials_zero [DecidableEq Source] (live : State → Source → Bool) (exhausted : Cause)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) (owned : List Source) (state : State) :
    filterTrials live exhausted draw accept 0 owned state =
      (if owned.all (live state) then (.error (some exhausted), 0) else (.error none, 0)) := rfl

/-- A rejected attempt forwards its whole history and spends exactly one token. -/
theorem filterTrials_reject [DecidableEq Source] (live : State → Source → Bool) (exhausted : Cause)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) (owned visited : List Source)
    (state next : State) (fuel : Nat) (before : owned.all (live state) = true)
    (rejected : filterTrial live draw accept owned state = .ok ((none, visited), next)) :
    filterTrials live exhausted draw accept (fuel + 1) owned state =
      let result := filterTrials live exhausted draw accept fuel visited next
      (result.1, result.2 + 1) := by simp [filterTrials, before, rejected]

/-- Acceptance stops immediately without drawing the remaining budget. -/
theorem filterTrials_accept [DecidableEq Source] (live : State → Source → Bool) (exhausted : Cause)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) (owned visited : List Source)
    (state next : State) (fuel : Nat) (value : Value) (before : owned.all (live state) = true)
    (accepted : filterTrial live draw accept owned state = .ok ((some value, visited), next)) :
    filterTrials live exhausted draw accept (fuel + 1) owned state = (.ok (value, next), 1) := by
  simp [filterTrials, before, accepted]

/-- Generator entries are bounded by the declared local quota, even on refusal. -/
theorem filterTrials_budget [DecidableEq Source] (live : State → Source → Bool) (exhausted : Cause)
    (draw : List Source → State → Except Cause ((Value × List Source) × State))
    (accept : Value → State → Except Cause (Bool × State)) (fuel : Nat) (owned : List Source) (state : State) :
    (filterTrials live exhausted draw accept fuel owned state).2 ≤ fuel := by
  induction fuel generalizing owned state with
  | zero => simp [filterTrials]; split <;> simp
  | succ fuel ih =>
    simp only [filterTrials]
    split
    · cases trial : filterTrial live draw accept owned state with
      | error cause => simp
      | ok result =>
        rcases result with ⟨⟨value, visited⟩, next⟩
        cases value with
        | none => simpa using Nat.succ_le_succ (ih visited next)
        | some value => simp
    · simp

/-- A resumed nested pipeline inherits rejected owners too. An old epoch changed
by its first stage suppresses every following mapper/selector in that pipeline. -/
theorem filterHistory_pipeline [DecidableEq Source] (live : State → Source → Bool)
    (owned observed : List Source) (state next : State) (value : Value)
    (rest : List (State → Except Cause (Value × State)))
    (before : (mergeSources owned observed).all (live state) = true)
    (after : owned.all (live next) = false) :
    guardedStages (fun state => (mergeSources owned observed).all (live state))
      ((fun _ => .ok (value, next)) :: rest) state = .error none := by
  have obsolete : (mergeSources owned observed).all (live next) = false := by
    cases fresh : (mergeSources owned observed).all (live next) with
    | false => rfl
    | true =>
      have old := ((mergeSources_current (live next) owned observed).mp fresh).1
      simp [after] at old
  exact guardedStages_revised _ state next value rest before obsolete

end LeanPoo.Functional.PropertyTesting
