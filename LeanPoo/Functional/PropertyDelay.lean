import LeanPoo.Functional.PropertyGenerators

/-! Retained delayed-construction allowances for dependent sample regeneration.
None is an unbounded context, some zero is exhausted. Faithful host capture and per-resume transfer of the incoming numeric credits
remain explicit premises; this does not verify host continuation implementation. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Meet original and active depth allowances without renewing either one. -/
def delayMeet : Option Nat → Option Nat → Option Nat
  | none, active => active
  | retained, none => retained
  | some retained, some active => some (min retained active)

/-- A delayed constructor additionally obeys its own declared finite depth. -/
def delayCredits (limit : Nat) (retained active : Option Nat) : Nat :=
  min limit ((delayMeet retained active).getD limit)

/-- Reuse the existing force-counted interpreter under the restored allowance. -/
def restoredDelayed (step : State → Sum Value State) (limit : Nat)
    (retained active : Option Nat) (state : State) : Option Value × Nat :=
  resolveDelayed step (delayCredits limit retained active) state

/-- An unbounded original context still inherits the active caller. -/
theorem delayMeet_unbounded_left (active : Option Nat) : delayMeet none active = active := rfl

/-- Leaving the consuming scope cannot erase the allowance retained on a child. -/
theorem delayMeet_unbounded_right (retained : Option Nat) : delayMeet retained none = retained := by
  cases retained <;> rfl

/-- Both original and active constraints have equal authority. -/
theorem delayMeet_comm (retained active : Option Nat) : delayMeet retained active = delayMeet active retained := by
  cases retained <;> cases active <;> simp [delayMeet, Nat.min_comm]

/-- Nested consumption cannot change the effective allowance by regrouping. -/
theorem delayMeet_assoc (first second third : Option Nat) :
    delayMeet (delayMeet first second) third = delayMeet first (delayMeet second third) := by
  cases first <;> cases second <;> cases third <;> simp [delayMeet, Nat.min_assoc]

/-- Restoring the same allowance never spends or manufactures a credit. -/
theorem delayMeet_idem (retained : Option Nat) : delayMeet retained retained = retained := by
  cases retained <;> simp [delayMeet]

/-- A captured finite allowance bounds the next delayed constructor's credits. -/
theorem delayCredits_retained (limit retained : Nat) (active : Option Nat) :
    delayCredits limit (some retained) active ≤ retained := by
  cases active <;> simp [delayCredits, delayMeet] <;> omega

/-- A stricter active caller cannot be relaxed by a retained subtree. -/
theorem delayCredits_active (limit active : Nat) (retained : Option Nat) :
    delayCredits limit retained (some active) ≤ active := by
  rw [delayCredits, delayMeet_comm]
  exact delayCredits_retained limit active retained

/-- Even cyclic constructor transitions cannot exceed restored or declared depth. -/
theorem restoredDelayed_budget (step : State → Sum Value State) (limit : Nat)
    (retained active : Option Nat) (state : State) :
    (restoredDelayed step limit retained active state).2 ≤ delayCredits limit retained active :=
  resolveDelayed_budget step _ state

/-- Exhausted retained depth skips every constructor, after the original scope exits. -/
theorem restoredDelayed_zero (step : State → Sum Value State) (limit : Nat)
    (active : Option Nat) (state : State) :
    restoredDelayed step limit (some 0) active state = (none, 0) := by
  cases active <;> simp [restoredDelayed, delayCredits, delayMeet, resolveDelayed]

/-- With no enclosing constraints, only the constructor's declared depth applies. -/
theorem restoredDelayed_unbounded (step : State → Sum Value State) (limit : Nat) (state : State) :
    restoredDelayed step limit none none state = resolveDelayed step limit state := by
  simp [restoredDelayed, delayCredits, delayMeet]

/-- Resume a suspended dependent iterator under both saved and incoming limits.
The saved continuation may restore its dynamic limit, but cannot erase the caller. -/
def resumedDelayed (step : State → Sum Value State) (limit : Nat)
    (retained saved incoming : Option Nat) (state : State) : Option Value × Nat :=
  restoredDelayed step limit retained (delayMeet saved incoming) state

/-- Per-resume transfer is precisely the same meet as ordinary nested scopes. -/
theorem resumedDelayed_flatten (step : State → Sum Value State) (limit : Nat)
    (retained saved incoming : Option Nat) (state : State) :
    resumedDelayed step limit retained saved incoming state =
      restoredDelayed step limit (delayMeet retained saved) incoming state := by
  simp only [resumedDelayed, restoredDelayed, delayCredits, delayMeet_assoc]

/-- Restoring a looser saved continuation cannot manufacture incoming credits. -/
theorem resumedDelayed_incoming_budget (step : State → Sum Value State) (limit incoming : Nat)
    (retained saved : Option Nat) (state : State) :
    (resumedDelayed step limit retained saved (some incoming) state).2 ≤ incoming := by
  rw [resumedDelayed_flatten]
  exact Nat.le_trans (restoredDelayed_budget step limit _ _ state)
    (delayCredits_active limit incoming _)

/-- The original saved finite limit also remains authoritative after resuming. -/
theorem resumedDelayed_saved_budget (step : State → Sum Value State) (limit saved : Nat)
    (retained incoming : Option Nat) (state : State) :
    (resumedDelayed step limit retained (some saved) incoming state).2 ≤ saved := by
  rw [resumedDelayed, delayMeet_comm (some saved) incoming]
  exact resumedDelayed_incoming_budget step limit saved retained incoming state

/-- An exhausted incoming caller skips the constructor despite a saved allowance. -/
theorem resumedDelayed_zero (step : State → Sum Value State) (limit : Nat)
    (retained saved : Option Nat) (state : State) :
    resumedDelayed step limit retained saved (some 0) state = (none, 0) := by
  cases retained <;> cases saved <;>
    simp [resumedDelayed, restoredDelayed, delayCredits, delayMeet, resolveDelayed]

/-- Resuming without an additional bound preserves the original force semantics. -/
theorem resumedDelayed_unbounded (step : State → Sum Value State) (limit : Nat)
    (retained saved : Option Nat) (state : State) :
    resumedDelayed step limit retained saved none state = restoredDelayed step limit retained saved state := by
  simp [resumedDelayed, delayMeet_unbounded_right]

end LeanPoo.Functional.PropertyTesting
