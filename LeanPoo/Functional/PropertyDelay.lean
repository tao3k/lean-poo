import LeanPoo.Functional.PropertyGenerators

/-! Retained delayed-construction allowances for dependent sample regeneration.
None is an unbounded context, some zero is exhausted. Host dynamic scope and
faithful capture of these immutable credits remain explicit premises. -/
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

end LeanPoo.Functional.PropertyTesting
