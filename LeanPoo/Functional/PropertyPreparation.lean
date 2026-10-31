import LeanPoo.Functional.PropertyScopes

/-! Checked owned-tree preparation and raw fallback. Live is a pure predicate over
captured owner epochs; callbacks obey the existing core interaction protocol.
Host dynamic-scope fidelity and terminating metadata callbacks remain premises. -/
namespace LeanPoo.Functional.PropertyTesting

/-- An owned factory may supply a tree or decline. Both paths keep the same
snapshot; declining does not authorize a raw binder after source invalidation. -/
def prepareBridge (live : State → Bool)
    (factory : State → Except Cause (Option Value × State))
    (fallback : State → Except Cause (Value × State)) (state : State) :
    Except (Option Cause) (Value × State) :=
  match guardedGeneration live factory state with
  | .error cause => .error cause
  | .ok (none, next) => guardedGeneration live fallback next
  | .ok (some value, next) => .ok (value, next)

/-- Stale authority skips the factory as well as every fallback binding. -/
theorem prepareBridge_stale (live : State → Bool)
    (factory : State → Except Cause (Option Value × State))
    (fallback : State → Except Cause (Value × State)) (state : State)
    (stale : live state = false) : prepareBridge live factory fallback state = .error none := by
  simp [prepareBridge, guardedGeneration_preflight live factory state stale]

/-- Any normal factory result, including opt-out, refuses when it retires owners. -/
theorem prepareBridge_revised (live : State → Bool) (state next : State) (candidate : Option Value)
    (fallback : State → Except Cause (Value × State))
    (before : live state = true) (after : live next = false) :
    prepareBridge live (fun _ => .ok (candidate, next)) fallback state = .error none := by
  simp [prepareBridge, guardedGeneration_revised live state next candidate before after]

/-- Original factory errors remain exact, without invoking later binders. -/
theorem prepareBridge_cause (live : State → Bool) (state : State) (cause : Cause)
    (fallback : State → Except Cause (Value × State)) (before : live state = true) :
    prepareBridge live (fun _ => .error cause) fallback state = .error (some cause) := by
  simp [prepareBridge, guardedGeneration_cause live state cause before]

/-- A valid owned tree, even with false data, never forces the raw fallback. -/
theorem prepareBridge_owned (live : State → Bool) (state next : State) (value : Value)
    (fallback : State → Except Cause (Value × State))
    (before : live state = true) (after : live next = true) :
    prepareBridge live (fun _ => .ok (some value, next)) fallback state = .ok (value, next) := by
  simp [prepareBridge, guardedGeneration_state live state next (some value) before after]

/-- Stable opt-out delegates once to the existing raw path at the returned state. -/
theorem prepareBridge_fallback (live : State → Bool) (state next : State)
    (fallback : State → Except Cause (Value × State))
    (before : live state = true) (after : live next = true) :
    prepareBridge live (fun _ => .ok (none, next)) fallback state = guardedGeneration live fallback next := by
  simp [prepareBridge, guardedGeneration_state live state next (none : Option Value) before after]

/-- Raw binding cannot publish after revising the same captured authority. -/
theorem prepareBridge_fallback_revised (live : State → Bool) (state next final : State) (value : Value)
    (before : live state = true) (middle : live next = true) (after : live final = false) :
    prepareBridge (Cause := Cause) live (fun _ => .ok (none, next))
      (fun _ => .ok (value, final)) state = .error none := by
  rw [prepareBridge_fallback live state next _ before middle]
  exact guardedGeneration_revised live next final value middle after

/-- Raw errors retain their original cause after a valid opt-out. -/
theorem prepareBridge_fallback_cause (live : State → Bool) (state next : State) (cause : Cause)
    (before : live state = true) (middle : live next = true) :
    prepareBridge (Value := Value) live (fun _ => .ok (none, next))
      (fun _ => .error cause) state = .error (some cause) := by
  rw [prepareBridge_fallback live state next _ before middle]
  exact guardedGeneration_cause live next cause middle

/-- A getter that retires owners skips later factories/domain metadata entirely. -/
theorem preparation_tail_refused (live : State → Bool) (state next : State) (metadata : Value)
    (rest : List (State → Except Cause (Value × State)))
    (before : live state = true) (after : live next = false) :
    guardedStages live ((fun _ => .ok (metadata, next)) :: rest) state = .error none :=
  guardedStages_revised live state next metadata rest before after

end LeanPoo.Functional.PropertyTesting
