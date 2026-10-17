import LeanPoo.Functional.InheritedMOP

/-! Intercept existing inheritance operations with ordinary higher-order hooks.
This advances generalized-MOP future work. Checked C3 is retained; arbitrary
alternative linearizations and effectful callback equivalence are not inferred. -/
namespace LeanPoo.Functional.InheritedMOP

/-- A hook sees the current receiver and the inherited computation as a thunk. -/
abbrev Hook (Context Result : Type) := Context → (Unit → Except String Result) → Except String Result
/-- Reuse the inherited operation without additional behavior. -/
def identityHook : Hook Context Result := fun _ next => next ()
/-- Most-specific wrappers surround inherited wrappers without forcing their suffix. -/
def composeHooks (outer inner : Hook Context Result) : Hook Context Result :=
  fun self next => outer self (fun _ => inner self next)
/-- Grouping protocol inheritance does not change the effective hook. -/
theorem composeHooks_assoc (outer middle inner : Hook Context Result) :
    composeHooks (composeHooks outer middle) inner = composeHooks outer (composeHooks middle inner) := rfl
/-- The ordinary inherited continuation is the right identity. -/
theorem composeHooks_identity (hook : Hook Context Result) : composeHooks hook identityHook = hook := rfl
/-- Native checked C3 hooks may inspect, wrap or refuse; a different order refuses.
The source C3 error is propagated before any hook is selected. -/
def checkedOrder [DecidableEq Name] (hook : Hook Context (List Name)) (self : Context)
    (reference : Except String (List Name)) : Except String (List Name) := do
  let order ← reference
  let chosen ← hook self (fun _ => .ok order)
  if chosen = order then .ok chosen else .error "inheritance hook must preserve checked C3 order"
/-- An accepted custom hook retains the actual canonical order, not an old receipt. -/
theorem checkedOrder_sound [DecidableEq Name] (hook : Hook Context (List Name)) (self : Context)
    (reference : Except String (List Name)) (order : List Name)
    (accepted : checkedOrder hook self reference = .ok order) : reference = .ok order := by
  cases source : reference with
  | error message => simp [checkedOrder, source, bind, Except.bind] at accepted
  | ok canonical =>
    cases called : hook self (fun _ => .ok canonical) with
    | error message => simp [checkedOrder, source, called, bind, Except.bind] at accepted
    | ok chosen =>
      by_cases same : chosen = canonical
      · simp [checkedOrder, source, called, same, bind, Except.bind] at accepted
        subst chosen
        simpa [source] using congrArg (Except.ok (ε := String)) accepted
      · simp [checkedOrder, source, called, same, bind, Except.bind] at accepted
/-- C3 refusal never calls a custom order hook. -/
theorem checkedOrder_error [DecidableEq Name] (hook : Hook Context (List Name)) (self : Context) (message : String) :
    checkedOrder (Name := Name) hook self (.error message) = .error message := rfl
end LeanPoo.Functional.InheritedMOP
