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
  if chosen = order then .ok order else .error "inheritance hook must preserve checked C3 order"
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
/-- Successful order admission retains the source canonical order. The host must
supply independent continuation/public spines; Lean lists are already immutable. -/
theorem checkedOrder_canonical [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (canonical : List Name)
    (accepted : hook self (fun _ => .ok canonical) = .ok canonical) :
    checkedOrder hook self (.ok canonical) = .ok canonical := by
  simp [checkedOrder, accepted, bind, Except.bind]

/-- An altered successful hook result is refused before any final cache escapes. -/
theorem checkedOrder_changed [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (canonical chosen : List Name)
    (called : hook self (fun _ => .ok canonical) = .ok chosen)
    (different : chosen ≠ canonical) :
    checkedOrder hook self (.ok canonical) =
      .error "inheritance hook must preserve checked C3 order" := by
  simp [checkedOrder, called, different, bind, Except.bind]

/-- The original hook error is propagated; repair requires a fresh invocation. -/
theorem checkedOrder_hook_error [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (canonical : List Name) (cause : String)
    (called : hook self (fun _ => .ok canonical) = .error cause) :
    checkedOrder hook self (.ok canonical) = .error cause := by
  simp [checkedOrder, called, bind, Except.bind]

/-- Only the final accepted order is retained at the observable cache boundary.
Temporary host construction state is private and cleared on every exception. -/
def cacheCheckedOrder [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (reference : Except String (List Name)) : Option (List Name) :=
  (checkedOrder hook self reference).toOption

/-- A retained cache entry must be the exact canonical C3 result. -/
theorem cacheCheckedOrder_sound [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (reference : Except String (List Name)) (order : List Name)
    (cached : cacheCheckedOrder hook self reference = some order) : reference = .ok order := by
  unfold cacheCheckedOrder at cached
  cases result : checkedOrder hook self reference with
  | error cause => simp [result, Except.toOption] at cached
  | ok chosen =>
    simp [result, Except.toOption] at cached
    subst chosen
    exact checkedOrder_sound hook self reference order result

/-- A refused hook result cannot leave a usable cache; its corrected retry may. -/
theorem cacheCheckedOrder_refused [DecidableEq Name] (hook : Hook Context (List Name))
    (self : Context) (reference : Except String (List Name)) (cause : String)
    (refused : checkedOrder hook self reference = .error cause) :
    cacheCheckedOrder hook self reference = none := by
  simp [cacheCheckedOrder, refused, Except.toOption]

end LeanPoo.Functional.InheritedMOP
