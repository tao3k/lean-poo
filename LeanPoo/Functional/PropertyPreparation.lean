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

/-- Reader configuration feeds the existing bridge under one captured live
predicate. Options are ordinary values, never replacement authority. The resulting
value is prepared metadata; trial execution and consumer IO are outside this scope. -/
def prepareConfiguredBridge (live : State → Bool)
    (read : State → Except Cause (Options × State))
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State)) (state : State) :
    Except (Option Cause) (Value × State) :=
  match guardedGeneration live read state with
  | .error cause => .error cause
  | .ok (options, next) => prepareBridge live (factory options) (fallback options) next

/-- An obsolete request performs no configuration or bridge preparation. -/
theorem prepareConfiguredBridge_stale (live : State → Bool)
    (read : State → Except Cause (Options × State))
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State)) (state : State)
    (stale : live state = false) :
    prepareConfiguredBridge live read factory fallback state = .error none := by
  simp [prepareConfiguredBridge, guardedGeneration_preflight live read state stale]

/-- Configuring a different option value cannot refresh retired request owners. -/
theorem prepareConfiguredBridge_revised (live : State → Bool) (state next : State) (options : Options)
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State))
    (before : live state = true) (after : live next = false) :
    prepareConfiguredBridge live (fun _ => .ok (options, next)) factory fallback state = .error none := by
  simp [prepareConfiguredBridge, guardedGeneration_revised live state next options before after]

/-- An original configuration exception, including false, bypasses later stages. -/
theorem prepareConfiguredBridge_cause (live : State → Bool) (state : State) (cause : Cause)
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State)) (before : live state = true) :
    prepareConfiguredBridge live (fun _ => .error cause) factory fallback state = .error (some cause) := by
  simp [prepareConfiguredBridge, guardedGeneration_cause live state cause before]

/-- Stable configuration is read once and passed exactly to the existing bridge. -/
theorem prepareConfiguredBridge_continue (live : State → Bool) (state next : State) (options : Options)
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State))
    (before : live state = true) (after : live next = true) :
    prepareConfiguredBridge live (fun _ => .ok (options, next)) factory fallback state =
      prepareBridge live (factory options) (fallback options) next := by
  simp [prepareConfiguredBridge, guardedGeneration_state live state next options before after]

/-- A subsequent automatic factory is still governed by the initial live predicate. -/
theorem prepareConfiguredBridge_factory_revised (live : State → Bool)
    (state middle final : State) (options : Options) (candidate : Option Value)
    (fallback : Options → State → Except Cause (Value × State))
    (before : live state = true) (ready : live middle = true) (after : live final = false) :
    prepareConfiguredBridge live (fun _ => .ok (options, middle))
      (fun _ _ => .ok (candidate, final)) fallback state = .error none := by
  rw [prepareConfiguredBridge_continue live state middle options _ fallback before ready]
  exact prepareBridge_revised live middle final candidate (fallback options) ready after

/-- Stable configuration and owned trees preserve the final result and actual state. -/
theorem prepareConfiguredBridge_present (live : State → Bool)
    (state middle final : State) (options : Options) (value : Value)
    (fallback : Options → State → Except Cause (Value × State))
    (before : live state = true) (ready : live middle = true) (after : live final = true) :
    prepareConfiguredBridge live (fun _ => .ok (options, middle))
      (fun _ _ => .ok (some value, final)) fallback state = .ok (value, final) := by
  rw [prepareConfiguredBridge_continue live state middle options _ fallback before ready]
  simp [prepareBridge, guardedGeneration_state live middle final (some value) ready after]

/-- Refused preparation cannot enter a success publication/consumer function.
Application consumption of an error report is a separate IO operation. -/
theorem prepareConfiguredBridge_refused (live : State → Bool)
    (read : State → Except Cause (Options × State))
    (factory : Options → State → Except Cause (Option Value × State))
    (fallback : Options → State → Except Cause (Value × State)) (state : State)
    (cause : Option Cause) (consume : Value × State → Except (Option Cause) Output)
    (refused : prepareConfiguredBridge live read factory fallback state = .error cause) :
    (prepareConfiguredBridge live read factory fallback state >>= consume) = .error cause := by
  rw [refused]; rfl

/-- A freshly returned specification must be live at its first observation;
its constructor cannot authorize the final generator by supplying a stale domain. -/
theorem declaration_new_source_refused (live : State → Source → Bool)
    (outer captured : List Source) (state next : State) (added : Source) (domain : Value)
    (rest : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (build : List Value → (State × List Source) → Except Cause (Output × (State × List Source)))
    (before : scopeCurrent live outer (state, captured) = true) (stale : live next added = false) :
    guardedProduct (scopeCurrent live outer)
      ((fun _ => .ok (domain, (next, added :: captured))) :: rest) build (state, captured) = .error none := by
  apply guardedProduct_field_revised _ _ _ _ _ _ before
  simp [scopeCurrent, stale]

/-- Registering more declarations cannot repair the retirement of an earlier
captured domain. Faithful construction preserves the old prefix of the ledger. -/
theorem declaration_retained_sources_refuse (live : State → Source → Bool)
    (outer captured added : List Source) (state next : State) (domain : Value)
    (rest : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (build : List Value → (State × List Source) → Except Cause (Output × (State × List Source)))
    (before : scopeCurrent live outer (state, captured) = true)
    (stale : captured.all (live next) = false) :
    guardedProduct (scopeCurrent live outer)
      ((fun _ => .ok (domain, (next, captured ++ added))) :: rest) build (state, captured) = .error none := by
  apply guardedProduct_field_revised _ _ _ _ _ _ before
  simp [scopeCurrent, List.all_append, stale]

/-- Two ordered specification constructors pass their exact domain values and
actual final ledger to the existing generator-construction guard, exactly once. -/
theorem declaration_order (live : State → Source → Bool) (outer : List Source)
    (initial middle final : State × List Source) (first second : Value)
    (build : List Value → (State × List Source) → Except Cause (Output × (State × List Source)))
    (before : scopeCurrent live outer initial = true)
    (ready : scopeCurrent live outer middle = true) (after : scopeCurrent live outer final = true) :
    guardedProduct (scopeCurrent live outer)
      [(fun _ => .ok (first, middle)), (fun _ => .ok (second, final))] build initial =
      guardedGeneration (scopeCurrent live outer) (build [first, second]) final := by
  simp [guardedProduct, guardedStages, before,
    guardedGeneration_state _ initial middle first before ready,
    guardedGeneration_state _ middle final second ready after]

/-- Construction exceptions preserve their exact cause after stable ordered
specification preparation. This includes a false-like cause and skips success IO. -/
theorem declaration_build_cause (live : State → Source → Bool) (outer : List Source)
    (initial middle final : State × List Source) (first second : Value) (cause : Cause)
    (before : scopeCurrent live outer initial = true)
    (ready : scopeCurrent live outer middle = true) (after : scopeCurrent live outer final = true) :
    guardedProduct (scopeCurrent live outer)
      [(fun _ => .ok (first, middle)), (fun _ => .ok (second, final))]
      (fun _ _ => (.error cause : Except Cause (Output × (State × List Source)))) initial =
      .error (some cause) := by
  rw [declaration_order live outer initial middle final first second _ before ready after]
  exact guardedGeneration_cause _ final cause after

/-- A normally returned generator is refused if its construction retires a
captured specification. A later successful check cannot be entered with it. -/
theorem declaration_build_revised (live : State → Source → Bool) (outer : List Source)
    (initial middle final retired : State × List Source) (first second : Value) (generator : Output)
    (before : scopeCurrent live outer initial = true)
    (ready : scopeCurrent live outer middle = true) (after : scopeCurrent live outer final = true)
    (stale : scopeCurrent live outer retired = false) :
    guardedProduct (Cause := Cause) (scopeCurrent live outer)
      [(fun _ => .ok (first, middle)), (fun _ => .ok (second, final))]
      (fun _ _ => .ok (generator, retired)) initial = .error none := by
  rw [declaration_order live outer initial middle final first second _ before ready after]
  exact guardedGeneration_revised _ final retired generator after stale

/-- Prepared domains retain their real final ledger, not the transient checker
or inherited directory. Host dynamic-scope restoration remains a separate premise. -/
theorem declaration_publish (live : State → Source → Bool) (outer : List Source)
    (initial middle final : State × List Source) (first second : Value)
    (before : scopeCurrent live outer initial = true)
    (ready : scopeCurrent live outer middle = true) (after : scopeCurrent live outer final = true) :
    guardedProduct (Cause := Cause) (scopeCurrent live outer)
      [(fun _ => .ok (first, middle)), (fun _ => .ok (second, final))]
      (fun values state => .ok (values, state)) initial = .ok ([first, second], final) := by
  rw [declaration_order live outer initial middle final first second _ before ready after]
  exact guardedGeneration_state _ final final [first, second] after after

end LeanPoo.Functional.PropertyTesting
