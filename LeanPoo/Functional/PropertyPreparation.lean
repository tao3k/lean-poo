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

/-- Read one finite Function declaration row under the already captured epochs,
then retain newly discovered clause/input identities. No child generator is run.
The host supplies faithful terminating metadata reads and revision counters. -/
def observeFunctionInputs [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat))
    (read : State → Except Cause (List Source × State)) (state : State) :
    Except (Option Cause) (List Source × (State × List (Source × Nat))) :=
  (guardedGeneration (fun before => revisionsCurrent (current before) ledger) read state).map
    (fun result => (result.1, (result.2, captureSources (current result.2) ledger result.1)))

/-- A stale Function/clause/input skips the next getter, not merely child draws. -/
theorem observeFunctionInputs_stale [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (List Source × State)) (state : State)
    (stale : revisionsCurrent (current state) ledger = false) :
    observeFunctionInputs current ledger read state = .error none := by
  simp [observeFunctionInputs, guardedGeneration_preflight (fun before => revisionsCurrent (current before) ledger) read state stale, Except.map]

/-- A computed field cannot retire a known participant and capture its new epoch. -/
theorem observeFunctionInputs_revised [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state next : State) (row : List Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = false) :
    observeFunctionInputs (Cause := Cause) current ledger (fun _ => .ok (row, next)) state = .error none := by
  simp [observeFunctionInputs, guardedGeneration_revised (fun before => revisionsCurrent (current before) ledger) state next row before after, Except.map]

/-- Original metadata errors, including false, retain precedence over retirement. -/
theorem observeFunctionInputs_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state : State) (cause : Cause)
    (before : revisionsCurrent (current state) ledger = true) :
    observeFunctionInputs current ledger (fun _ => .error cause) state = .error (some cause) := by
  simp [observeFunctionInputs, guardedGeneration_cause (fun before => revisionsCurrent (current before) ledger) state cause before, Except.map]

/-- Stable discovery preserves exact row order and records each first observation. -/
theorem observeFunctionInputs_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state next : State) (row : List Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) :
    observeFunctionInputs (Cause := Cause) current ledger (fun _ => .ok (row, next)) state =
      .ok (row, (next, captureSources (current next) ledger row)) := by
  simp [observeFunctionInputs, guardedGeneration_state (fun before => revisionsCurrent (current before) ledger) state next row before after, Except.map]

/-- A later metadata field cannot repair retirement by rediscovering declarations.
This applies equally to a cached layout or an unforced optional child. -/
theorem functionInputs_retained_refusal [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source) (state : State)
    (draw : State → Except Cause (Value × State))
    (stale : revisionsCurrent (current state) ledger = false) :
    guardedGeneration (fun before => revisionsCurrent (current before)
      (captureSources (current state) ledger row)) draw state = .error none := by
  exact guardedGeneration_preflight _ draw state (captureSources_stale _ row ledger stale)

/-- Captured metadata bookkeeping is bounded by returned identities, not trials
or cached-layout hits. This is a ledger-size bound, not a runtime latency claim. -/
theorem functionInputs_capture_cost [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source) :
    (captureSources current ledger row).length ≤ ledger.length + row.length :=
  captureSources_cost current row ledger

/-- Repeated known declarations do not refresh epochs even if callbacks advanced
state; only explicit fresh preparation can establish a new initial ledger. -/
theorem functionInputs_known [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (row : List Source)
    (known : ∀ source ∈ row, source ∈ ledger.map Prod.fst) :
    captureSources current ledger row = ledger := captureSources_known current row ledger known

/-- Refused metadata acquisition cannot enter subsequent generator construction. -/
theorem observeFunctionInputs_refused [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (List Source × State))
    (state : State) (cause : Option Cause)
    (build : List Source × (State × List (Source × Nat)) → Except (Option Cause) Value)
    (refused : observeFunctionInputs current ledger read state = .error cause) :
    (observeFunctionInputs current ledger read state >>= build) = .error cause := by
  rw [refused]; rfl

/-- A fixed carrier edge spends occurrence fuel before its metadata callback,
then records the returned Type at first observation. Shared IDs still spend fuel.
Host callbacks terminate and source revisions faithfully describe supported edits. -/
def discoverCarrierEdge [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat)
    (read : State → Except Cause (Source × State)) (state : State) :
    Except (Option Cause) (Source × (State × Nat × List (Source × Nat))) :=
  match fuel with
  | 0 => .error (some quota)
  | rest + 1 =>
    (guardedGeneration (fun before => revisionsCurrent (current before) ledger) read state).map
      (fun result => (result.1, (result.2, rest,
        captureRevision ledger result.1 (current result.2 result.1))))

/-- Exhausted discovery never evaluates a computed child declaration. -/
theorem discoverCarrierEdge_empty [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause)
    (read : State → Except Cause (Source × State)) (state : State) :
    discoverCarrierEdge current ledger quota 0 read state = .error (some quota) := rfl

/-- Available fuel does not authorize a getter under obsolete captured epochs. -/
theorem discoverCarrierEdge_stale [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat)
    (read : State → Except Cause (Source × State)) (state : State)
    (stale : revisionsCurrent (current state) ledger = false) :
    discoverCarrierEdge current ledger quota (fuel + 1) read state = .error none := by
  simp [discoverCarrierEdge, guardedGeneration_preflight
    (fun before => revisionsCurrent (current before) ledger) read state stale, Except.map]

/-- Original exceptions, including false, bypass normal post-return refusal. -/
theorem discoverCarrierEdge_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota cause : Cause) (fuel : Nat) (state : State)
    (before : revisionsCurrent (current state) ledger = true) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .error cause) state =
      .error (some cause) := by
  simp [discoverCarrierEdge, guardedGeneration_cause
    (fun before => revisionsCurrent (current before) ledger) state cause before, Except.map]

/-- A later Pair field cannot retire its earlier captured sibling and publish. -/
theorem discoverCarrierEdge_revised [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = false) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state = .error none := by
  simp [discoverCarrierEdge, guardedGeneration_revised
    (fun before => revisionsCurrent (current before) ledger) state next child before after, Except.map]

/-- Stable discovery returns the exact child, actual state and one fewer edge. -/
theorem discoverCarrierEdge_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state =
      .ok (child, (next, fuel, captureRevision ledger child (current next child))) := by
  simp [discoverCarrierEdge, guardedGeneration_state
    (fun before => revisionsCurrent (current before) ledger) state next child before after, Except.map]

/-- Shared child occurrences spend edge fuel without refreshing the old epoch. -/
theorem discoverCarrierEdge_shared [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (quota : Cause) (fuel : Nat) (state next : State) (child : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (after : revisionsCurrent (current next) ledger = true) (known : child ∈ ledger.map Prod.fst) :
    discoverCarrierEdge current ledger quota (fuel + 1) (fun _ => .ok (child, next)) state =
      .ok (child, (next, fuel, ledger)) := by
  rw [discoverCarrierEdge_stable current ledger quota fuel state next child before after,
    captureRevision_existing ledger child (current next child) known]

/-- Capturing a child makes it current for the next field while retaining all
prior authority; it never validates the child's generator or recursive payload. -/
theorem discoverCarrierEdge_current [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (child : Source) (before : revisionsCurrent current ledger = true) :
    revisionsCurrent current (captureRevision ledger child (current child)) = true :=
  captureRevision_fresh current ledger child before

/-- Registration grows by at most one identity per edge, independently of sharing.
This bounds ledger cardinality, not callback runtime or hash-table latency. -/
theorem discoverCarrierEdge_capture_cost [DecidableEq Source] (ledger : List (Source × Nat))
    (child : Source) (epoch : Nat) :
    (captureRevision ledger child epoch).length ≤ ledger.length + 1 :=
  captureRevision_length ledger child epoch

end LeanPoo.Functional.PropertyTesting
