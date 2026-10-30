import LeanPoo.Functional.PropertyProducts

/-! Run-local observation scope. Transient replay observers authorize callbacks;
only explicitly observed owners belong to the new report. Host scope fidelity,
pure observers and sequential terminating callbacks remain premises. -/
namespace LeanPoo.Functional.PropertyTesting

/-- A scope checks its transient observers and the run's evolving owner ledger.
The ledger contains source identities, never its own checking procedure. -/
def scopeCurrent (live : State → Source → Bool) (transient : List Source)
    (snapshot : State × List Source) : Bool :=
  transient.all (live snapshot.1) && snapshot.2.all (live snapshot.1)

/-- Existing guarded stages run under the joint scope. Identity publication
returns the actual ledger rather than adding the transient directory to it. -/
def scopedStages (live : State → Source → Bool) (transient : List Source)
    (stages : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (snapshot : State × List Source) :
    Except (Option Cause) (List Value × (State × List Source)) :=
  guardedProduct (scopeCurrent live transient) stages (fun values state => .ok (values, state)) snapshot

/-- With no transient scope, only the actual owner's admission remains. -/
theorem scopeCurrent_empty (live : State → Source → Bool) (snapshot : State × List Source) :
    scopeCurrent live [] snapshot = snapshot.2.all (live snapshot.1) := by
  simp [scopeCurrent]

/-- Nested transient scopes preserve both outer and inner authority. -/
theorem scopeCurrent_join [DecidableEq Source] (live : State → Source → Bool)
    (outer inner : List Source) (snapshot : State × List Source) :
    scopeCurrent live (mergeSources outer inner) snapshot = true ↔
      scopeCurrent live outer snapshot = true ∧ scopeCurrent live inner snapshot = true := by
  simp only [scopeCurrent, Bool.and_eq_true, mergeSources_current]
  constructor
  · rintro ⟨⟨left, right⟩, owned⟩
    exact ⟨⟨left, owned⟩, ⟨right, owned⟩⟩
  · rintro ⟨⟨left, owned⟩, ⟨right, _⟩⟩
    exact ⟨⟨left, right⟩, owned⟩

/-- An obsolete old report or current ledger suppresses all unstarted stages. -/
theorem scopedStages_preflight (live : State → Source → Bool) (transient : List Source)
    (stages : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (snapshot : State × List Source) (stale : scopeCurrent live transient snapshot = false) :
    scopedStages live transient stages snapshot = .error none := by
  exact guardedProduct_preflight _ stages _ snapshot stale

/-- A draw that retires any checked owner cannot enter the next mapper/selector. -/
theorem scopedStages_revised (live : State → Source → Bool) (transient : List Source)
    (before after : State × List Source) (value : Value)
    (rest : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (fresh : scopeCurrent live transient before = true)
    (stale : scopeCurrent live transient after = false) :
    scopedStages live transient ((fun _ => .ok (value, after)) :: rest) before = .error none := by
  exact guardedProduct_field_revised _ before after value rest _ fresh stale

/-- A thrown callback cause is preserved, with no post-check replacing it. -/
theorem scopedStages_cause (live : State → Source → Bool) (transient : List Source)
    (snapshot : State × List Source) (cause : Cause)
    (rest : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (fresh : scopeCurrent live transient snapshot = true) :
    scopedStages live transient ((fun _ => .error cause) :: rest) snapshot = .error (some cause) := by
  exact guardedProduct_field_cause _ snapshot cause rest _ fresh

/-- Even an empty inspection performs scope admission, without adding ownership. -/
theorem scopedStages_empty (live : State → Source → Bool) (transient : List Source)
    (snapshot : State × List Source) (fresh : scopeCurrent live transient snapshot = true) :
    scopedStages (Cause := Cause) (Value := Value) live transient [] snapshot = .ok ([], snapshot) := by
  simp [scopedStages, guardedProduct, guardedStages, guardedGeneration, fresh]

/-- Stable observation publishes exactly the new callback ledger. An old replay
directory authorizes the action but is not unioned into its resulting metadata. -/
theorem scopedStages_publish (live : State → Source → Bool) (transient : List Source)
    (before after : State × List Source) (value : Value)
    (fresh : scopeCurrent live transient before = true)
    (checked : scopeCurrent live transient after = true) :
    scopedStages (Cause := Cause) live transient [fun _ => .ok (value, after)] before = .ok ([value], after) := by
  simp [scopedStages, guardedProduct, guardedStages, guardedGeneration, fresh, checked]

/-- Stable fields retain their exact values/order without another sampler pass. -/
theorem scopedStages_constant (live : State → Source → Bool) (transient : List Source)
    (snapshot : State × List Source) (values : List Value)
    (fresh : scopeCurrent live transient snapshot = true) :
    scopedStages (Cause := Cause) live transient (values.map (fun value => fun _ => .ok (value, snapshot))) snapshot =
      .ok (values, snapshot) := by
  simp [scopedStages, guardedProduct, fresh, guardedStages_constant _ snapshot values fresh, guardedGeneration]

/-- Different admitted replay scopes cannot accumulate themselves in an
unchanged new ledger. Faithful callbacks supply that ledger explicitly. -/
theorem scopedStages_scopes_agree (live : State → Source → Bool) (left right : List Source)
    (before after : State × List Source) (value : Value)
    (leftBefore : scopeCurrent live left before = true) (leftAfter : scopeCurrent live left after = true)
    (rightBefore : scopeCurrent live right before = true) (rightAfter : scopeCurrent live right after = true) :
    scopedStages (Cause := Cause) live left [fun _ => .ok (value, after)] before =
      scopedStages live right [fun _ => .ok (value, after)] before := by
  rw [scopedStages_publish live left before after value leftBefore leftAfter,
      scopedStages_publish live right before after value rightBefore rightAfter]

/-- Two dependent model/fixture actions reuse the ordinary callback guard. The
second action receives the actual first value and state; no intermediate result
is authorized after revision. Serial terminating actions and pure observers are
premises. This is not a proof of host stack unwinding or concurrent publication. -/
def guardedThen (live : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State) :
    Except (Option Cause) (Output × State) :=
  match guardedGeneration live first state with
  | .error cause => .error cause
  | .ok (value, after) => guardedGeneration live (next value) after

/-- Preflight refusal suppresses both actions, including empty trace setup. -/
theorem guardedThen_preflight (live : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State)
    (stale : live state = false) : guardedThen live first next state = .error none := by
  simp [guardedThen, guardedGeneration, stale]

/-- A revised initializer/draw/observer cannot enter the dependent action. -/
theorem guardedThen_revised (live : State → Bool) (state after : State) (value : Value)
    (next : Value → State → Except Cause (Output × State))
    (before : live state = true) (stale : live after = false) :
    guardedThen live (fun _ => .ok (value, after)) next state = .error none := by
  simp [guardedThen, guardedGeneration, before, stale]

/-- Original causes survive without running the second callback or a post-check. -/
theorem guardedThen_cause (live : State → Bool) (state : State) (cause : Cause)
    (next : Value → State → Except Cause (Output × State)) (before : live state = true) :
    guardedThen live (fun _ => .error cause) next state = .error (some cause) := by
  simp [guardedThen, guardedGeneration, before]

/-- Fresh first results, including false-like values and tuples, are forwarded
exactly to the dependent action's own guard. -/
theorem guardedThen_continue (live : State → Bool) (state after : State) (value : Value)
    (next : Value → State → Except Cause (Output × State))
    (before : live state = true) (fresh : live after = true) :
    guardedThen live (fun _ => .ok (value, after)) next state =
      guardedGeneration live (next value) after := by
  simp [guardedThen, guardedGeneration, before, fresh]

/-- A normal second action that revises the source cannot publish its result. -/
theorem guardedThen_last_revised (live : State → Bool) (state middle after : State)
    (value : Value) (output : Output) (before : live state = true)
    (fresh : live middle = true) (stale : live after = false) :
    guardedThen (Cause := Cause) live (fun _ => .ok (value, middle))
      (fun _ _ => .ok (output, after)) state = .error none := by
  simp [guardedThen, guardedGeneration, before, fresh, stale]

/-- Finite fresh execution retains values and the final actual state exactly. -/
theorem guardedThen_present (live : State → Bool) (state middle after : State)
    (value : Value) (output : Output) (before : live state = true)
    (fresh : live middle = true) (current : live after = true) :
    guardedThen (Cause := Cause) live (fun _ => .ok (value, middle))
      (fun _ _ => .ok (output, after)) state = .ok (output, after) := by
  simp [guardedThen, guardedGeneration, before, fresh, current]

/-- Suppression composes: a refused pair cannot reach any later trace stage. -/
theorem guardedThen_refused (live : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State)
    (cause : Option Cause) (later : Output × State → Except (Option Cause) Other)
    (refused : guardedThen live first next state = .error cause) :
    (guardedThen live first next state >>= later) = .error cause := by
  rw [refused]; rfl

/-- Primitive actions inherit both ancestor authority and the child domain.
Terminal diagnostic reports have a separate parent-only publication boundary. -/
def nestedActions (parent child : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State) :
    Except (Option Cause) (Output × State) :=
  guardedThen (fun state => parent state && child state) first next state

/-- A fresh child cannot authorize callbacks beneath an obsolete parent. -/
theorem nestedActions_parent_stale (parent child : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State)
    (stale : parent state = false) : nestedActions parent child first next state = .error none := by
  apply guardedThen_preflight
  simp [stale]

/-- Ancestor freshness does not remove the child's own admission requirement. -/
theorem nestedActions_local_stale (parent child : State → Bool)
    (first : State → Except Cause (Value × State))
    (next : Value → State → Except Cause (Output × State)) (state : State)
    (stale : child state = false) : nestedActions parent child first next state = .error none := by
  apply guardedThen_preflight
  simp [stale]

/-- Parent revision stops later fields, packing and portable stages. -/
theorem nestedActions_parent_revised (parent child : State → Bool) (state after : State)
    (value : Value) (next : Value → State → Except Cause (Output × State))
    (before : parent state = true) (own : child state = true) (stale : parent after = false) :
    nestedActions parent child (fun _ => .ok (value, after)) next state = .error none := by
  apply guardedThen_revised
  · simp [before, own]
  · simp [stale]

/-- A child revision still suppresses the continuation when the parent stays live. -/
theorem nestedActions_local_revised (parent child : State → Bool) (state after : State)
    (value : Value) (next : Value → State → Except Cause (Output × State))
    (before : parent state = true) (own : child state = true) (stale : child after = false) :
    nestedActions parent child (fun _ => .ok (value, after)) next state = .error none := by
  apply guardedThen_revised
  · simp [before, own]
  · simp [stale]

/-- Thrown callback causes are not replaced by trailing source checks. -/
theorem nestedActions_cause (parent child : State → Bool) (state : State) (cause : Cause)
    (next : Value → State → Except Cause (Output × State))
    (before : parent state = true) (own : child state = true) :
    nestedActions parent child (fun _ => .error cause) next state = .error (some cause) := by
  apply guardedThen_cause
  simp [before, own]

/-- Fresh nested execution leaves values and state unchanged. -/
theorem nestedActions_present (parent child : State → Bool) (state middle after : State)
    (value : Value) (output : Output) (p₀ : parent state = true) (l₀ : child state = true)
    (p₁ : parent middle = true) (l₁ : child middle = true)
    (p₂ : parent after = true) (l₂ : child after = true) :
    nestedActions (Cause := Cause) parent child (fun _ => .ok (value, middle))
      (fun _ _ => .ok (output, after)) state = .ok (output, after) := by
  apply guardedThen_present <;> simp_all

/-- Even an early child diagnostic return must pass ancestor publication. -/
theorem nestedReport_parent_revised (parent : State → Bool) (state after : State)
    (diagnostic : Value) (before : parent state = true) (stale : parent after = false) :
    guardedGeneration parent (fun _ => (.ok (diagnostic, after) : Except Cause (Value × State))) state =
      .error none := guardedGeneration_revised parent state after diagnostic before stale

/-- A valid ancestor may receive any child diagnostic status. No child-current
check is re-entered at this boundary, so child refusal cannot call its own guard. -/
theorem nestedReport_diagnostic (parent : State → Bool) (state after : State)
    (diagnostic : Value) (before : parent state = true) (fresh : parent after = true) :
    guardedGeneration parent (fun _ => (.ok (diagnostic, after) : Except Cause (Value × State))) state =
      .ok (diagnostic, after) := guardedGeneration_state parent state after diagnostic before fresh

/-- Error interpretation reuses the same guarded callback boundary. An original
failure is diagnostic data: neither a secondary error nor refusal can replace it.
Classifier statuses are required to belong to the host's non-passing vocabulary;
malformed classifier outputs are rejected by the host before report publication. -/
def classifyFailure (live : State → Bool)
    (classify : State → Except Secondary (CheckStatus × State)) (original : Cause) (state : State) :
    CheckStatus × Cause :=
  match guardedGeneration live classify state with
  | .error none => (.stale, original)
  | .error (some _) => (.error, original)
  | .ok (status, _) => (status, original)

/-- Obsolete authority suppresses classification and refuses the original failure. -/
theorem classifyFailure_preflight (live : State → Bool)
    (classify : State → Except Secondary (CheckStatus × State)) (original : Cause) (state : State)
    (stale : live state = false) :
    classifyFailure live classify original state = (.stale, original) := by
  simp [classifyFailure, guardedGeneration_preflight live classify state stale]

/-- A normally returning classifier cannot publish a status after revising sources. -/
theorem classifyFailure_revised {Secondary : Type} (live : State → Bool)
    (original : Cause) (state after : State) (status : CheckStatus)
    (fresh : live state = true) (stale : live after = false) :
    classifyFailure (Secondary := Secondary) live (fun _ => .ok (status, after)) original state =
      (.stale, original) := by
  simp [classifyFailure, guardedGeneration_revised live state after status fresh stale]

/-- A classifier exception reports an error with the first cause, not its own. -/
theorem classifyFailure_secondary (live : State → Bool) (original : Cause)
    (secondary : Secondary) (state : State) (fresh : live state = true) :
    classifyFailure live (fun _ => .error secondary) original state = (.error, original) := by
  simp [classifyFailure, guardedGeneration_cause live state secondary fresh]

/-- Stable classification preserves its exact status and original diagnostic cause. -/
theorem classifyFailure_stable {Secondary : Type} (live : State → Bool) (original : Cause)
    (state after : State) (status : CheckStatus) (before : live state = true) (fresh : live after = true) :
    classifyFailure (Secondary := Secondary) live (fun _ => .ok (status, after)) original state =
      (status, original) := by
  simp [classifyFailure, guardedGeneration_state live state after status before fresh]

/-- Every possible classification outcome keeps the first failure identity. -/
theorem classifyFailure_original (live : State → Bool)
    (classify : State → Except Secondary (CheckStatus × State)) (original : Cause) (state : State) :
    (classifyFailure live classify original state).2 = original := by
  unfold classifyFailure
  split <;> rfl

/-- A lawful error classifier never manufactures passing or falsified evidence. -/
theorem classifyFailure_nonpassing (live : State → Bool)
    (classify : State → Except Secondary (CheckStatus × State)) (original : Cause) (state : State)
    (lawful : ∀ before status after, classify before = .ok (status, after) →
      status ≠ .passed ∧ status ≠ .failed) :
    (classifyFailure live classify original state).1 ≠ .passed ∧
      (classifyFailure live classify original state).1 ≠ .failed := by
  cases fresh : live state with
  | false => simp [classifyFailure, guardedGeneration, fresh]
  | true =>
    cases returned : classify state with
    | error secondary => simp [classifyFailure, guardedGeneration, fresh, returned]
    | ok result =>
      obtain ⟨status, after⟩ := result
      have allowed := lawful state status after returned
      cases later : live after <;>
        simp [classifyFailure, guardedGeneration, fresh, returned, later, allowed.1, allowed.2]


end LeanPoo.Functional.PropertyTesting
