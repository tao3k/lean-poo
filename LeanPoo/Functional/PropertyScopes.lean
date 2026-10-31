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

/-- Leaving a fixture restores the enclosing declaration ledger, preserving the
actual state and its revisions. It neither refreshes stamps nor rolls back effects. -/
def restoreDeclarations (declarations : List Source) (snapshot : State × List Source) :
    State × List Source := (snapshot.1, declarations)

/-- Scope restoration preserves the actual state, including callback revisions. -/
theorem restoreDeclarations_state (declarations : List Source) (snapshot : State × List Source) :
    (restoreDeclarations declarations snapshot).1 = snapshot.1 := rfl

/-- Restoring a scope twice cannot refresh any declaration identity. -/
theorem restoreDeclarations_idempotent (declarations : List Source) (snapshot : State × List Source) :
    restoreDeclarations declarations (restoreDeclarations declarations snapshot) =
      restoreDeclarations declarations snapshot := rfl

/-- Fixture-only revisions cease to matter after use; enclosing declarations and
transient ancestors still authorize teardown. No fixture stamp is recaptured. -/
theorem scopeCurrent_restored (live : State → Source → Bool) (outer declarations : List Source)
    (snapshot : State × List Source) :
    scopeCurrent live outer (restoreDeclarations declarations snapshot) =
      (outer.all (live snapshot.1) && declarations.all (live snapshot.1)) := rfl

/-- Retiring an enclosing model declaration cannot be repaired by fixture exit. -/
theorem scopeCurrent_restored_stale (live : State → Source → Bool)
    (outer declarations : List Source) (snapshot : State × List Source)
    (stale : declarations.all (live snapshot.1) = false) :
    scopeCurrent live outer (restoreDeclarations declarations snapshot) = false := by
  simp [scopeCurrent_restored, stale]

/-- Stable model and ancestor declarations permit cleanup regardless of the old
fixture ledger. Its objects do not escape into subsequent declaration authority. -/
theorem scopeCurrent_restored_current (live : State → Source → Bool)
    (outer declarations : List Source) (snapshot : State × List Source)
    (ancestors : outer.all (live snapshot.1) = true)
    (models : declarations.all (live snapshot.1) = true) :
    scopeCurrent live outer (restoreDeclarations declarations snapshot) = true := by
  simp [scopeCurrent_restored, ancestors, models]

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

/-- Every action in a nested handoff observes both codec and application scope.
This is an equality of whole finite stage executions, not just final admission.
Observers are pure and total; the host still preserves its ordered error checks. -/
theorem scopedStages_inherit [DecidableEq Source] (live : State → Source → Bool)
    (outer inner : List Source)
    (stages : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (snapshot : State × List Source) :
    scopedStages live (mergeSources outer inner) stages snapshot =
      guardedProduct (fun state => scopeCurrent live outer state && scopeCurrent live inner state)
        stages (fun values state => .ok (values, state)) snapshot := by
  have guards : scopeCurrent live (mergeSources outer inner) =
      (fun state => scopeCurrent live outer state && scopeCurrent live inner state) := by
    funext state
    apply Bool.eq_iff_iff.mpr
    simpa only [Bool.and_eq_true] using scopeCurrent_join live outer inner state
  simp only [scopedStages, guards]

/-- A nested action with no additional transient owner keeps the entire parent
authority. Empty child ownership cannot authorize work beneath a retired codec. -/
theorem scopedStages_empty_child [DecidableEq Source] (live : State → Source → Bool)
    (outer : List Source)
    (stages : List ((State × List Source) → Except Cause (Value × (State × List Source))))
    (snapshot : State × List Source) :
    scopedStages live (mergeSources outer []) stages snapshot = scopedStages live outer stages snapshot := by
  have guards : scopeCurrent live (mergeSources outer []) = scopeCurrent live outer := by
    funext state
    apply Bool.eq_iff_iff.mpr
    simp [scopeCurrent, List.all_eq_true, mergeSources_mem]
  simp only [scopedStages, guards]

/-- Discovery records a source's first revision. Repeated edges share that
snapshot rather than silently authorizing a newer epoch. Identity hashing in the
host implements this finite association-list semantics. -/
def captureRevision [DecidableEq Source] (ledger : List (Source × Nat))
    (source : Source) (revision : Nat) : List (Source × Nat) :=
  if source ∈ ledger.map Prod.fst then ledger else (source, revision) :: ledger

/-- Currentness observes every registered revision; new callbacks cannot replace
the ledger. Opaque sampler admission remains an additional host predicate. -/
def revisionsCurrent (current : Source → Nat) (ledger : List (Source × Nat)) : Bool :=
  ledger.all (fun stamp => stamp.2 == current stamp.1)

/-- A known source keeps its exact old revision and ledger position. -/
theorem captureRevision_existing [DecidableEq Source] (ledger : List (Source × Nat))
    (source : Source) (revision : Nat) (known : source ∈ ledger.map Prod.fst) :
    captureRevision ledger source revision = ledger := by simp [captureRevision, known]

/-- A newly discovered identity is captured once at its current frontier. -/
theorem captureRevision_new [DecidableEq Source] (ledger : List (Source × Nat))
    (source : Source) (revision : Nat) (unknown : source ∉ ledger.map Prod.fst) :
    captureRevision ledger source revision = (source, revision) :: ledger := by
  simp [captureRevision, unknown]

/-- Each registration adds at most one metadata entry, even with shared edges. -/
theorem captureRevision_length [DecidableEq Source] (ledger : List (Source × Nat))
    (source : Source) (revision : Nat) :
    (captureRevision ledger source revision).length ≤ ledger.length + 1 := by
  unfold captureRevision
  split <;> simp_all

/-- Distinct source identities stay distinct under arbitrary rediscovery. -/
theorem captureRevision_unique [DecidableEq Source] (ledger : List (Source × Nat))
    (source : Source) (revision : Nat) (unique : (ledger.map Prod.fst).Nodup) :
    ((captureRevision ledger source revision).map Prod.fst).Nodup := by
  unfold captureRevision
  split <;> simp_all

/-- Neither revisiting a known source nor adding a new one repairs stale history. -/
theorem captureRevision_stale [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (source : Source) (revision : Nat)
    (stale : revisionsCurrent current ledger = false) :
    revisionsCurrent current (captureRevision ledger source revision) = false := by
  unfold captureRevision
  split <;> simp_all [revisionsCurrent]

/-- A fresh first observation extends a fresh ledger without changing old epochs. -/
theorem captureRevision_fresh [DecidableEq Source] (current : Source → Nat)
    (ledger : List (Source × Nat)) (source : Source)
    (fresh : revisionsCurrent current ledger = true) :
    revisionsCurrent current (captureRevision ledger source (current source)) = true := by
  unfold captureRevision
  split
  · exact fresh
  · simpa [revisionsCurrent] using fresh

/-- One computed declaration read checks all earlier stamps before and after
its callback, then captures the returned identity at its first observed revision.
The host validates Type identities separately; discovery never refreshes history. -/
def observeDeclaration [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (Source × State))
    (state : State) : Except (Option Cause) (Source × (State × List (Source × Nat))) :=
  (guardedGeneration (fun before => revisionsCurrent (current before) ledger) read state).map
    (fun result => (result.1,
      (result.2, captureRevision ledger result.1 (current result.2 result.1))))

/-- Already stale metadata prevents even the next computed field from running. -/
theorem observeDeclaration_preflight [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (Source × State)) (state : State)
    (stale : revisionsCurrent (current state) ledger = false) :
    observeDeclaration current ledger read state = .error none := by
  simp [observeDeclaration, Except.map, guardedGeneration_preflight (fun before => revisionsCurrent (current before) ledger) read state stale]

/-- A later getter cannot retire an earlier field and then capture fresh authority. -/
theorem observeDeclaration_revised [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state after : State) (source : Source)
    (fresh : revisionsCurrent (current state) ledger = true)
    (stale : revisionsCurrent (current after) ledger = false) :
    observeDeclaration (Cause := Cause) current ledger (fun _ => .ok (source, after)) state =
      .error none := by
  simp [observeDeclaration, Except.map, guardedGeneration_revised (fun before => revisionsCurrent (current before) ledger) state after source fresh stale]

/-- An original computed-field exception remains exact; no new stamp is installed. -/
theorem observeDeclaration_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state : State) (cause : Cause)
    (fresh : revisionsCurrent (current state) ledger = true) :
    observeDeclaration current ledger (fun _ => .error cause) state = .error (some cause) := by
  simp [observeDeclaration, Except.map, guardedGeneration_cause (fun before => revisionsCurrent (current before) ledger) state cause fresh]

/-- Stable preparation records the returned identity and actual state exactly. -/
theorem observeDeclaration_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state after : State) (source : Source)
    (fresh : revisionsCurrent (current state) ledger = true)
    (later : revisionsCurrent (current after) ledger = true) :
    observeDeclaration (Cause := Cause) current ledger (fun _ => .ok (source, after)) state =
      .ok (source, (after, captureRevision ledger source (current after source))) := by
  simp [observeDeclaration, Except.map, guardedGeneration_state (fun before => revisionsCurrent (current before) ledger) state after source fresh later]

/-- Admission after a successful read includes both earlier fields and the new
one. It does not claim atomic concurrent reads or callback termination. -/
theorem observeDeclaration_current [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (read : State → Except Cause (Source × State)) (state after : State)
    (source : Source) (captured : List (Source × Nat))
    (success : observeDeclaration current ledger read state = .ok (source, (after, captured))) :
    revisionsCurrent (current after) captured = true := by
  unfold observeDeclaration guardedGeneration at success
  split at success
  · split at success
    · contradiction
    · split at success
      · cases success
        apply captureRevision_fresh
        assumption
      · contradiction
  · contradiction

/-- A typed sampler always owns its identity and actual declaration; additional
application dependencies can extend but cannot erase these two participants. -/
def samplerOwners [DecidableEq Source] (owner descriptor : Source) (dependencies : List Source) : List Source :=
  mergeSources [owner, descriptor] dependencies

/-- Constructor binding is checked as preparation data, without invoking a tree
factory or a value predicate. A mismatch is a configuration error, not falsity. -/
def prepareSampler [DecidableEq Source] (owner bound actual : Source)
    (dependencies : List Source) : Except Unit (List Source) :=
  if bound = actual then .ok (samplerOwners owner actual dependencies) else .error ()

/-- Only the two mandatory identities and explicitly declared owners participate. -/
theorem samplerOwners_mem [DecidableEq Source] (source owner descriptor : Source) (dependencies : List Source) :
    source ∈ samplerOwners owner descriptor dependencies ↔
      source = owner ∨ source = descriptor ∨ source ∈ dependencies := by
  simp [samplerOwners, mergeSources_mem, or_assoc]

/-- Freshness includes both mandatory owners even when dependencies are replaced. -/
theorem samplerOwners_current [DecidableEq Source] (live : Source → Bool)
    (owner descriptor : Source) (dependencies : List Source) :
    (samplerOwners owner descriptor dependencies).all live = true ↔
      live owner = true ∧ live descriptor = true ∧ dependencies.all live = true := by
  change (mergeSources [owner, descriptor] dependencies).all live = true ↔ _
  rw [mergeSources_current]
  simp [Bool.and_eq_true, and_assoc]

/-- No dependency list can hide a changed actual Type from the prepared sampler. -/
theorem samplerOwners_descriptor_stale [DecidableEq Source] (live : Source → Bool)
    (owner descriptor : Source) (dependencies : List Source) (stale : live descriptor = false) :
    (samplerOwners owner descriptor dependencies).all live = false := by
  cases observed : (samplerOwners owner descriptor dependencies).all live with
  | false => rfl
  | true =>
    have required := (samplerOwners_current live owner descriptor dependencies).mp observed
    simp [stale] at required

/-- Ordinary construction and same-declaration derivation admit the same owners. -/
theorem prepareSampler_same [DecidableEq Source] (owner descriptor : Source) (dependencies : List Source) :
    prepareSampler owner descriptor descriptor dependencies = .ok (samplerOwners owner descriptor dependencies) := by
  simp [prepareSampler]

/-- Inherited protocols cannot relabel their constructor's declaration. -/
theorem prepareSampler_changed [DecidableEq Source] (owner bound actual : Source)
    (dependencies : List Source) (different : bound ≠ actual) :
    prepareSampler owner bound actual dependencies = .error () := by
  simp [prepareSampler, different]

/-- Successful preparation preserves the declaration binding and mandatory identities. -/
theorem prepareSampler_sound [DecidableEq Source] (owner bound actual : Source)
    (dependencies owners : List Source) (admitted : prepareSampler owner bound actual dependencies = .ok owners) :
    bound = actual ∧ owner ∈ owners ∧ actual ∈ owners := by
  unfold prepareSampler at admitted
  split at admitted
  · rename_i matching
    cases admitted
    exact ⟨matching, (samplerOwners_mem owner owner actual dependencies).mpr (Or.inl rfl),
      (samplerOwners_mem actual owner actual dependencies).mpr (Or.inr (Or.inl rfl))⟩
  · contradiction

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


/-- Standard assertion admission consumes actual report authority. Rendering is
arbitrary data: only a present passed report and fresh source checks before/after
rendering can pass. Missing execution and original nonpassing causes stay failures.
Host exception delivery is represented by the error projection, not verified here. -/
def admitRendering (present : Bool) (actual : CheckDiagnostics Value Cause)
    (live : State → Bool) (render : State → Except Cause (Rendered × State)) (state : State) :
    Except (CheckStatus × Option Cause) Unit :=
  if !present then .error (if actual.status = .passed then .error else actual.status, actual.cause)
  else if actual.status = .passed then
    match guardedGeneration (fun before => actual.current && live before) render state with
    | .error none => .error (.stale, actual.cause)
    | .error (some cause) => .error (.error, some cause)
    | .ok _ => .ok ()
  else .error (actual.status, actual.cause)

/-- Diagnostic data cannot manufacture an execution, even when it claims passed. -/
theorem admitRendering_missing (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (render : State → Except Cause (Rendered × State)) (state : State) :
    admitRendering false actual live render state ≠ .ok () := by
  simp [admitRendering]

/-- Rendering cannot promote falsification, exhaustion, error or coverage refusal. -/
theorem admitRendering_nonpass (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (render : State → Except Cause (Rendered × State)) (state : State)
    (refused : actual.status ≠ .passed) :
    admitRendering true actual live render state = .error (actual.status, actual.cause) := by
  simp [admitRendering, refused]

/-- Invalid report authority suppresses even the renderer's first action. -/
theorem admitRendering_preflight (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (render : State → Except Cause (Rendered × State)) (state : State)
    (passed : actual.status = .passed) (stale : (actual.current && live state) = false) :
    admitRendering true actual live render state = .error (.stale, actual.cause) := by
  simp [admitRendering, passed, guardedGeneration, stale]

/-- A normal renderer return cannot publish success after retiring report sources. -/
theorem admitRendering_revised (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (state after : State) (value : Rendered) (passed : actual.status = .passed)
    (before : (actual.current && live state) = true) (later : (actual.current && live after) = false) :
    admitRendering true actual live (fun _ => .ok (value, after)) state = .error (.stale, actual.cause) := by
  simp [admitRendering, passed, guardedGeneration, before, later]

/-- Arbitrary rendered status/cause fields do not alter valid report admission. -/
theorem admitRendering_stable (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (state after : State) (value : Rendered) (passed : actual.status = .passed)
    (before : (actual.current && live state) = true) (later : (actual.current && live after) = true) :
    admitRendering true actual live (fun _ => .ok (value, after)) state = .ok () := by
  simp [admitRendering, passed, guardedGeneration, before, later]

/-- A renderer exception remains its precise cause and is never passing evidence. -/
theorem admitRendering_cause (actual : CheckDiagnostics Value Cause) (live : State → Bool)
    (state : State) (cause : Cause) (passed : actual.status = .passed)
    (before : (actual.current && live state) = true) :
    admitRendering (Rendered := Rendered) true actual live (fun _ => .error cause) state =
      .error (.error, some cause) := by
  simp [admitRendering, passed, guardedGeneration, before]

/-- Success requires actual execution, nominal passage and current sources;
no condition is discharged by the diagnostic payload returned by rendering. -/
theorem admitRendering_authority (present : Bool) (actual : CheckDiagnostics Value Cause)
    (live : State → Bool) (render : State → Except Cause (Rendered × State)) (state : State)
    (success : admitRendering present actual live render state = .ok ()) :
    present = true ∧ actual.status = .passed ∧ actual.current = true ∧ live state = true := by
  cases available : present with
  | false => simp [admitRendering, available] at success
  | true =>
    by_cases passed : actual.status = .passed
    · have fresh : (actual.current && live state) = true := by
        cases checked : actual.current && live state with
        | false => simp [admitRendering, available, passed, guardedGeneration, checked] at success
        | true => rfl
      have components : actual.current = true ∧ live state = true := by
        cases before : actual.current <;> cases now : live state <;> simp_all
      exact ⟨rfl, passed, components.1, components.2⟩
    · simp [admitRendering, available, passed] at success

/-- Finite function observations inherit call-site authority without storing it
in the retained table. The shared action gate also owns table/domain export. -/
def observeFunction (parent owner : State → Bool)
    (observe : State → Except Cause (Value × State)) (state : State) :=
  guardedGeneration (fun snapshot => parent snapshot && owner snapshot) observe state

/-- An obsolete caller cannot reach a table observation, even with a live table. -/
theorem observeFunction_parent_refused (parent owner : State → Bool)
    (observe : State → Except Cause (Value × State)) (state : State)
    (stale : parent state = false) :
    observeFunction parent owner observe state = .error none := by
  simp [observeFunction, guardedGeneration, stale]

/-- A fresh caller cannot authorize a table whose retained owner is obsolete. -/
theorem observeFunction_owner_refused (parent owner : State → Bool)
    (observe : State → Except Cause (Value × State)) (state : State)
    (stale : owner state = false) :
    observeFunction parent owner observe state = .error none := by
  simp [observeFunction, guardedGeneration, stale]

/-- Current observation preserves the exact payload and continuation state. -/
theorem observeFunction_stable (parent owner : State → Bool)
    (state after : State) (value : Value)
    (before : (parent state && owner state) = true)
    (later : (parent after && owner after) = true) :
    observeFunction parent owner (fun _ => (.ok (value, after) : Except Cause (Value × State))) state =
      .ok (value, after) := by
  simp [observeFunction, guardedGeneration, before, later]

/-- Retirement before normal return cannot publish a successful observation. -/
theorem observeFunction_revised (parent owner : State → Bool)
    (state after : State) (value : Value)
    (before : (parent state && owner state) = true) (later : parent after = false) :
    observeFunction parent owner (fun _ => (.ok (value, after) : Except Cause (Value × State))) state =
      .error none := by
  simp [observeFunction, guardedGeneration, before, later]

/-- Callback failure is kept exactly; source admission does not replace its cause. -/
theorem observeFunction_cause (parent owner : State → Bool)
    (state : State) (cause : Cause) (before : (parent state && owner state) = true) :
    observeFunction parent owner (fun _ => (.error cause : Except Cause (Value × State))) state =
      .error (some cause) := by
  simp [observeFunction, guardedGeneration, before]

/-- Finite dispatch reuses the established exact-row lookup, with an explicit
missing-row failure rather than a fallback output or unconstrained result type. -/
def callFunction [DecidableEq Input] (parent owner : State → Bool) (missing : Cause)
    (table : List (Input × Output)) (input : Input) (state : State) :=
  observeFunction parent owner (fun snapshot =>
    match lookupFunction table input with
    | none => .error missing
    | some value => .ok (value, snapshot)) state

/-- Fresh dispatch returns precisely the existing table's selected result. -/
theorem callFunction_known [DecidableEq Input] (parent owner : State → Bool) (missing : Cause)
    (table : List (Input × Output)) (input : Input) (state : State) (value : Output)
    (fresh : (parent state && owner state) = true) (found : lookupFunction table input = some value) :
    callFunction parent owner missing table input state = .ok (value, state) := by
  simp [callFunction, observeFunction, guardedGeneration, fresh, found]

/-- Missing finite rows stay errors under a fresh caller, never generated defaults. -/
theorem callFunction_unknown [DecidableEq Input] (parent owner : State → Bool) (missing : Cause)
    (table : List (Input × Output)) (input : Input) (state : State)
    (fresh : (parent state && owner state) = true)
    (absent : ∀ entry ∈ table, input ≠ entry.1) :
    callFunction parent owner missing table input state = .error (some missing) := by
  simp [callFunction, observeFunction, guardedGeneration, fresh, unknown_function_row table absent]

/-- A Map factory observes Key then Value using the existing first-stamp ledger.
Known request owners are supplied before either read, including empty-key Maps. -/
def observeMap [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (key value : State → Except Cause (Source × State))
    (state : State) : Except (Option Cause) ((Source × Source) × (State × List (Source × Nat))) :=
  match observeDeclaration current ledger key state with
  | .error cause => .error cause
  | .ok (k, (afterKey, captured)) =>
    (observeDeclaration current captured value afterKey).map (fun result => ((k, result.1), result.2))

/-- A stale request prevents both metadata getters, independently of key count. -/
theorem observeMap_preflight [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (key value : State → Except Cause (Source × State))
    (state : State) (stale : revisionsCurrent (current state) ledger = false) :
    observeMap current ledger key value state = .error none := by
  simp [observeMap, observeDeclaration_preflight current ledger key state stale]

/-- A failed first read cannot invoke Value or bind a partial Map factory. -/
theorem observeMap_key_error [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (key value : State → Except Cause (Source × State))
    (state : State) (cause : Option Cause)
    (failed : observeDeclaration current ledger key state = .error cause) :
    observeMap current ledger key value state = .error cause := by
  simp [observeMap, failed]

/-- Any failure of the second read is propagated without refreshing the first. -/
theorem observeMap_value_error [DecidableEq Source] (current : State → Source → Nat)
    (ledger captured : List (Source × Nat)) (key value : State → Except Cause (Source × State))
    (state afterKey : State) (k : Source) (cause : Option Cause)
    (first : observeDeclaration current ledger key state = .ok (k, (afterKey, captured)))
    (second : observeDeclaration current captured value afterKey = .error cause) :
    observeMap current ledger key value state = .error cause := by
  simp [observeMap, first, second, Except.map]

/-- Editing Key inside Value refuses even if Value itself could be captured anew. -/
theorem observeMap_value_revises [DecidableEq Source] (current : State → Source → Nat)
    (ledger captured : List (Source × Nat)) (key : State → Except Cause (Source × State))
    (state afterKey afterValue : State) (k v : Source)
    (first : observeDeclaration current ledger key state = .ok (k, (afterKey, captured)))
    (stale : revisionsCurrent (current afterValue) captured = false) :
    observeMap (Cause := Cause) current ledger key (fun _ => .ok (v, afterValue)) state = .error none := by
  apply observeMap_value_error current ledger captured key _ state afterKey k none first
  exact observeDeclaration_revised current captured afterKey afterValue v
    (observeDeclaration_current current ledger key state afterKey k captured first) stale

/-- Original second-getter errors remain exact, including false-valued causes. -/
theorem observeMap_value_cause [DecidableEq Source] (current : State → Source → Nat)
    (ledger captured : List (Source × Nat)) (key : State → Except Cause (Source × State))
    (state afterKey : State) (k : Source) (cause : Cause)
    (first : observeDeclaration current ledger key state = .ok (k, (afterKey, captured))) :
    observeMap current ledger key (fun _ => .error cause) state = .error (some cause) := by
  apply observeMap_value_error current ledger captured key _ state afterKey k (some cause) first
  exact observeDeclaration_cause current captured afterKey cause
    (observeDeclaration_current current ledger key state afterKey k captured first)

/-- Stable readings publish exactly the two effective Types and original ledger. -/
theorem observeMap_stable [DecidableEq Source] (current : State → Source → Nat)
    (ledger : List (Source × Nat)) (state afterKey afterValue : State) (k v : Source)
    (before : revisionsCurrent (current state) ledger = true)
    (keyLive : revisionsCurrent (current afterKey) ledger = true)
    (valueLive : revisionsCurrent (current afterValue)
      (captureRevision ledger k (current afterKey k)) = true) :
    observeMap (Cause := Cause) current ledger (fun _ => .ok (k, afterKey))
      (fun _ => .ok (v, afterValue)) state = .ok ((k, v), (afterValue,
        captureRevision (captureRevision ledger k (current afterKey k)) v (current afterValue v))) := by
  simp [observeMap, observeDeclaration_stable current ledger state afterKey k before keyLive,
    observeDeclaration_stable current (captureRevision ledger k (current afterKey k)) afterKey afterValue v
      (captureRevision_fresh (current afterKey) ledger k keyLive) valueLive, Except.map]

/-- One Map preparation adds at most two identities, sharing aliases and roots. -/
theorem observeMap_capture_cost [DecidableEq Source] (ledger : List (Source × Nat))
    (k v : Source) (kr vr : Nat) :
    (captureRevision (captureRevision ledger k kr) v vr).length ≤ ledger.length + 2 := by
  have first := captureRevision_length ledger k kr
  have second := captureRevision_length (captureRevision ledger k kr) v vr
  omega

end LeanPoo.Functional.PropertyTesting
