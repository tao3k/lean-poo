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

end LeanPoo.Functional.PropertyTesting
