import LeanPoo.Functional.PropertyGenerators

/-! Shared finite product observation. Field callbacks and representation packing
use the existing guarded stages; faithful captured topology is a host premise. -/
namespace LeanPoo.Functional.PropertyTesting
universe u

/-- A common owner protects even zero fields. Each field is checked before/after
execution, and packing cannot run after a refusal. -/
def guardedProduct (live : State → Bool)
    (fields : List (State → Except Cause (Value × State)))
    (pack : List Value → State → Except Cause (Output × State)) (state : State) :
    Except (Option Cause) (Output × State) :=
  if live state then
    match guardedStages live fields state with
    | .error cause => .error cause
    | .ok (values, next) => guardedGeneration live (pack values) next
  else .error none

/-- An obsolete owner suppresses all field and representation effects. -/
theorem guardedProduct_preflight (live : State → Bool)
    (fields : List (State → Except Cause (Value × State)))
    (pack : List Value → State → Except Cause (Output × State)) (state : State)
    (stale : live state = false) : guardedProduct live fields pack state = .error none := by
  simp [guardedProduct, stale]

/-- A field revision suppresses later fields and packing, rather than merely
refusing after the complete product has already been evaluated. -/
theorem guardedProduct_field_revised (live : State → Bool) (state next : State) (value : Value)
    (rest : List (State → Except Cause (Value × State)))
    (pack : List Value → State → Except Cause (Output × State))
    (before : live state = true) (after : live next = false) :
    guardedProduct live ((fun _ => .ok (value, next)) :: rest) pack state = .error none := by
  simp [guardedProduct, before, guardedStages_revised live state next value rest before after]

/-- An original field exception remains the exact exception and skips its tail. -/
theorem guardedProduct_field_cause (live : State → Bool) (state : State) (cause : Cause)
    (rest : List (State → Except Cause (Value × State)))
    (pack : List Value → State → Except Cause (Output × State)) (before : live state = true) :
    guardedProduct live ((fun _ => .error cause) :: rest) pack state = .error (some cause) := by
  simp [guardedProduct, before, guardedStages_cause live state cause rest before]

/-- Zero fields still retain common owner checks around their representation. -/
theorem guardedProduct_empty (live : State → Bool)
    (pack : List Value → State → Except Cause (Output × State)) (state : State) :
    guardedProduct live [] pack state = guardedGeneration live (pack []) state := by
  cases fresh : live state <;> simp [guardedProduct, guardedStages, guardedGeneration, fresh]

/-- A packing callback cannot publish a value after revising the product owner. -/
theorem guardedProduct_packing_revised {Cause : Type u} (live : State → Bool)
    (state next : State) (value : Output) (before : live state = true) (after : live next = false) :
    guardedProduct live ([] : List (State → Except Cause (Value × State)))
      (fun _ _ => .ok (value, next)) state =
      .error none := by
  rw [guardedProduct_empty]
  exact guardedGeneration_revised live state next value before after

/-- A packing error is not replaced by a source check or a fabricated product. -/
theorem guardedProduct_packing_cause (live : State → Bool) (state : State) (cause : Cause)
    (before : live state = true) :
    guardedProduct live ([] : List (State → Except Cause (Value × State)))
      (fun _ _ => (.error cause : Except Cause (Output × State))) state = .error (some cause) := by
  rw [guardedProduct_empty]
  exact guardedGeneration_cause live state cause before

/-- Stable fields preserve their exact order and values in the shared evaluator. -/
theorem guardedStages_constant {Cause : Type u} (live : State → Bool) (state : State)
    (values : List Value) (before : live state = true) :
    guardedStages (Cause := Cause) live (values.map (fun value => fun _ => .ok (value, state))) state =
      .ok (values, state) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp [guardedStages, guardedGeneration_state live state state value before before, ih]

/-- Shared natural measures preserve the original sum without another typed fold. -/
theorem guardedProduct_sum {Cause : Type u} (live : State → Bool) (state : State)
    (values : List Nat) (before : live state = true) :
    guardedProduct (Cause := Cause) live (values.map (fun value => fun _ => .ok (value, state)))
      (fun values state => .ok (values.sum, state)) state = .ok (values.sum, state) := by
  simp [guardedProduct, before, guardedStages_constant live state values before, guardedGeneration]

/-- Fixed product fields declare their leaves before any draw. Identity
deduplication assumes pure, truthful observers, as in `mergeSources`. -/
def productSources [DecidableEq Source] (fields : List (List Source)) : List Source :=
  fields.flatten.eraseDups

/-- Flattening and sharing leaves preserves the conjunction of every fixed field. -/
theorem productSources_current [DecidableEq Source] (live : Source → Bool)
    (fields : List (List Source)) :
    (productSources fields).all live = true ↔ fields.all (fun field => field.all live) = true := by
  simp only [productSources, List.all_eq_true, List.mem_eraseDups, List.mem_flatten]
  constructor
  · intro h field present source owned
    exact h source ⟨field, present, owned⟩
  · intro h source ⟨field, present, owned⟩
    exact h field present source owned

/-- One stale leaf in any fixed field makes the complete producer obsolete. -/
theorem productSources_stale [DecidableEq Source] (live : Source → Bool)
    (fields : List (List Source)) (field : List Source) (source : Source)
    (present : field ∈ fields) (owned : source ∈ field) (stale : live source = false) :
    (productSources fields).all live = false := by
  cases fresh : (productSources fields).all live with
  | false => rfl
  | true =>
    have all := (productSources_current live fields).mp fresh
    have yes := List.all_eq_true.mp (List.all_eq_true.mp all field present) source owned
    simp [stale] at yes

/-- The existing product evaluator suppresses every draw and pack even when the
obsolete source belongs to a later field. The declared directory is a premise. -/
theorem guardedProduct_sources_preflight [DecidableEq Source]
    (live : State → Source → Bool) (fields : List (List Source))
    (field : List Source) (source : Source) (state : State)
    (draws : List (State → Except Cause (Value × State)))
    (pack : List Value → State → Except Cause (Output × State))
    (present : field ∈ fields) (owned : source ∈ field) (stale : live state source = false) :
    guardedProduct (fun state => (productSources fields).all (live state)) draws pack state = .error none := by
  exact guardedProduct_preflight _ draws pack state
    (productSources_stale (live state) fields field source present owned stale)

/-- Nested fixed products retain the same finite source judgment. -/
theorem productSources_nested [DecidableEq Source] (live : Source → Bool)
    (left right : List (List Source)) :
    (productSources [productSources left, productSources right]).all live = true ↔
      (productSources (left ++ right)).all live = true := by
  simp only [productSources_current, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, List.all_append]

/-- Repeating a shared field does not manufacture new authority. -/
theorem productSources_shared [DecidableEq Source] (live : Source → Bool)
    (fields : List (List Source)) :
    (productSources (fields ++ fields)).all live = true ↔ (productSources fields).all live = true := by
  simp only [productSources_current, List.all_append, Bool.and_eq_true, and_self]

/-- No result row means no result producer is observed; an explicit common
function/domain owner still uses `guardedProduct_empty`. -/
theorem productSources_empty (live : Source → Bool) [DecidableEq Source] :
    (productSources ([] : List (List Source))).all live = true := by
  rfl

end LeanPoo.Functional.PropertyTesting
