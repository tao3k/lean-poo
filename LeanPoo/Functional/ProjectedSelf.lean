import LeanPoo.Functional.ConstructionCache

/-! Lossy cooked self, with only the observations actually used by a finite
construction preserved. Existing lens compilation, locality and closure remain
authoritative. This advances generalized-prototype future work. -/
namespace LeanPoo.Functional.ProjectedSelf
open GeneralizedGraph
variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

/-- `view` is a partial observation decoder, not an inverse of cooking. Hidden
slots may differ arbitrarily, including their presence and failure outcomes. -/
structure Projection (Key : Type) (Value : Key → Type) (Cooked : Type) where
  visible : List Key
  cook : State Key Value → Cooked
  view : Cooked → State Key Value
  preserves : ∀ raw key, key ∈ visible → view (cook raw) key = raw key

variable (projection : Projection Key Value Cooked)

/-- Changing representation of retained observations reuses the existing exact
bridge. Loss occurs before this bridge, which does not reconstruct hidden raw. -/
def Projection.represent (bridge : Prototype.DictionaryBridge Cooked Other) : Projection Key Value Other where
  visible := projection.visible
  cook := bridge.toFields ∘ projection.cook
  view := projection.view ∘ bridge.fromFields
  preserves := by intro raw key member; simp [bridge.from_to, projection.preserves raw key member]

structure Checked (spec : Declaration Key Value) : Type where
  covers : ∀ key dep, dep ∈ spec.reads key → dep ∈ projection.visible

/-- Coverage includes presence, negative-capability and all conditional reads.
The ordinary scheduler separately rejects opaque bodies and cycles. -/
def check (spec : Declaration Key Value) : Except Unit (Checked projection spec) :=
  if covered : spec.keys.all (fun key => (spec.reads key).all (fun dep => decide (dep ∈ projection.visible))) = true then
    .ok ⟨by
      intro key dep member
      have active : key ∈ spec.keys := by
        by_cases active : key ∈ spec.keys
        · exact active
        · simp [Declaration.reads, Declaration.footprint, active] at member
      exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp covered key active) dep member)⟩
  else .error ()

theorem check_ok_iff (spec : Declaration Key Value) :
    (∃ checked, check projection spec = .ok checked) ↔
      ∀ key dep, dep ∈ spec.reads key → dep ∈ projection.visible := by
  constructor
  · rintro ⟨checked,_⟩; exact checked.covers
  · intro covers
    have covered : spec.keys.all (fun key => (spec.reads key).all (fun dep => decide (dep ∈ projection.visible))) = true := by
      apply List.all_eq_true.mpr
      intro key _
      apply List.all_eq_true.mpr
      intro dep member
      exact decide_eq_true (covers key dep member)
    exact ⟨⟨covers⟩,by simp [check, covered]⟩

def protocol (spec : Declaration Key Value) := spec.protocol.reindexSelf projection.view projection.cook

/-- Whole raw steps agree although view(cook raw) need not equal raw. -/
theorem step (spec : Declaration Key Value) (checked : Checked projection spec)
    (known : ∀ key, (spec.footprint key).unknown = false) :
    (protocol projection spec).step spec.keys = spec.protocol.step spec.keys := by
  funext self base
  unfold protocol Prototype.Generalized.Protocol.step
  rw [Prototype.Generalized.Protocol.assemble_reindexSelf]
  change spec.protocol.step spec.keys (projection.view (projection.cook self)) base =
    spec.protocol.step spec.keys self base
  funext key
  rw [spec.assemble_apply, spec.assemble_apply]
  split
  · exact spec.locality key (known key) _ _ (fun dep member => projection.preserves self dep (checked.covers key dep member))
  · rfl

/-- Materialized raw values are reused directly; no second construction occurs. -/
def close (spec : Declaration Key Value) (checked : Checked projection spec)
    (known : ∀ key, (spec.footprint key).unknown = false) (cache : ConstructionCache.Cache spec) :
    Prototype.Generalized.Closed (protocol projection spec) spec.keys spec.base :=
  ⟨cache.closed.raw,by rw [step projection spec checked known]; exact cache.closed.fixed⟩

@[simp] theorem close_raw (spec : Declaration Key Value) (checked : Checked projection spec)
    (known) (cache : ConstructionCache.Cache spec) : (close projection spec checked known cache).raw = cache.closed.raw := rfl

omit [DecidableEq Key] in
theorem represent_interface (bridge : Prototype.DictionaryBridge Cooked Other)
    (raw : State Key Value) : (projection.represent bridge).cook raw = bridge.toFields (projection.cook raw) := rfl

end LeanPoo.Functional.ProjectedSelf
