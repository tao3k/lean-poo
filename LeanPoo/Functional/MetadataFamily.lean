import LeanPoo.Prototype.CheckedMetaPrototype
import LeanPoo.Functional.Requirements

/-! Functional clients of the existing checked metadata/C3 construction.
An explicit slotwise closure witness connects retained factories to the actual
captured source program; arbitrary knots receive no fixed-point equation. -/
namespace LeanPoo.Functional
open Prototype

namespace MetadataFamily

/-- The source's constant three-slot metadata prototype has this explicit
closed record. Keeping it with its production layer needs no general knot. -/
def constantMetadata (function : MetaPrototype.Layer α) (supers precedence : List String) :
    MetaPrototype.Meta α :=
  let fields : MetaPrototype.MetaRecord α := { lookup := fun key => match key with
    | .function => some function
    | .supers => some supers
    | .precedence => some precedence }
  let layer := DelayedProto.compose (Object.recordSlotGen .function (fun _ _ => some function))
    (DelayedProto.compose (Object.recordSlotGen .supers (fun _ _ => some supers))
      (Object.recordSlotGen .precedence (fun _ _ => some precedence)))
  ⟨layer, Thunk.pure Record.empty, Thunk.pure fields⟩

theorem constantMetadata_closed (function : MetaPrototype.Layer α) (supers precedence : List String) :
    let metadata := constantMetadata function supers precedence
    metadata.prototype (Thunk.pure metadata.value) metadata.base = metadata.value := by
  apply congrArg (fun lookup => ({ lookup := lookup } : MetaPrototype.MetaRecord α))
  funext key
  cases key <;> simp [constantMetadata, Object.value, DelayedProto.compose, Object.recordSlotGen,
    Thunk.get, Record.empty]

end MetadataFamily

variable {Context Key : Type} {Value : Context → Key → Type}
abbrev FactoryRecord (Context Key : Type) (Value : Context → Key → Type) :=
  Record Key (fun key => Factory Context (fun context => Value context key))

namespace MetadataFamily

/-- Apply the captured source program to explicit final-self and inherited
factory records. The caller chooses the self; this does not tie a new knot. -/
def apply (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (self base : FactoryRecord Context Key Value) : Provider Context Key Value :=
  (plan.program (Thunk.pure self) (Thunk.pure base)).lookup

def prepareOpen (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (self base : FactoryRecord Context Key Value) (keys : List Key) :=
  Requirements.prepare (apply plan self base) keys

theorem prepareOpen_selected (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (self base : FactoryRecord Context Key Value) (keys : List Key)
    (factories : Requirements.Factories Context Value keys)
    (ready : prepareOpen plan self base keys = .ok factories) :
    Requirements.Selected (plan.program (Thunk.pure self) (Thunk.pure base)).lookup keys factories :=
  (Requirements.prepare_ok_iff _ _ _).mp ready

end MetadataFamily

/-- A caller-supplied family closes the exact admitted metadata program at
every capability key. The metadata plan and base remain type indices. -/
structure MetadataFamily (plan : MetaPrototype.Prepared (FactoryRecord Context Key Value))
    (base : FactoryRecord Context Key Value) where
  provider : Provider Context Key Value
  closed : ∀ key, (plan.program (Thunk.pure { lookup := provider }) (Thunk.pure base)).lookup key = provider key

namespace MetadataFamily
variable {plan : MetaPrototype.Prepared (FactoryRecord Context Key Value)}
  {base : FactoryRecord Context Key Value}

def production (family : MetadataFamily plan base) : FactoryRecord Context Key Value :=
  plan.program (Thunk.pure { lookup := family.provider }) (Thunk.pure base)

theorem production_lookup (family : MetadataFamily plan base) (key : Key) :
    family.production.lookup key = family.provider key := family.closed key

def prepare (family : MetadataFamily plan base) (keys : List Key) :=
  Requirements.prepare family.provider keys

/-- Complete retained tuples and first missing errors are those of the actual
captured own/parent production, at the declared closed self and base. -/
theorem prepare_source (family : MetadataFamily plan base) (keys : List Key) :
    family.prepare keys = Requirements.prepare family.production.lookup keys := by
  apply Requirements.prepare_congr
  intro key _
  exact (family.production_lookup key).symm

theorem selected_source (family : MetadataFamily plan base) (keys : List Key)
    (factories : Requirements.Factories Context Value keys)
    (ready : family.prepare keys = .ok factories) :
    Requirements.Selected family.production.lookup keys factories := by
  rw [family.prepare_source] at ready
  exact (Requirements.prepare_ok_iff _ _ _).mp ready

/-- An independently checked metadata revision preserves this consumer's
complete preparation exactly when its requested factories are equal. -/
theorem prepare_stable {otherPlan : MetaPrototype.Prepared (FactoryRecord Context Key Value)}
    {otherBase : FactoryRecord Context Key Value} (family : MetadataFamily plan base)
    (other : MetadataFamily otherPlan otherBase) (keys : List Key)
    (same : ∀ key ∈ keys, other.provider key = family.provider key) :
    other.prepare keys = family.prepare keys := Requirements.prepare_congr _ _ _ same

/-- Both the order and frozen metadata retain the source C3 derivation. -/
theorem frozen_order (family : MetadataFamily plan base) (order : List String)
    (source : C3.GraphDerivation plan.graph plan.root order) :
    plan.order = order ∧ plan.frozenMetadata.lookup .precedence = some order :=
  ⟨plan.order_unique order source, plan.frozen_order order source⟩

end MetadataFamily
end LeanPoo.Functional
