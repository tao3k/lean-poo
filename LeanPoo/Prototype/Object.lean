import LeanPoo.Prototype.Computation

/-!
POOF's first-class object: an instance stays paired with the prototype that
produced it. The instance is delayed, so retaining the prototype does not
force its value.
-/

namespace LeanPoo.Prototype

universe u v

/-- A delayed record slot for first-class objects. Neither final self nor the
inherited slot is forced while assembling the record; a later lookup chooses
when to use either computation. This is the typed counterpart of the paper's
object-level slot generator. -/
def Object.recordSlotGen {Key : Type} {Value : Key → Type} [DecidableEq Key]
    (key : Key)
    (compute : Thunk (Record Key Value) → Thunk (Option (Value key)) →
      Option (Value key)) :
    DelayedProto (Record Key Value) (Record Key Value) (Record Key Value) :=
  fun self inherited =>
    { lookup := fun query =>
        if same : query = key then
          same.symm ▸ compute self
            (Thunk.mk fun _ => inherited.get.lookup key)
        else inherited.get.lookup query }

/-- A reusable delayed prototype and one of its lazy instances. -/
structure Object (Self : Type u) (Parent : Type v) where
  prototype : DelayedProto Self Parent Self
  base : Thunk Parent
  result : Thunk Self

/-- Form the paper's object pair by tying one delayed fixed point. -/
unsafe def Object.ofPrototype (prototype : DelayedProto Self Parent Self)
    (base : Thunk Parent) : Object Self Parent :=
  ⟨prototype, base, DelayedProto.instantiate prototype base⟩

/-- Construct an object from a heterogeneous, type-checked inheritance chain. -/
unsafe def Object.ofChain (chain : DelayedProto.Chain Self Parent Self)
    (base : Thunk Parent) : Object Self Parent :=
  Object.ofPrototype chain.toProto base

/-- Extend an existing object with a typed chain of prototype layers. -/
unsafe def Object.extendChain (object : Object Self Parent)
    (layers : DelayedProto.Chain Self Self Self) : Object Self Parent :=
  Object.ofPrototype (DelayedProto.compose layers.toProto object.prototype)
    object.base

/-- A derived object keeps the original base and composes a child prototype
before creating a fresh lazy instance. -/
unsafe def Object.extend (object : Object Self Parent)
    (child : DelayedProto Self Self Self) : Object Self Parent :=
  object.extendChain (.cons child .nil)

/-- Mix two already-instantiated objects by reusing their retained
prototypes, then close a new fixed point over the parent's base. -/
unsafe def Object.mix (child : Object Self Self)
    (parent : Object Self Parent) : Object Self Parent :=
  parent.extend child.prototype

/-- Observe this object's instance without discarding its prototype. -/
def Object.value (object : Object Self Parent) : Self :=
  object.result.get

end LeanPoo.Prototype
