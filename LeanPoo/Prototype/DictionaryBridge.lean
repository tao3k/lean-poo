import LeanPoo.Prototype.FiniteFix
import LeanPoo.Prototype.Class

/-! Exact typed conversion between dictionary values and descriptor field
representations. The compiler supplies both inverses; prototype composition,
finite self unfolding and typed runtime descriptors use the same conversion. -/
namespace LeanPoo.Prototype
universe u v w x y z

/-- Preserve all data, functions and dependent proofs in both directions. -/
structure DictionaryBridge (Dictionary : Sort u) (Fields : Sort v) where
  toFields : Dictionary → Fields
  fromFields : Fields → Dictionary
  from_to : ∀ dictionary, fromFields (toFields dictionary) = dictionary
  to_from : ∀ fields, toFields (fromFields fields) = fields

namespace DictionaryBridge
variable {Dictionary : Type u} {Fields : Type v}

def identity (Dictionary : Type u) : DictionaryBridge Dictionary Dictionary :=
  ⟨id, id, fun _ => rfl, fun _ => rfl⟩

def inverse (bridge : DictionaryBridge Dictionary Fields) : DictionaryBridge Fields Dictionary :=
  ⟨bridge.fromFields, bridge.toFields, bridge.to_from, bridge.from_to⟩

def trans (first : DictionaryBridge Dictionary Fields) (next : DictionaryBridge Fields Target) :
    DictionaryBridge Dictionary Target :=
  ⟨fun value => next.toFields (first.toFields value),
    fun value => first.fromFields (next.fromFields value),
    fun value => by rw [next.from_to, first.from_to],
    fun value => by rw [first.to_from, next.to_from]⟩

/-- Compile dictionary-style self/inheritance into field-style prototypes. -/
def toPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : Proto A B C) : Proto AFields BFields CFields :=
  fun final inherited => result.toFields (prototype (self.fromFields final) (parent.fromFields inherited))

/-- Compile field-style self/inheritance back to the original dictionary type. -/
def fromPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : Proto AFields BFields CFields) : Proto A B C :=
  fun final inherited => result.fromFields (prototype (self.toFields final) (parent.toFields inherited))

theorem from_toPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : Proto A B C) :
    fromPrototype self parent result (toPrototype self parent result prototype) = prototype := by
  funext final inherited
  simp only [fromPrototype, toPrototype, self.from_to, parent.from_to, result.from_to]

theorem to_fromPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : Proto AFields BFields CFields) :
    toPrototype self parent result (fromPrototype self parent result prototype) = prototype := by
  funext final inherited
  simp only [fromPrototype, toPrototype, self.to_from, parent.to_from, result.to_from]

theorem toPrototype_apply (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : Proto A B C) (final : A) (inherited : B) :
    toPrototype self parent result prototype (self.toFields final) (parent.toFields inherited) =
      result.toFields (prototype final inherited) := by
  simp only [toPrototype, self.from_to, parent.from_to]

/-- Actual child/parent composition commutes with the generated conversion. -/
theorem toPrototype_compose (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (middle : DictionaryBridge C CFields) (result : DictionaryBridge D DFields)
    (child : Proto A C D) (base : Proto A B C) :
    toPrototype self parent result (compose child base) =
      compose (toPrototype self middle result child) (toPrototype self parent middle base) := by
  funext final inherited
  simp only [toPrototype, compose, middle.from_to]

theorem toPrototype_identity (self : DictionaryBridge A AFields) (value : DictionaryBridge B BFields) :
    toPrototype self value value (LeanPoo.Prototype.identity : Proto A B B) = LeanPoo.Prototype.identity := by
  funext final inherited
  simp only [toPrototype, LeanPoo.Prototype.identity, value.to_from]

theorem toPrototype_constant (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (value : C) :
    toPrototype self parent result (constant value) = constant (result.toFields value) := rfl

/-- Every finite self observation is preserved; no unsafe knot is introduced. -/
theorem iterate_toPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (prototype : Proto A B A) (base : B) (seed : A) (depth : Nat) :
    FiniteFix.iterate (toPrototype self parent self prototype) (parent.toFields base) (self.toFields seed) depth =
      self.toFields (FiniteFix.iterate prototype base seed depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    simp only [FiniteFix.iterate, ih, toPrototype, self.from_to, parent.from_to]

theorem fixed_iff (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (prototype : Proto A B A) (base : B) (value : A) :
    toPrototype self parent self prototype (self.toFields value) (parent.toFields base) = self.toFields value ↔
      prototype value base = value := by
  rw [toPrototype_apply]
  constructor
  · intro equal
    have same := congrArg self.fromFields equal
    simpa only [self.from_to] using same
  · intro equal
    rw [equal]

/-- Mapping a delayed dictionary in both directions preserves the actual thunk. -/
theorem thunk_from_to (bridge : DictionaryBridge Dictionary Fields) (value : Thunk Dictionary) :
    (value.map bridge.toFields).map bridge.fromFields = value := by
  cases value with
  | mk execute =>
    apply congrArg Thunk.mk
    funext token
    cases token
    simp only [Thunk.map, Thunk.get, bridge.from_to]

theorem thunk_to_from (bridge : DictionaryBridge Dictionary Fields) (value : Thunk Fields) :
    (value.map bridge.fromFields).map bridge.toFields = value := bridge.inverse.thunk_from_to value

/-- Adapt delayed self/super without forcing either computation during conversion. -/
def toDelayedPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : DelayedProto A B C) : DelayedProto AFields BFields CFields :=
  fun final inherited => result.toFields (prototype (final.map self.fromFields) (inherited.map parent.fromFields))

def fromDelayedPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : DelayedProto AFields BFields CFields) : DelayedProto A B C :=
  fun final inherited => result.fromFields (prototype (final.map self.toFields) (inherited.map parent.toFields))

theorem from_toDelayedPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : DelayedProto A B C) :
    fromDelayedPrototype self parent result (toDelayedPrototype self parent result prototype) = prototype := by
  funext final inherited
  simp only [fromDelayedPrototype, toDelayedPrototype, self.thunk_from_to, parent.thunk_from_to, result.from_to]

theorem to_fromDelayedPrototype (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (result : DictionaryBridge C CFields) (prototype : DelayedProto AFields BFields CFields) :
    toDelayedPrototype self parent result (fromDelayedPrototype self parent result prototype) = prototype := by
  funext final inherited
  simp only [fromDelayedPrototype, toDelayedPrototype, self.thunk_to_from, parent.thunk_to_from, result.to_from]

theorem toDelayedPrototype_compose (self : DictionaryBridge A AFields) (parent : DictionaryBridge B BFields)
    (middle : DictionaryBridge C CFields) (result : DictionaryBridge D DFields)
    (child : DelayedProto A C D) (base : DelayedProto A B C) :
    toDelayedPrototype self parent result (DelayedProto.compose child base) =
      DelayedProto.compose (toDelayedPrototype self middle result child) (toDelayedPrototype self parent middle base) := by
  funext final inherited
  simp only [toDelayedPrototype, DelayedProto.compose, Thunk.map, Thunk.get, middle.from_to]

/-- Transport actual typed validation/display/default/codec operations. -/
def descriptor (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary) : Descriptor Fields :=
  { name := source.name
    accepts := fun value => source.accepts (bridge.fromFields value)
    display := fun value => source.display (bridge.fromFields value)
    prototypeValue := source.prototypeValue.map bridge.toFields
    json := source.json.map fun codec =>
      { encode := fun value => codec.encode (bridge.fromFields value)
        decode := fun raw => (codec.decode raw).map bridge.toFields } }

theorem descriptor_accepts (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary)
    (value : Dictionary) : (bridge.descriptor source).accepts (bridge.toFields value) = source.accepts value := by
  simp only [descriptor, bridge.from_to]

theorem descriptor_display (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary)
    (value : Dictionary) : (bridge.descriptor source).display (bridge.toFields value) = source.display value := by
  simp only [descriptor, bridge.from_to]

theorem descriptor_validate (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary)
    (value : Dictionary) : (bridge.descriptor source).validate (bridge.toFields value) =
      (source.validate value).map bridge.toFields := by
  simp only [Descriptor.validate, descriptor, bridge.from_to]
  split <;> rfl

theorem descriptor_encodeJson (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary)
    (value : Dictionary) : (bridge.descriptor source).encodeJson (bridge.toFields value) = source.encodeJson value := by
  simp only [Descriptor.encodeJson, descriptor_validate]
  cases validated : source.validate value with
  | error _ => rfl
  | ok accepted =>
    have equal : accepted = value := by
      unfold Descriptor.validate at validated
      split at validated <;> simp_all
    subst accepted
    cases found : source.json with
    | none => simp only [descriptor, found, Option.map, Except.map]
    | some codec =>
      simp only [descriptor, found, Option.map, Except.map]
      change Except.ok (codec.encode (bridge.fromFields (bridge.toFields value))) = Except.ok (codec.encode value)
      rw [bridge.from_to]

/-- Codec errors and runtime refinement refusals commute with conversion too. -/
theorem descriptor_decodeJson (bridge : DictionaryBridge Dictionary Fields) (source : Descriptor Dictionary)
    (raw : Lean.Json) : (bridge.descriptor source).decodeJson raw =
      (source.decodeJson raw).map bridge.toFields := by
  cases found : source.json with
  | none => simp only [Descriptor.decodeJson, descriptor, found, Option.map]; rfl
  | some codec =>
    simp only [Descriptor.decodeJson, descriptor, found, Option.map]
    cases decoded : codec.decode raw with
    | error error => rfl
    | ok value =>
      change (bridge.descriptor source).validate (bridge.toFields value) = (source.validate value).map bridge.toFields
      exact bridge.descriptor_validate source value

end DictionaryBridge
end LeanPoo.Prototype
