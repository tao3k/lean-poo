import LeanPoo.Object.Resolve

/-!
Index each declaration once, then resolve slots through constant-time typed
lookups in C4 order. The index is an implementation of the existing resolver,
not a second source of slot semantics.
-/

namespace LeanPoo.Object

universe u v

structure IndexedLayer (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  defaults : Std.DHashMap Key Value
  slots : Std.DHashMap Key (SlotPayload Key Value)

def IndexedLayer.ofDeclaration {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (declaration : Declaration Key Value) :
    IndexedLayer Key Value :=
  ⟨Entry.toMap declaration.defaults, Entry.toMap declaration.slots⟩

structure IndexedPlan (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  plan : Plan Key Value
  layers : List (Option (IndexedLayer Key Value))
  aligned : layers = plan.precedence.reverse.map (fun name =>
    (plan.schema.declaration name).map IndexedLayer.ofDeclaration)

def Plan.index {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] (plan : Plan Key Value) :
    IndexedPlan Key Value :=
  ⟨plan, plan.precedence.reverse.map (fun name =>
    (plan.schema.declaration name).map IndexedLayer.ofDeclaration), rfl⟩

private def IndexedLayer.defaultStep {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) (inherited : Option (Value key))
    (layer : Option (IndexedLayer Key Value)) : Option (Value key) :=
  match layer with
  | none => inherited
  | some layer =>
      match layer.defaults.get? key with
      | none => inherited
      | some value => some value

private def IndexedLayer.methodStep {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key)
    (inherited : Prototype.Method (Self Key Value) (Option (Value key)))
    (layer : Option (IndexedLayer Key Value)) :
    Prototype.Method (Self Key Value) (Option (Value key)) :=
  match layer with
  | none => inherited
  | some layer =>
      match layer.slots.get? key with
      | none => inherited
      | some spec => Prototype.Method.compose spec.toMethod inherited

private theorem IndexedLayer.defaultStep_ofDeclaration
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) (inherited : Option (Value key))
    (declaration : Option (Declaration Key Value)) :
    IndexedLayer.defaultStep key inherited
      (declaration.map IndexedLayer.ofDeclaration) =
    match declaration with
    | none => inherited
    | some declaration =>
        match declaration.default key with
        | none => inherited
        | some value => some value := by
  cases declaration with
  | none => rfl
  | some declaration =>
      simp [IndexedLayer.defaultStep, IndexedLayer.ofDeclaration,
        Declaration.default, Entry.toMap_get?]

private theorem IndexedLayer.methodStep_ofDeclaration
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key)
    (inherited : Prototype.Method (Self Key Value) (Option (Value key)))
    (declaration : Option (Declaration Key Value)) :
    IndexedLayer.methodStep key inherited
      (declaration.map IndexedLayer.ofDeclaration) =
    match declaration with
    | none => inherited
    | some declaration =>
        match declaration.slot key with
        | none => inherited
        | some spec => Prototype.Method.compose spec.toMethod inherited := by
  cases declaration with
  | none => rfl
  | some declaration =>
      simp [IndexedLayer.methodStep, IndexedLayer.ofDeclaration,
        Declaration.slot, Entry.toMap_get?]
      rfl

def IndexedPlan.resolve {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value)
    (key : Key) (self : Self Key Value) : Option (Value key) :=
  let default := indexed.layers.foldl (IndexedLayer.defaultStep key) none
  let method := indexed.layers.foldl (IndexedLayer.methodStep key)
    Prototype.Method.identity
  method self (fun _ => default)

theorem IndexedPlan.resolve_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (indexed : IndexedPlan Key Value) (key : Key)
    (self : Self Key Value) :
    indexed.resolve key self = indexed.plan.resolve key self := by
  unfold IndexedPlan.resolve Plan.resolve Plan.compileSlotForward
  rw [indexed.aligned]
  simp only [List.foldl_map, IndexedLayer.defaultStep_ofDeclaration,
    IndexedLayer.methodStep_ofDeclaration]
  rfl

theorem Plan.index_resolve_sound {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (plan : Plan Key Value) (key : Key) (self : Self Key Value) :
    (plan.index).resolve key self = plan.resolve key self :=
  (plan.index).resolve_sound key self

end LeanPoo.Object
