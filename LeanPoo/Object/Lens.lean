import LeanPoo.Object.Memo

/-!
A typed functional lens for object values. Setting a slot returns a new C4
object; it does not mutate the source instance or introduce another evaluator.
-/

namespace LeanPoo.Object

universe u v w x

structure Lens (Source : Type u) (Target : Type v) (Error : Type w) where
  get : Source → Except Error Target
  set : Target → Source → Except Error Source

def Lens.modify (lens : Lens Source Target Error)
    (change : Target → Target) (source : Source) : Except Error Source := do
  lens.set (change (← lens.get source)) source

/-- Access the outer focus, then the inner focus. -/
def Lens.compose (outer : Lens Source Target Error)
    (inner : Lens Target Middle Error) : Lens Source Middle Error :=
  { get := fun source => do
      inner.get (← outer.get source)
    set := fun value source => do
      let middle ← outer.get source
      let updated ← inner.set value middle
      outer.set updated source }

/-- Focus on one prototype's direct specification. Updating it rebuilds the
instance from a revised plan; the source instance remains unchanged. -/
def Lens.specification {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] (name : String) :
    Lens (Memoized Key Value) (Declaration Key Value) C4.Error :=
  { get := fun object =>
      if (object.plan.schema.graph.findNode? name).isSome then
        .ok ((object.plan.schema.declaration name).getD Declaration.empty)
      else .error (.unknownNode name)
    set := fun declaration object =>
      object.reviseDeclaration name (fun _ => declaration) }

theorem Lens.specification_set {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (declaration : Declaration Key Value)
    (object : Memoized Key Value) :
    (Lens.specification name).set declaration object =
      object.reviseDeclaration name (fun _ => declaration) := rfl

/-- Modifying a known specification is precisely the existing declaration
revision, so it inherits the plan's C4-preservation guarantee. -/
theorem Lens.specification_modify {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (change : Declaration Key Value → Declaration Key Value)
    (object : Memoized Key Value)
    (known : (object.plan.schema.graph.findNode? name).isSome = true) :
    (Lens.specification name).modify change object =
      object.reviseDeclaration name change := by
  simp [Lens.modify, Lens.specification, known]
  rfl

theorem Lens.specification_modify_preserves_precedence
    {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (change : Declaration Key Value → Declaration Key Value)
    (object revised : Memoized Key Value)
    (known : (object.plan.schema.graph.findNode? name).isSome = true)
    (result : (Lens.specification name).modify change object = .ok revised) :
    revised.plan.precedence = object.plan.precedence := by
  rw [Lens.specification_modify name change object known] at result
  unfold Memoized.reviseDeclaration at result
  cases equation : object.plan.reviseDeclaration name change with
  | error error =>
    rw [equation] at result
    change Except.error error = Except.ok revised at result
    cases result
  | ok plan =>
    rw [equation] at result
    change Except.ok (object.rebuild plan) = Except.ok revised at result
    cases result
    rw [Memoized.rebuild_plan]
    exact Plan.reviseDeclaration_preserves_precedence
      object.plan name change plan equation

inductive SlotLensError (Key : Type u) where
  | lookup (error : LookupError Key)
  | c4 (error : C4.Error)
  deriving Repr

/-- A total getter for a declared typed slot and a persistent C4 setter.
The setter revises the current root declaration, then creates a fresh lazy
instance. Existing instances retain their original values. -/
def Lens.slot {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key) : Lens (Memoized Key Value) (Value key) (SlotLensError Key) :=
  { get := fun object => object.ref key |>.mapError .lookup
    set := fun value object =>
      object.reviseSlot object.plan.root key (.constant (some value))
        |>.mapError .c4 }

end LeanPoo.Object
