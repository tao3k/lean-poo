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

/-- A focused update may itself fail, as when a nested prototype extension
fails C4 validation. No source object is installed on failure. -/
def Lens.modifyM (lens : Lens Source Target Error)
    (change : Target → Except Error Target)
    (source : Source) : Except Error Source := do
  lens.set (← change (← lens.get source)) source

theorem Lens.modifyM_pure (lens : Lens Source Target Error)
    (change : Target → Target) (source : Source) :
    lens.modifyM (fun target => .ok (change target)) source =
      lens.modify change source := by
  rfl

/-- Adapt a lens's errors before composing independently defined layers. -/
def Lens.mapError (lens : Lens Source Target Error)
    (wrap : Error → OtherError) : Lens Source Target OtherError :=
  { get := fun source => (lens.get source).mapError wrap
    set := fun target source => (lens.set target source).mapError wrap }

theorem Lens.mapError_id (lens : Lens Source Target Error) :
    lens.mapError (fun error => error) = lens := by
  cases lens with
  | mk get set =>
      unfold Lens.mapError
      congr 1
      · funext source
        dsimp
        cases get source <;> rfl
      · funext target source
        dsimp
        cases set target source <;> rfl

theorem Lens.mapError_compose (lens : Lens Source Target Error)
    (first : Error → MiddleError) (second : MiddleError → OtherError) :
    (lens.mapError first).mapError second =
      lens.mapError (second ∘ first) := by
  cases lens with
  | mk get set =>
      unfold Lens.mapError
      congr 1
      · funext source
        dsimp
        cases get source <;> rfl
      · funext target source
        dsimp
        cases set target source <;> rfl

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

/-- Focus the paper's complete prototype specification: direct methods,
parent orders, and suffix policy. A topology edit is checked by C4 before a
new instance is returned; an unchanged topology keeps the compiled order. -/
def Lens.prototypeSpecification {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key] (name : String) :
    Lens (Memoized Key Value) (Specification Key Value) C4.Error :=
  { get := fun object =>
      match object.plan.schema.graph.findNode? name with
      | none => .error (.unknownNode name)
      | some node => .ok {
          declaration := (object.plan.schema.declaration name).getD
            Declaration.empty
          parentOrders := node.parentOrders
          suffix := node.suffix }
    set := fun specification object =>
      object.reviseSpecification name specification }

theorem Lens.prototypeSpecification_set {Key : Type u}
    {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name : String) (specification : Specification Key Value)
    (object : Memoized Key Value) :
    (Lens.prototypeSpecification name).set specification object =
      object.reviseSpecification name specification := rfl

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

/-- Focus one optional direct method inside a declaration. Removing it does
not remove inherited methods of the same key. -/
def Lens.directSlot {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key) :
    Lens (Declaration Key Value) (Option (SlotPayload Key Value key)) C4.Error :=
  { get := fun declaration => .ok (declaration.slot key)
    set := fun spec declaration => .ok <|
      match spec with
      | some method => declaration.withSlot key method
      | none => declaration.withoutSlot key }

/-- Focus one optional direct default within a declaration. -/
def Lens.directDefault {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key) :
    Lens (Declaration Key Value) (Option (Value key)) C4.Error :=
  { get := fun declaration => .ok (declaration.default key)
    set := fun value declaration => .ok <|
      match value with
      | some item => declaration.withDefault key item
      | none => declaration.withoutDefault key }

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
