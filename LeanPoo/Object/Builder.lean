import LeanPoo.Object.Schema
import LeanPoo.Prototype.SkewLens

/-!
Lean's `do` notation provides an ordered, typed declaration surface without
introducing a second object syntax or evaluator. Each builder step calls the
same persistent `Declaration` operation used by the rest of the library.
-/

namespace LeanPoo.Object

universe u v

/-- Pure state construction of one ordered typed declaration. -/
abbrev Declaration.Builder (Key : Type u) (Value : Key → Type v) :=
  StateM (Declaration Key Value)

/-- Apply a reusable declaration program to an existing direct declaration. -/
def Declaration.buildOn {Key : Type u} {Value : Key → Type v}
    (declaration : Declaration Key Value)
    (program : Declaration.Builder Key Value PUnit) : Declaration Key Value :=
  (program.run declaration).2

/-- Run a pure declaration program from the empty declaration. -/
def Declaration.build {Key : Type u} {Value : Key → Type v}
    (program : Declaration.Builder Key Value PUnit) : Declaration Key Value :=
  Declaration.buildOn Declaration.empty program

namespace Declaration.Builder

/-- Install or replace a direct value at its first declaration position. -/
def value {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (item : Value key) : Declaration.Builder Key Value PUnit :=
  modify fun declaration => declaration.withValue key item

/-- Supply the inherited base for a slot without defining its method. -/
def default {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (item : Value key) : Declaration.Builder Key Value PUnit :=
  modify fun declaration => declaration.withDefault key item

/-- Drop a direct method so resolution can expose an inherited method. -/
def eraseSlot {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) : Declaration.Builder Key Value PUnit :=
  modify fun declaration => declaration.withoutSlot key

/-- Drop a direct default without changing ancestor declarations. -/
def eraseDefault {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) : Declaration.Builder Key Value PUnit :=
  modify fun declaration => declaration.withoutDefault key

/-- Install a method whose final self and inherited computation stay open. -/
def slot {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (spec : SlotPayload Key Value key) :
    Declaration.Builder Key Value PUnit :=
  modify fun declaration => declaration.withSlot key spec

/-- Update the current direct declaration with an ordinary Lean function. -/
def edit {Key : Type u} {Value : Key → Type v}
    (change : Declaration Key Value → Declaration Key Value) :
    Declaration.Builder Key Value PUnit :=
  modify change

/-- Transform an inherited result without forcing it before the slot is read. -/
def modifyInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (change : Option (Value key) → Option (Value key)) :
    Declaration.Builder Key Value PUnit :=
  slot key (.computed fun _ inherited => change (inherited ()))

/-- Lift a focused value change into a delayed inherited slot method. -/
def focusInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (focus : Prototype.MonoLens (Value key) Part)
    (change : Part → Part) : Declaration.Builder Key Value PUnit :=
  modifyInherited key (Option.map (focus.modify change))

/-- Install any paper-style skew extension as one C4 slot method. The lens
controls both the final-self view and when to force inherited computation. -/
def skew {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (focus : Prototype.SkewLens Inherited Required Provided
      (Prototype.Next (Option (Value key)))
      (Self Key Value) (Option (Value key)))
    (extension : Prototype.Proto Required Inherited Provided) :
    Declaration.Builder Key Value PUnit :=
  slot key (.computed (focus.focus extension))

end Declaration.Builder

theorem Declaration.buildOn_value {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (declaration : Declaration Key Value)
    (key : Key) (item : Value key) :
    Declaration.buildOn declaration (Declaration.Builder.value key item) =
      declaration.withValue key item := rfl

theorem Declaration.buildOn_modifyInherited {Key : Type u}
    {Value : Key → Type v} [DecidableEq Key]
    (declaration : Declaration Key Value) (key : Key)
    (change : Option (Value key) → Option (Value key)) :
    Declaration.buildOn declaration
      (Declaration.Builder.modifyInherited key change) =
      declaration.withSlot key
        (.computed fun _ inherited => change (inherited ())) := rfl

theorem Declaration.buildOn_focusInherited {Key : Type u}
    {Value : Key → Type v} [DecidableEq Key]
    (declaration : Declaration Key Value) (key : Key)
    (focus : Prototype.MonoLens (Value key) Part)
    (change : Part → Part) :
    Declaration.buildOn declaration
      (Declaration.Builder.focusInherited key focus change) =
      declaration.withSlot key
        (.computed fun _ inherited =>
          Option.map (focus.modify change) (inherited ())) := rfl

theorem Declaration.buildOn_skew {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (declaration : Declaration Key Value) (key : Key)
    (focus : Prototype.SkewLens Inherited Required Provided
      (Prototype.Next (Option (Value key)))
      (Self Key Value) (Option (Value key)))
    (extension : Prototype.Proto Required Inherited Provided) :
    Declaration.buildOn declaration
      (Declaration.Builder.skew key focus extension) =
      declaration.withSlot key (.computed (focus.focus extension)) := rfl

end LeanPoo.Object
