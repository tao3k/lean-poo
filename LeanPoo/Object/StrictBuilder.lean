import LeanPoo.Object.Builder

/-!
An opt-in checked declaration program for object literals. It keeps Lean's
typed `do` notation while rejecting repeated direct methods and defaults
before object construction. The ordinary Builder remains available for
intentional ordered replacement.
-/

namespace LeanPoo.Object

universe u v

inductive Declaration.DuplicateError (Key : Type u) where
  | slot (key : Key)
  | default (key : Key)
  deriving Repr

structure Declaration.StrictBuilder (Key : Type u) (Value : Key → Type v)
    (α : Type) where
  run : Declaration Key Value →
    Except (Declaration.DuplicateError Key) (α × Declaration Key Value)

instance {Key : Type u} {Value : Key → Type v} :
    Monad (Declaration.StrictBuilder Key Value) where
  pure item := ⟨fun declaration => .ok (item, declaration)⟩
  bind program next := ⟨fun declaration => do
    let (item, updated) ← program.run declaration
    (next item).run updated⟩

def Declaration.StrictBuilder.build {Key : Type u} {Value : Key → Type v}
    (program : Declaration.StrictBuilder Key Value PUnit) :
    Except (Declaration.DuplicateError Key) (Declaration Key Value) := do
  let (_, declaration) ← program.run Declaration.empty
  return declaration

namespace Declaration.StrictBuilder

/-- A direct method name may appear only once in this program. -/
def slot {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (spec : SlotPayload Key Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  ⟨fun declaration =>
    if (declaration.slot key).isSome then
      .error (.slot key)
    else
      .ok (⟨⟩, declaration.withSlot key spec)⟩

def value {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (item : Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.constant (some item))

/-- A direct default name may appear only once, independently of methods. -/
def default {Key : Type u} {Value : Key → Type v} [DecidableEq Key]
    (key : Key) (item : Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  ⟨fun declaration =>
    if (declaration.default key).isSome then
      .error (.default key)
    else
      .ok (⟨⟩, declaration.withDefault key item)⟩

def modifyInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (change : Option (Value key) → Option (Value key)) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.computed fun _ inherited => change (inherited ()))

def focusInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (focus : Prototype.MonoLens (Value key) Part)
    (change : Part → Part) : Declaration.StrictBuilder Key Value PUnit :=
  modifyInherited key (Option.map (focus.modify change))

def skew {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] (key : Key)
    (focus : Prototype.SkewLens Inherited Required Provided
      (Prototype.Next (Option (Value key)))
      (Self Key Value) (Option (Value key)))
    (extension : Prototype.Proto Required Inherited Provided) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.computed (focus.focus extension))

end Declaration.StrictBuilder

end LeanPoo.Object
