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

private structure StrictState (Key : Type u) (Value : Key → Type v)
    [BEq Key] [Hashable Key] where
  slotsRev : List (Entry Key (SlotPayload Key Value)) := []
  defaultsRev : List (Entry Key Value) := []
  seenSlots : Std.HashSet Key
  seenDefaults : Std.HashSet Key

structure Declaration.StrictBuilder (Key : Type u) (Value : Key → Type v)
    [BEq Key] [Hashable Key]
    (α : Type) where
  run : StrictState Key Value →
    Except (Declaration.DuplicateError Key) (α × StrictState Key Value)

instance {Key : Type u} {Value : Key → Type v}
    [BEq Key] [Hashable Key] :
    Monad (Declaration.StrictBuilder Key Value) where
  pure item := ⟨fun declaration => .ok (item, declaration)⟩
  bind program next := ⟨fun declaration => do
    let (item, updated) ← program.run declaration
    (next item).run updated⟩

def Declaration.StrictBuilder.build {Key : Type u} {Value : Key → Type v}
    [BEq Key] [Hashable Key]
    (program : Declaration.StrictBuilder Key Value PUnit) :
    Except (Declaration.DuplicateError Key) (Declaration Key Value) := do
  let (_, state) ← program.run {
    slotsRev := [], defaultsRev := [], seenSlots := {}, seenDefaults := {} }
  return ⟨state.slotsRev.reverse, state.defaultsRev.reverse⟩

namespace Declaration.StrictBuilder

/-- A direct method name may appear only once in this program. -/
def slot {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key) (spec : SlotPayload Key Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  ⟨fun state =>
    if state.seenSlots.contains key then
      .error (.slot key)
    else
      .ok (⟨⟩, { state with
        slotsRev := ⟨key, spec, fun _ => inferInstance⟩ :: state.slotsRev
        seenSlots := state.seenSlots.insert key })⟩

def value {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key) (item : Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.constant (some item))

/-- A direct default name may appear only once, independently of methods. -/
def default {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key) (item : Value key) :
    Declaration.StrictBuilder Key Value PUnit :=
  ⟨fun state =>
    if state.seenDefaults.contains key then
      .error (.default key)
    else
      .ok (⟨⟩, { state with
        defaultsRev := ⟨key, item, fun _ => inferInstance⟩ :: state.defaultsRev
        seenDefaults := state.seenDefaults.insert key })⟩

def modifyInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key)
    (change : Option (Value key) → Option (Value key)) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.computed fun _ inherited => change (inherited ()))

def focusInherited {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key)
    (focus : Prototype.MonoLens (Value key) Part)
    (change : Part → Part) : Declaration.StrictBuilder Key Value PUnit :=
  modifyInherited key (Option.map (focus.modify change))

def skew {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    [LawfulHashable Key]
    (key : Key)
    (focus : Prototype.SkewLens Inherited Required Provided
      (Prototype.Next (Option (Value key)))
      (Self Key Value) (Option (Value key)))
    (extension : Prototype.Proto Required Inherited Provided) :
    Declaration.StrictBuilder Key Value PUnit :=
  slot key (.computed (focus.focus extension))

end Declaration.StrictBuilder

end LeanPoo.Object
