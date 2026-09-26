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
