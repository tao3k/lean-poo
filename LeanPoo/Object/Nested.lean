import LeanPoo.Object.Memo

/-!
A nested object is an ordinary typed slot value. These method fragments
extend its inherited object when the outer C4 resolver reaches the slot.
They use the same inner C4 composition operations as a top-level object.
-/

namespace LeanPoo.Object.Nested

universe u v w

/-- Extend an inherited inner object with an independently defined override.
The outer slot retains both absence and inner composition errors. -/
def plusWith {Outer : Type u} {Key : Type v} {Value : Key → Type w}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (override : Memoized Key Value) (name : String) :
    Prototype.SlotSpec Outer
      (Option (Except PlusWithError (Memoized Key Value))) :=
  .computed fun _ inherited =>
    (inherited ()).map fun result =>
      result.bind fun base => base.plusWith override name

/-- Extend an inherited inner object with an override already present in its
own C4 family. The outer slot retains inner composition errors. -/
def plus {Outer : Type u} {Key : Type v} {Value : Key → Type w}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name overrideName : String) :
    Prototype.SlotSpec Outer
      (Option (Except LeanPoo.CompositionError (Memoized Key Value))) :=
  .computed fun _ inherited =>
    (inherited ()).map fun result =>
      result.bind fun base => base.plus name overrideName

end LeanPoo.Object.Nested
