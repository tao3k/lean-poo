import LeanPoo.Object.Memo

/-!
A Lean-native generic method chooses a method value from an object or an
explicit descriptor, then invokes it with a receiver. Method selection is
ordinary typed data rather than a runtime MOP or a second slot evaluator.
-/

namespace LeanPoo.Object

universe u v w x

structure Generic (Receiver : Type u) (Method : Type v)
    (Args : Type w) (Result : Type x) where
  select : Receiver → Option Method
  invoke : Method → Receiver → Args → Result
  fallback : Receiver → Args → Result

def Generic.call (generic : Generic Receiver Method Args Result)
    (receiver : Receiver) (args : Args) : Result :=
  match generic.select receiver with
  | some method => generic.invoke method receiver args
  | none => generic.fallback receiver args

/-- Dispatch through a typed slot of a C4 object's current lazy instance. -/
def Generic.fromSlot {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (key : Key)
    (invoke : Value key → Memoized Key Value → Args → Result)
    (fallback : Memoized Key Value → Args → Result) :
    Generic (Memoized Key Value) (Value key) Args Result :=
  { select := fun object => object.read key, invoke, fallback }

/-- Dispatch through a descriptor associated with the receiver. The method
selector determines which type-level operation applies; no dynamic type map
or macro expansion is required. -/
def Generic.fromType (typeOf : Receiver → Descriptor)
    (select : Descriptor → Option Method)
    (invoke : Method → Receiver → Args → Result)
    (fallback : Receiver → Args → Result) :
    Generic Receiver Method Args Result :=
  { select := fun receiver => select (typeOf receiver)
    invoke
    fallback }

end LeanPoo.Object
