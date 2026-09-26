import LeanPoo.Prototype.Object

namespace LeanPoo.Examples.FirstClassObject

open LeanPoo.Prototype

/-- A first-class object retains the prototype used to create its value. -/
unsafe def baseObject : Object Nat Nat :=
  Object.ofPrototype (fun _ parent => parent.get + 1) (Thunk.pure 2)

/-- Inheritance works after the base object has already been instantiated. -/
unsafe def derivedObject : Object Nat Nat :=
  baseObject.extend (fun _ inherited => 2 * inherited.get)

/-- An instantiated object can itself serve as the inheriting prototype. -/
unsafe def multiplierObject : Object Nat Nat :=
  Object.ofPrototype (fun _ inherited => 2 * inherited.get) (Thunk.pure 1)

unsafe def mixedObject : Object Nat Nat :=
  multiplierObject.mix baseObject

/-- The intermediate Bool is checked statically while the object remains
first-class and keeps its composed prototype for later inheritance. -/
unsafe def typedChainObject : Object Nat Nat :=
  let threshold : DelayedProto Nat Nat Bool :=
    fun _ inherited => inherited.get > 2
  let choose : DelayedProto Nat Bool Nat :=
    fun _ inherited => if inherited.get then 10 else 0
  baseObject.extendChain (.cons choose (.cons threshold .nil))

#eval (baseObject.value, derivedObject.value)
#eval (multiplierObject.value, mixedObject.value)
#eval typedChainObject.value

end LeanPoo.Examples.FirstClassObject
