import LeanPoo.Object.Memo
import LeanPoo.Prototype.Object

/-!
The typed C4 slot plan is an instance of the paper's delayed prototype
construction. The plan remains the only slot evaluator; this module merely
ties its open self reference into a first-class object.
-/

namespace LeanPoo.Object

universe u v

/-- Interpret a validated C4 plan as a delayed prototype over typed slots. -/
def Plan.toDelayedProto (plan : Plan Key Value) :
    Prototype.DelayedProto (Self Key Value) (Self Key Value) (Self Key Value) :=
  fun self _ => fun key => plan.resolve key self.get

/-- Construct the paper's instance/prototype pair from a typed C4 plan. -/
unsafe def Plan.toFirstClassObject (plan : Plan Key Value) :
    Prototype.Object (Self Key Value) (Self Key Value) :=
  Prototype.Object.ofPrototype plan.toDelayedProto
    (Thunk.pure (fun _ => none))

/-- Project an executable C4 object into the paper's first-class pair.
The current instance keeps its per-slot call-by-need cells; the retained
prototype still describes the plan and can be composed with a new final self. -/
def Memoized.toFirstClassObject {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) :
    Prototype.Object (Self Key Value) (Self Key Value) :=
  { prototype := object.plan.toDelayedProto
    base := Thunk.pure (fun _ => none)
    result := Thunk.pure (fun key => object.read key) }

end LeanPoo.Object
