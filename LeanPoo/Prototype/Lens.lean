import LeanPoo.Prototype.Delayed

/-!
The generalized prototype constructor sketched in POOF Appendix B. A getter
selects the inherited method, a wrapper cooks one method fragment, and a
setter installs the result into the raw computation. The output is still an
ordinary delayed prototype and uses its existing composition semantics.
-/

namespace LeanPoo.Prototype

universe u v w x y

/-- Build a delayed prototype from a typed method lens and wrapper. -/
def lensGen {Self : Type u} {Raw : Type v}
    {InheritedMethod : Type w} {Method : Type x} {ResultMethod : Type y}
    (get : Raw → InheritedMethod)
    (set : ResultMethod → Raw → Raw)
    (wrap : Method → Thunk Self → Thunk InheritedMethod → ResultMethod)
    (method : Method) : DelayedProto Self Raw Raw :=
  fun self inherited =>
    let oldMethod := Thunk.mk fun _ => get inherited.get
    set (wrap method self oldMethod) inherited.get

end LeanPoo.Prototype
