import LeanPoo.Prototype.Compose

namespace LeanPoo.Prototype

/-- A typed function with an explicit bottom/error outcome. -/
abbrev CheckedFunction (Input Output : Type) := FixedFunction Input (Except String Output)

def CheckedFunction.bottom : CheckedFunction Input Output :=
  FixedFunction.ofFun fun _ => .error "bottom"

/-- Close the source prototype-list constructor over an explicit bottom base. -/
unsafe def CheckedFunction.instance
    (layers : List (Proto (CheckedFunction Input Output) (CheckedFunction Input Output)
      (CheckedFunction Input Output))) : CheckedFunction Input Output :=
  instantiateAll layers CheckedFunction.bottom

theorem CheckedFunction.bottom_apply (input : Input) :
    (CheckedFunction.bottom : CheckedFunction Input Output) input = .error "bottom" := rfl

/-- Appendix D fix--0: rebuild the prototype at each application. This is an
executable contrast to shared instantiation, not the recommended default. -/
unsafe def rebuildingFix
    (prototype : Proto (FixedFunction Input Output) Parent (FixedFunction Input Output))
    (base : Parent) : FixedFunction Input Output :=
  let rec apply (input : Input) : Output :=
    (prototype (FixedFunction.ofFun apply) base) input
  FixedFunction.ofFun apply

end LeanPoo.Prototype
