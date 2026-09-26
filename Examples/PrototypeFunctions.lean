import LeanPoo.Prototype.MVP

namespace LeanPoo.Examples.PrototypeFunctions

open LeanPoo.Prototype

/-- A prototype can incrementally specify an arbitrary function, not only
a record or object. Negative inputs recurse through the final function. -/
def evenFunction : Proto (FixedFunction Int Int)
    (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun self inherited => FixedFunction.ofFun fun x =>
    if x < 0 then self (-x) else inherited x

def cubeResult : Proto (FixedFunction Int Int)
    (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun _ inherited => FixedFunction.ofFun fun x =>
    let y := inherited x
    y * y * y

/-- The terminal prototype supplies identity; the external base is unused. -/
unsafe def absoluteCube : FixedFunction Int Int :=
  let terminal : Proto (FixedFunction Int Int)
      (FixedFunction Int Int) (FixedFunction Int Int) :=
    constant (FixedFunction.ofFun fun x : Int => x)
  instantiate
    (compose evenFunction (compose cubeResult terminal))
    (FixedFunction.ofFun fun _ => 0)

#eval ([-3, -2, 0, 1, 3] : List Int).map absoluteCube

end LeanPoo.Examples.PrototypeFunctions
