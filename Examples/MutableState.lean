import LeanPoo.Prototype.MutableRecordSemantics

namespace LeanPoo.Examples.MutableState
open Prototype
open MutableRecord

def base : Storage := fromValues [("x", .integer 0)]

def interrupted : Specification :=
  .compose (.slot "later" (constant (.integer 9)))
    (.compose (.error "stop") (.slot "x" (constant (.integer 5))))

def status : Except String α → String
  | .ok _ => "ok" | .error message => s!"error: {message}"

def run : IO Unit := do
  let (retained, outcome) := interrupted.transition base
  IO.println s!"pure: {status outcome}, x={repr (readPure retained 3 "x")}, later={repr (readPure retained 3 "later")}"
  let mutable ← create base
  let before ← mutable.snapshot
  let outcome ← interrupted.apply mutable
  IO.println s!"mutable: {status outcome}, x={repr (← mutable.read 3 "x")}; snapshot x={repr (readPure before 3 "x")}"
  let linear ← LinearState.create base
  let alias := linear
  let outcome ← interrupted.applyLinear linear
  let current ← IO.ofExcept (← alias.read)
  IO.println s!"linear: {status outcome}, retained alias x={repr (readPure current 3 "x")}"
  let next ← IO.ofExcept (← (Specification.slot "y" (constant (.integer 2))).applyLinear alias)
  let result ← IO.ofExcept (← next.read)
  IO.println s!"resumed: y={repr (readPure result 3 "y")}; old alias={status (← linear.read)}"

#eval run
end LeanPoo.Examples.MutableState
