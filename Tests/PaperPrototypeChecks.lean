import LeanPoo.Prototype.Record
import LeanPoo.Prototype.Object
import LeanPoo.Prototype.Class
open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperPrototypeChecks

inductive Key where | x | y | z deriving DecidableEq
private abbrev Value : Key → Type
  | .x | .y => Int
  | .z => Int × Int
private abbrev Rec := Record Key Value
private abbrev Layer := Proto Rec Rec Rec
private def base : Rec := { lookup := fun key => match key with
  | .x => some 1 | .y => some 2 | .z => none }
private def x3 : Layer := Record.slot .x (3 : Int)
private def doubleX : Layer := Record.modify .x (fun x : Int => 2*x)
-- Literal source complex numbers use integral real/imaginary coordinates.
private def zXY : Layer := Record.compute .z fun self =>
  ((self.lookup .x).getD 0, (self.lookup .y).getD 0)
private unsafe def close (layer : Layer) : Rec := Record.instantiate layer base

private unsafe def records : IO Unit := do
  -- Original eval:check source lines 272, 328, 332, 336, 344.
  unless (base.lookup .x, base.lookup .y) == (some 1,some 2) do throw (IO.userError "paper:272")
  let changed := close x3
  unless (changed.lookup .x,changed.lookup .y) == (some 3,some 2) do throw (IO.userError "paper:328")
  let complex := close zXY
  unless (complex.lookup .x,complex.lookup .y,complex.lookup .z) == (some 1,some 2,some (1,2)) do
    throw (IO.userError "paper:332")
  let doubled := close doubleX
  unless (doubled.lookup .x,doubled.lookup .y) == (some 2,some 2) do throw (IO.userError "paper:336")
  let combined := close (compose zXY (compose doubleX x3))
  unless (combined.lookup .x,combined.lookup .y,combined.lookup .z) == (some 6,some 2,some (6,2)) do
    throw (IO.userError "paper:344")
  -- Original right/left association cases and final self rebinding: 352, 362.
  for layer in [compose zXY (compose doubleX x3),compose doubleX (compose zXY x3),
      compose doubleX (compose x3 zXY)] do
    unless (close layer).lookup .z == some (6,2) do throw (IO.userError "paper:352")
  for layer in [compose (compose zXY doubleX) x3,compose (compose doubleX zXY) x3,
      compose (compose doubleX x3) zXY] do
    unless (close layer).lookup .z == some (6,2) do throw (IO.userError "paper:362")
  unless ((close (compose doubleX x3)).lookup .x,(close (compose x3 doubleX)).lookup .x) ==
      (some 6,some 3) do throw (IO.userError "paper:376")
  let lone : Rec := Record.instantiate x3 Record.empty
  unless lone.lookup .x == some 3 do throw (IO.userError "paper:456")
  let both : Rec := Record.instantiate
    (compose (Record.slot .x (1 : Int)) (Record.slot .y (2 : Int))) Record.empty
  unless (both.lookup .x,both.lookup .y) == (some 1,some 2) do throw (IO.userError "paper:465")
  IO.println "POOF-RECORD-CHECKS-OK sourceChecks=10 complexCoordinates=integral typedSlots=true"

private def evenLayer : Proto (FixedFunction Int Int) (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun self inherited => FixedFunction.ofFun fun x => if x < 0 then self (-x) else inherited x
private def cube : Proto (FixedFunction Int Int) (FixedFunction Int Int) (FixedFunction Int Int) :=
  fun _ inherited => FixedFunction.ofFun fun x => let y := inherited x; y*y*y
private unsafe def otherCases : IO Unit := do
  let absoluteCube := instantiate (compose evenLayer (compose cube
    (constant (FixedFunction.ofFun fun x : Int => x)))) (FixedFunction.ofFun fun _ : Int => (0 : Int))
  unless ([3,-2,0,-1] : List Int).map absoluteCube == [27,8,0,1] do throw (IO.userError "paper:869")
  let plus : DelayedProto Nat Nat Nat := fun _ inherited => inherited.get+1
  let twice : DelayedProto Nat Nat Nat := fun _ inherited => inherited.get*2
  unless ((DelayedProto.instantiate (DelayedProto.compose plus twice) (Thunk.pure 30)).get,
    (DelayedProto.instantiate (DelayedProto.compose twice plus) (Thunk.pure 30)).get) == (61,62) do
    throw (IO.userError "paper:878")
  -- Source object checks: typed delayed slots, retained prototype/instance pair.
  let empty : Record String (fun _ => Int) := Record.empty
  let layer := DelayedProto.compose (Object.recordSlotGen "a" (fun _ _ => some (1 : Int)))
    (DelayedProto.compose (Object.recordSlotGen "b" (fun _ _ => some (2 : Int))) (Object.recordSlotGen "c" (fun _ _ => some (3 : Int))))
  let object := Object.ofPrototype layer (Thunk.pure empty)
  unless (["a","b","c"].map fun k => object.value.lookup k) == [some 1,some 2,some 3] do
    throw (IO.userError "paper:1974")
  let foo := Object.ofPrototype (Object.recordSlotGen "foo" (fun _ _ => some (1 : Int))) (Thunk.pure empty)
  unless foo.value.lookup "foo" == some 1 do throw (IO.userError "paper:1975")
  let numbers := ((Descriptor.top "Int" toString : Descriptor Int).withJson).listOf
  let checks := [numbers.decodeJson (.arr #[]),numbers.decodeJson (Lean.toJson ([1,2,3] : List Int)),
    numbers.decodeJson (.arr #[Lean.toJson (1 : Int),.str "a",Lean.toJson (2 : Int)]),
    numbers.decodeJson (Lean.Json.mkObj [("car",Lean.toJson (1 : Int)),("cdr",Lean.toJson (2 : Int))])]
  unless checks.map Except.isOk == [true,true,false,false] do throw (IO.userError "paper:1976")
  IO.println "POOF-OTHER-CHECKS-OK numericChecks=2 extraChecks=3 listBoundary=typed-json"

example : True := by
  fail_if_success have mixed : List Int := [1,"a",2]
  fail_if_success have improper : List Int := (1,2)
  trivial
#eval records
#eval otherCases
end LeanPoo.Tests.PaperPrototypeChecks
