import LeanPoo.Functional.PositiveEquations

/-! Exhaustive independent truth-table fixed-point oracle, unsupported-cycle
controls and height-sized propagation chains for automatic positive closure. -/
namespace LeanPoo.Tests.PositiveEquations
open Functional Functional.PositiveEquations

def clauses : List (Expr 3 × (Nat → Bool)) := [
  (.literal false,fun _ => false),(.literal true,fun _ => true),
  (.read 0,fun mask => mask.testBit 0),(.read 1,fun mask => mask.testBit 1),(.read 2,fun mask => mask.testBit 2),
  (.both (.read 0) (.read 1),fun mask => mask.testBit 0 && mask.testBit 1),
  (.either (.read 1) (.read 2),fun mask => mask.testBit 1 || mask.testBit 2),
  (Expr.twoOfThree (.read 0) (.read 1) (.read 2),fun mask =>
    decide (2 ≤ (if mask.testBit 0 then 1 else 0)+(if mask.testBit 1 then 1 else 0)+(if mask.testBit 2 then 1 else 0)))]

def exhaustive : Except String Nat := do
  let mut count := 0
  for (a,oa) in clauses do
    for (b,ob) in clauses do
      for (c,oc) in clauses do
        let equations : Equations 3 := fun index => match index.val with | 0 => a | 1 => b | _ => c
        -- Enumerate every candidate assignment using independent clause tables.
        let fixed := (List.range 8).filter fun mask =>
          oa mask == mask.testBit 0 && ob mask == mask.testBit 1 && oc mask == mask.testBit 2
        unless !fixed.isEmpty do throw "finite monotone system had no oracle solution"
        let expected := (List.range 3).map fun index => fixed.all (fun mask => mask.testBit index)
        let result := close equations
        unless List.ofFn result.value == expected && result.depth ≤ 3 do throw "least truth-table oracle"
        let cache := materialize equations
        unless (List.ofFn fun index : Fin 3 => ((cache.closed.raw index).bind Except.toOption).getD false) == expected &&
            cache.evaluated.isEmpty && cache.reused.isEmpty do throw "compiled closure/builder boundary"
        count := count+1
  return count

def chain (n : Nat) : Equations n := fun index =>
  if zero : index.val = 0 then .literal true else .read ⟨index.val-1,by omega⟩

def controls : Except String Unit := do
  let empty : Equations 0 := Fin.elim0
  unless (close empty).depth == 0 && (materialize empty).evaluated.isEmpty do throw "empty equations"
  let unsupported : Equations 1 := fun _ => .read 0
  unless (close unsupported).value 0 == false && (step unsupported (fun _ => true)) 0 == true do
    throw "larger fixed point mistaken for least"
  unless !(declaration unsupported).schedule.isOk do throw "acyclic scheduler unexpectedly accepted a cycle"
  let errors : GeneralizedGraph.State (Fin 1) (fun _ => Bool) := fun _ => some (.error (.source "body"))
  match (declaration unsupported).resolve 0 errors with
  | some (.error (.source "body")) => pure ()
  | _ => throw "compiled source failure lost"
  let absent : GeneralizedGraph.State (Fin 1) (fun _ => Bool) := fun _ => none
  match (declaration unsupported).resolve 0 absent with
  | some (.ok false) => pure ()
  | _ => throw "declared missing-fact semantics"
  for n in List.range 13 do
    let result := close (chain n)
    unless (List.ofFn result.value).all id && result.depth == n do throw "height-sized propagation"

#eval match exhaustive.bind (fun count => controls.map (fun _ => count)) with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"POSITIVE-EQUATIONS-OK systems={count} candidate-assignments={count*8} chains=13 least-fixed-points=true"
end LeanPoo.Tests.PositiveEquations
