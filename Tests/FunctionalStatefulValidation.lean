import LeanPoo.Functional.StatefulValidation

namespace LeanPoo.Tests.FunctionalStatefulValidation
open Functional Validation
abbrev State := Nat × List Nat
private def equal : Except String (List Nat) → Except String (List Nat) → Bool
  | .error a, .error b => a == b
  | .ok a, .ok b => a == b
  | _, _ => false
private def check (limit : Nat) (state : State) (item : Nat) : Except String Nat × State :=
  let next := (state.1+item+1, state.2++[item])
  if item == 0 then (.error "zero", next)
  else if state.1+item > limit then (.error "limit", next)
  else (.ok (state.1+item), next)

-- Find the first offending index using prefix sums, independently of traversal.
private def control (limit seed : Nat) (items : List Nat) : Except String (List Nat) × State :=
  let bad := (List.range items.length).find? fun index =>
    items[index]! == 0 || seed+(items.take index).sum+index+items[index]! > limit
  let count := bad.map (·+1) |>.getD items.length
  let next : State := (seed+(items.take count).sum+count, items.take count)
  match bad with
  | some index => (.error (if items[index]! == 0 then "zero" else "limit"), next)
  | none => (.ok ((List.range items.length).map fun index => seed+(items.take (index+1)).sum+index), next)

#eval do
  let mut cases := 0
  let mut splits := 0
  for limit in List.range 7 do
    for seed in List.range 3 do
      for raw in [[],[0],[1],[2],[1,0,4],[2,3],[3,1,2],[1,1,1,1]] do
        let items : List Nat := raw
        let state : State := (seed,[])
        let actual := traverseState (check limit) state items
        let expected := control limit seed items
        unless equal actual.1 expected.1 && actual.2 == expected.2 do
          throw (IO.userError "stateful first-error/output/state differs from prefix-sum control")
        for index in List.range (items.length+1) do
          let (before, next) := traverseState (check limit) state (items.take index)
          let combined : Except String (List Nat) × State := match before with
            | .error error => (.error error, next)
            | .ok outputs =>
              let (after, final) := traverseState (check limit) next (items.drop index)
              (after.map (outputs++·), final)
          unless equal combined.1 actual.1 && combined.2 == actual.2 do
            throw (IO.userError "split batch lost first failure or retained state")
          splits := splits+1
        cases := cases+1
  unless cases == 168 && splits == 483 do throw (IO.userError s!"stateful coverage drift: {cases}/{splits}")
  IO.println s!"FUNCTIONAL-STATEFUL-VALIDATION-OK cases={cases} splits={splits}"

private partial def unreachable (state : State) : Except String Nat × State := unreachable state
private def guarded (state : State) (item : Nat) :=
  if item == 9999 then unreachable state else check 2 state item
#eval do
  for item in [0,3] do
    let actual := traverseState guarded (0,[]) [item,9999]
    unless actual.1.toOption.isNone && actual.2 == (item+1,[item]) do
      throw (IO.userError "failed step lost state or forced suffix")
  IO.println "STATEFUL-UNREACHABLE-SUFFIX-OK cases=2"

#print axioms traverseState_append
#print axioms traverseState_error_iff
#print axioms traverseState_stateless
#print axioms traverseState_map
end LeanPoo.Tests.FunctionalStatefulValidation
