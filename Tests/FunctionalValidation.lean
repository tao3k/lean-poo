import LeanPoo.Functional.Validation

namespace LeanPoo.Tests.FunctionalValidation
open Functional

-- Errors identify a successful prefix, its first failure and an arbitrary suffix.
example (check : α → Except ε β) (items : List α) (error : ε) :
    Validation.traverse check items = .error error ↔
      ∃ before item after values, items = before ++ item :: after ∧
        Validation.traverse check before = .ok values ∧ check item = .error error :=
  Validation.traverse_error_iff check items error

private def bounded (capacity value : Nat) : Except Nat {n : Nat // n ≤ capacity} :=
  if valid : value ≤ capacity then .ok ⟨value, valid⟩ else .error value
private partial def unreachable (capacity : Nat) : Except Nat {n : Nat // n ≤ capacity} :=
  unreachable capacity

#eval do
  let mut cases := 0
  for capacity in List.range 6 do
    for items in [[], [0], [1, 1], [0, 2, 5], [5, 2], [7, 8, 0]] do
      let actual := Factory.traverseExcept items bounded capacity
      let expected := items.find? (fun value => capacity < value)
      match actual, expected with
      | .error error, some first =>
        unless error == first do throw (IO.userError "wrong first batch refusal")
      | .ok values, none =>
        unless values.map Subtype.val == items do throw (IO.userError "batch lost order or duplicates")
      | _, _ => throw (IO.userError "batch differs from independent first-invalid scan")
      cases := cases + 1
    let factories := [(fun c => bounded c 7), unreachable]
    match Factory.sequenceExcept factories capacity with
    | .error 7 => pure ()
    | _ => throw (IO.userError "error did not stop before unreachable factory")
  IO.println s!"FUNCTIONAL-VALIDATION-OK cases={cases} unreachableSuffixes=6"

-- Dependent results from another context cannot be published as this batch.
example : True := by
  fail_if_success have bad : Except Nat (List {n : Nat // n ≤ 2}) :=
    Factory.traverseExcept [3] bounded 4
  trivial

#print axioms Validation.traverse_error_iff
#print axioms Validation.traverse_append
#print axioms Validation.traverse_success
#print axioms Factory.sequenceExcept_append
end LeanPoo.Tests.FunctionalValidation
