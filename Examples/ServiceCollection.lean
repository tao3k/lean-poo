import LeanPoo.Functional.CacheLookup

/-! Ordered host Iterable observations over source-bound recursive service rows.
The host hash/interface and iterator laws are premises; no GC/dispatch proof is asserted.
-/
namespace Examples.ServiceCollection
open LeanPoo.Functional
open LeanPoo.Functional.ConstructionCache

/-- The two alternatives distinguish stored false from a missing table entry. -/
def values : Nat → Option (Option Bool) := fun key => if key = 0 then some (some false) else some none
example : lookupOr (values 0) (fun _ => Except.error "unexpected fallback") = .ok (some false) := rfl
example : lookupOr (values 1) (fun _ => Except.error "unexpected fallback") = .ok none := rfl

/-- A symbolic shape identity stands for the exact live object held by layouts. -/
def shapes : Nat → Option Nat := fun _ => none
example : ensureLookup shapes 0 (fun _ => Except.error "constructor failure") =
    (.error "constructor failure", shapes) := rfl
example : ensureLookup (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2
    0 (fun _ => Except.error "must not rebuild") =
      (.ok 7, (ensureLookup shapes 0 (fun _ => Except.ok 7 : Unit → Except String Nat)).2) :=
  ensureLookup_repeat shapes 0 7 _ _ rfl rfl

/-- Iterator pulls retain order; a wrapping refusal stops before later service rows. -/
def wrap (row : Nat) : Except String Nat := if row = 2 then .error "invalid method" else .ok (row + 10)
example : Validation.traverse wrap [0, 1] = .ok [10, 11] := rfl
example : Validation.traverse wrap [0, 2, 1] = .error "invalid method" := rfl
/-- The diagnostic builder preserves issue order and multiplicity. -/
example : Validation.gatherIssues (fun (row : Nat) => [row, row + 10]) [0, 1] = [0, 10, 1, 11] := rfl

/-- Row admission delegates the guard before wrapping and observing through FUN. -/
example : Validation.checkThen (fun (_ : Nat) => Except.ok false) "shape"
    wrap (fun _ => Except.error "consumer must not run" : Nat → Except String Nat) 2 =
      .error "shape" := rfl
end Examples.ServiceCollection
