import LeanPoo.Prototype.FiniteFix

open LeanPoo.Prototype
namespace LeanPoo.Tests.PaperFiniteFix

abbrev Pair := Bool → Option Nat

private def pairLayer : Proto Pair Unit Pair :=
  fun self _ flag => if flag then some 1 else self true

private def emptyPair : Pair := fun _ => none

private theorem pair_stable :
    FiniteFix.iterate pairLayer () emptyPair 2 =
      FiniteFix.iterate pairLayer () emptyPair 3 := by
  funext flag
  cases flag <;> rfl

private def pairFixed : { value : Pair // pairLayer value () = value } :=
  FiniteFix.certified pairLayer () emptyPair 2 pair_stable

#guard pairFixed.1 false == some 1 && pairFixed.1 true == some 1
#guard (FiniteFix.iterate pairLayer () emptyPair 0) false == none
#guard (FiniteFix.iterate pairLayer () emptyPair 1) false == none
#guard (FiniteFix.iterate pairLayer () emptyPair 2) false == some 1

private def triangular : Nat → Nat
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

private def recursive : Proto (CheckedFunction Nat Nat)
    (CheckedFunction Nat Nat) (CheckedFunction Nat Nat) :=
  fun self _ => FixedFunction.ofFun fun n =>
    if n == 0 then .ok 0 else do return (← self (n-1)) + n

private theorem finite_triangular (n : Nat) :
    (CheckedFunction.approximate recursive (n + 1)) n =
      .ok (triangular n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (recursive (CheckedFunction.approximate recursive (n + 1))
      CheckedFunction.bottom) (n + 1) = .ok (triangular (n + 1))
    simp only [recursive, FixedFunction.ofFun, Nat.succ_sub_one, triangular]
    simp [ih, Functor.map, Except.map]

private unsafe def compareShared : IO Unit := do
  let shared := CheckedFunction.instance [recursive]
  for n in List.range 65 do
    let bounded := CheckedFunction.approximate recursive (n + 1)
    unless (bounded n).toOption == some (triangular n) &&
        (shared n).toOption == (bounded n).toOption do
      throw (IO.userError "finite unfolding differs from guarded shared recursion")
  IO.println "POOF-FINITE-FIX-OK guardedInputs=65 certifiedBoolDepth=2 finiteUnfolding=true sharedObservation=true"

#eval compareShared
#print axioms FiniteFix.unfold
#print axioms FiniteFix.unfold_compose
#print axioms FiniteFix.certified
#print axioms FiniteFix.stable_forever
#print axioms CheckedFunction.approximate_succ
#print axioms finite_triangular

end LeanPoo.Tests.PaperFiniteFix
