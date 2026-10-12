import LeanPoo.Prototype.RecursiveSemantics
import LeanPoo.Prototype.CheckedFunction

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
namespace LeanPoo.Tests.RecursiveSemantics

private def factorialLayer : Proto (Generator Nat Nat) (Generator Nat Nat) (Generator Nat Nat) :=
  fun self _ input => if input == 0 then .value 1 else
    (self (input - 1)).map (fun answer => input * answer)

private def factorial : Generator Nat Nat := close factorialLayer (fun _ => .error "bottom")

private def factorialInt : Generator Nat Int := fun input =>
  if input == 0 then .value 1 else
    .call (input - 1) (fun answer => .value (Int.ofNat input * answer))

private theorem factorial_related (left right : Nat) (same : left = right) :
    Interaction.Rel Eq (fun n i => Int.ofNat n = i) (fun n i => Int.ofNat n = i)
      (factorial left) (factorialInt right) := by
  subst right
  by_cases zero : left == 0
  · simp only [factorial, close, factorialLayer, factorialInt, zero, ↓reduceIte]
    exact .value (by rfl)
  · simp only [factorial, close, factorialLayer, factorialInt, zero,
      request, Interaction.map, Interaction.bind]
    apply Interaction.Rel.call rfl
    intro answer answer' related
    subst answer'
    exact .value (by simp)

private theorem every_observation (depth input : Nat) :
    Observation.Rel (fun n i => Int.ofNat n = i)
      (solve factorial depth input) (solve factorialInt depth input) :=
  solve_relation factorial factorialInt Eq _ factorial_related depth input input rfl

private def loop : Generator Nat Nat := request
private theorem loop_diverges (input : Nat) : Diverges loop input := by
  intro depth
  induction depth with
  | zero => rfl
  | succ depth ih =>
    change (request input).interpret (solve loop depth) = .pending
    simp only [request, Interaction.interpret, ih]

private def errorProgram : Generator Nat Nat := fun input =>
  if input == 0 then .error "base rejected" else .call (input - 1) .value

#guard solve factorial 1 0 == .value 1
#guard solve factorial 6 6 == .pending
#guard solve factorial 7 6 == .value 720
#guard solve errorProgram 10 5 == .error "base rejected"
#guard solve loop 50 0 == .pending

-- Mix shares one recursive request generator and lets an override skip bottom.
private def constantLayer : Proto (Generator Nat Nat) (Generator Nat Nat) (Generator Nat Nat) :=
  fun _ _ _ => .value 42
#guard instantiate (compose constantLayer factorialLayer) (fun _ => .error "bottom") 1 99 == .value 42

private def delayedIncrement : Proto (Interaction Unit Nat Nat) (Interaction Unit Nat Nat)
    (Interaction Unit Nat Nat) := fun _ inherited => inherited.map (· + 1)
#guard instantiateValue (compose delayedIncrement delayedIncrement) (.value 0) 1 == .value 2
#guard instantiateValue (fun _ inherited => inherited.map String.length)
  (.value "typed inherited value") 1 == .value 21
#guard instantiateValue (fun self _ => self) (.value 0 : Interaction Unit Nat Nat) 30 == .pending

private theorem completed : Evaluates factorial (factorial 6) (.value 720) :=
  solve_sound factorial 7 6 (.value 720) (by decide) (by simp)

private unsafe def parity : IO Unit := do
  let oldLayer : Proto (FixedFunction Nat Nat) (FixedFunction Nat Nat) (FixedFunction Nat Nat) :=
    fun self _ => FixedFunction.ofFun fun input =>
      if input == 0 then 1 else input * self (input - 1)
  let old := instantiateAll [oldLayer] (FixedFunction.ofFun fun _ => 0)
  for input in List.range 13 do
    unless solve factorial (input + 1) input == .value (old input) do
      throw (IO.userError "safe recursive semantics differs from shared thunk")
  IO.println "POOF-RECURSIVE-OK operational=sound+complete outcomes=return+error+divergence parity=13 typedTransfer=allDepths"
#eval parity
#print axioms solve_sound
#print axioms solve_complete
#print axioms diverges_iff_no_evaluation
#print axioms solve_relation
#print axioms every_observation
#print axioms completed
end LeanPoo.Tests.RecursiveSemantics
