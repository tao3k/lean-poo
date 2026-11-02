import LeanPoo.Object.MethodCompilation

/-! Preparation laws with opaque callbacks, plus current-metadata observations.
Metadata is supplied by the caller on every invocation; mutable dependency
registration and actual public reflection are covered by Gerbil regressions. -/
namespace LeanPoo.Examples.DeclaredMethods
open LeanPoo Object.MethodCombination

/-- A prepared fragment collection uses the same next nesting as the interpreter. -/
example {Receiver : Type} {M : Type → Type} {Result : Type}
    (methods : List (SubMethod Receiver M Result)) (terminal : Receiver → M Result) :
    composeContinuations (methods.map methodContinuation) terminal =
      callChain methods terminal := composeMethods_eq_callChain _ _

/-- The callback retains a read operation, never a successful read's old result. -/
def currentRead {Receiver : Type} (read : Receiver → Except String Nat) :
    SubMethod Receiver (Except String) Nat := fun _ receiver => read receiver

/-- A fresh refused receiver remains refused through the SAME prepared code,
including when a previous receiver succeeded. No mutation theorem is assumed. -/
example {Receiver : Type} (read : Receiver → Except String Nat)
    (previous current : Receiver) (value : Nat) (message : String)
    (_old : read previous = .ok value) (refused : read current = .error message)
    (terminal : Receiver → Except String Nat) :
    composeContinuations [methodContinuation (currentRead read)] terminal current =
      .error message := refused

/-- Skipping next suppresses the whole remaining sequence, including its failure. -/
example : composeContinuations
    ([fun _ => fun (_ : Nat) => (Except.ok 7 : Except String Nat),
      fun _ => fun _ => .error "unreachable"] : List ((Nat → Except String Nat) → (Nat → Except String Nat)))
    (fun _ => .error "terminal") 3 = .ok 7 := rfl

/-- Repeated next observes the same current row twice, without result substitution. -/
example : (composeContinuations
    [methodContinuation (M := Id) (Result := Nat) (fun next (_ : Nat) => do
      let first ← next (); let second ← next (); pure (first + second))]
    (fun row => pure (row + 1)) 4).run = 10 := rfl

#print axioms composeMethods_eq_callChain
#print axioms composeForward_eq_callForwardChain
#print axioms composeSides_eq_runSides
#print axioms composeSimula_eq_effective
end LeanPoo.Examples.DeclaredMethods
