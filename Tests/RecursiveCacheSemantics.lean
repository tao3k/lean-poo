import LeanPoo.Prototype.RecursiveCacheSemantics

open LeanPoo.Prototype.Recursive
namespace LeanPoo.Tests.RecursiveCacheSemantics

private def countdown : Generator Nat Nat
  | 0 => .value 0
  | n + 1 => .call n (fun value => .value (value + 1))

private theorem countdown_returns (input : Nat) :
    Evaluates countdown (countdown input) (.value input) := by
  induction input with
  | zero => exact .value
  | succ input ih => exact .callValue ih .value

/-- The shared runtime terminates for every input and every sound warm cache. -/
example (input : Nat) (cache : Cached.Cache countdown) :
    ∃ budget receipt next, Cached.run countdown input budget cache = .ok (receipt, next) ∧
      receipt.result.observation = .value input :=
  Cached.run_complete countdown input cache _ (countdown_returns input)

private def failure : Generator Nat Nat
  | 0 => .error "source failure"
  | n + 1 => .call n .value

private theorem failure_propagates (input : Nat) :
    Evaluates failure (failure input) (.error "source failure") := by
  induction input with
  | zero => exact .error
  | succ input ih => exact .callError ih

example (input : Nat) (cache : Cached.Cache failure) :
    ∃ budget receipt next, Cached.run failure input budget cache = .ok (receipt, next) ∧
      receipt.result.observation = .error "source failure" :=
  Cached.run_complete failure input cache _ (failure_propagates input)

private def loop : Generator Nat Nat := request

/-- An actual reported path now establishes divergence at every source depth. -/
example (input : Nat) : Diverges loop input := by
  apply Cached.run_cycle_diverges loop input 5 {} [input, input]
  simp [Cached.run, Cached.resolve, Cached.evaluate, Cached.Cache.lookup, loop, request,
    Cached.Cache.lookup.lookup, bind, Except.bind]

private def checks : IO Unit := do
  unless Cached.run countdown 128 1 matches .error .budgetExhausted do
    throw (IO.userError "small budget unexpectedly completed")
  let (receipt, _) ← IO.ofExcept ((Cached.run countdown 128 512).mapError reprStr)
  let (failed, _) ← IO.ofExcept ((Cached.run failure 128 512).mapError reprStr)
  unless receipt.result == .value 128 && failed.result == .error "source failure" &&
      Cached.run loop 7 20 matches .error (.cycle [7, 7]) do
    throw (IO.userError "terminating/error/cycle semantic controls")
  IO.println "RECURSIVE-CACHE-SEMANTICS-OK completeness=allFiniteEvaluations cycles=provenDivergence budgetExhaustion=distinct"

#eval checks
#print axioms Cached.run_complete
#print axioms Cached.run_cycle_diverges
#print axioms Cached.run_iff_evaluates
#print axioms Cached.diverges_iff_no_run
end LeanPoo.Tests.RecursiveCacheSemantics
