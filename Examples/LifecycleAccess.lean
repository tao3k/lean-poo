import LeanPoo.Functional.ClosureLifecycle
import LeanPoo.Functional.CyclicAccess
import LeanPoo.Functional.ClosureScenarios

/-! Generalized-protocol future work: cold access closure, delayed preparation,
retained cyclic revocation and dense shared dependencies. -/
namespace LeanPoo.Examples.LifecycleAccess
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  let plan := compile (CyclicAccess.equations {} true)
  let cold := ClosureLifecycle.prepare .cold plan
  let prepared := cold.upgrade
  let revoked := prepared.reconfigure (CyclicAccess.equations {} false) (by
    intro index
    rw [compile_source]
    exact CyclicAccess.equation_dependencies _ _ _ _ _)
  unless cold.solve.store[7] && prepared.solve.store[7] && !revoked.solve.store[7] &&
      cold.visits == 0 && revoked.visits == 0 && revoked.choose == prepared.choose do
    throw (IO.userError "cold / delayed / revoked access")
  for family in ["diamond","hubchain","ring","bursts","dense"] do
    let plan := compile (ClosureScenarios.equations family 256 16 true)
    let cold := ClosureLifecycle.prepare .cold plan
    let warm := cold.upgrade
    let expected : QueueSelection.Queue :=
      if family == "dense" then .chunked else if family == "bursts" then .hybrid else .append
    unless warm.choose == expected && cold.solve.store[255] && warm.solve.store[255] do
      throw (IO.userError "lifecycle strategy")
  IO.println "LIFECYCLE-ACCESS-OK cold delayed-upgrade retained-revocation dense-chunked shared-bursts"
#print axioms ClosureLifecycle.assemble_canonical
#print axioms ClosureLifecycle.assemble_pop_bound
#print axioms ClosureLifecycle.total_cost_bound
end LeanPoo.Examples.LifecycleAccess
