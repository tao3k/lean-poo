import LeanPoo.Functional.HybridClosure
import LeanPoo.Functional.CyclicAccess
import LeanPoo.Functional.ClosureScenarios

/-! Per-write scheduling, retained dependency metadata and cyclic revocation.
This advances the generalized protocol's future work within finite positive equations. -/
namespace LeanPoo.Examples.AdaptiveAccess
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  let plan := compile (CyclicAccess.equations {} true)
  let active := HybridClosure.close HybridClosure.balanced plan
  unless active.store[7] do throw (IO.userError "release")
  let revoked := reconfigure plan (CyclicAccess.equations {} false) (by
    intro index
    rw [compile_source]
    exact CyclicAccess.equation_dependencies _ _ _ _ _)
  let next := HybridClosure.close HybridClosure.balanced revoked
  unless !next.store[7] && active.store[7] do throw (IO.userError "revocation or retained snapshot")
  -- Shared fan-out bursts alternate with narrow links. Different backend prices
  -- change scheduling while preserving exactly the same published solution.
  let bursts := compile (ClosureScenarios.equations "bursts" 128 16 true)
  let cheapCopy := HybridClosure.measured ⟨0,4,4⟩ bursts
  let cheapFrame := HybridClosure.measured ⟨9,0,0⟩ bursts
  let balanced := HybridClosure.measured HybridClosure.balanced bursts
  unless cheapCopy.work.frames == 0 && cheapFrame.work.frames > 0 &&
      cheapCopy.store == cheapFrame.store && balanced.store == cheapCopy.store &&
      balanced.work.frames < balanced.stats.writes do throw (IO.userError "adaptive policy")
  IO.println "ADAPTIVE-ACCESS-OK retained-index cyclic-revocation shared-bursts explicit-backend-prices"
#print axioms HybridClosure.canonical
#print axioms HybridClosure.execute_refines
#print axioms HybridClosure.balanced_allocation
#print axioms HybridClosure.fee_bound
end LeanPoo.Examples.AdaptiveAccess
