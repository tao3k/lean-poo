import LeanPoo.Functional.QueueSelection
import LeanPoo.Functional.CyclicAccess
import LeanPoo.Functional.ClosureScenarios

/-! Cached strategy selection, shared fan-out and least cyclic revocation.
This advances generalized-protocol future work within finite positive equations. -/
namespace LeanPoo.Examples.SelectedAccess
open Functional PositiveEquations IncrementalClosure

#eval show IO Unit from do
  let plan := compile (CyclicAccess.equations {} true)
  let prepared := QueueSelection.prepare QueueSelection.reference plan
  let active := prepared.solve
  let next := prepared.reconfigure (CyclicAccess.equations {} false) (by
    intro index
    rw [compile_source]
    exact CyclicAccess.equation_dependencies _ _ _ _ _)
  unless active.store[7] && !next.solve.store[7] && next.choose == prepared.choose &&
      next.appendCeiling == prepared.appendCeiling && next.hybridCeiling == prepared.hybridCeiling do
    throw (IO.userError "cached selection or cyclic revocation")
  for family in ["diamond","ring","hubchain","bursts"] do
    let source := compile (ClosureScenarios.equations family 256 16 true)
    let selected := QueueSelection.prepare QueueSelection.reference source
    let expected : QueueSelection.Queue := if family == "bursts" then .hybrid else .append
    unless selected.choose == expected && selected.run.store[255] &&
        selected.charge ≤ selected.appendCeiling && selected.charge ≤ selected.hybridCeiling do
      throw (IO.userError "topology selection")
  IO.println "SELECTED-ACCESS-OK cached-ceilings retained-index cyclic-revocation narrow-append shared-bursts"
#print axioms QueueSelection.selected_bound
#print axioms QueueSelection.canonical
#print axioms QueueSelection.reconfigure_choice
end LeanPoo.Examples.SelectedAccess
