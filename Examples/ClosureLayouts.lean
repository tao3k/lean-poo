import LeanPoo.Functional.ClosurePolicy
import LeanPoo.Functional.CyclicAccess

/-! Cost-guided materialization of a cyclic access graph: select one of two
proved queue representations, then revoke a source seed with the exact index. -/
namespace LeanPoo.Examples.ClosureLayouts
open Functional PositiveEquations IncrementalClosure

def layout : ClosureCosts.Layout := ⟨8,by decide,1,1,2,4,20⟩
def prices : ClosureCosts.Prices := ⟨2,3,5,7⟩

#eval show IO Unit from do
  let source := CyclicAccess.equations {} true
  let plan := compile source
  let choice := ClosurePolicy.choose plan prices layout
  let active := ClosurePolicy.solve plan choice
  unless active.store[7] do throw (IO.userError "release")
  let revokedSource := CyclicAccess.equations {} false
  let retained := reconfigure plan revokedSource (by
    intro index
    rw [compile_source]
    exact CyclicAccess.equation_dependencies _ _ _ _ _)
  let revoked := ClosurePolicy.solve retained (ClosurePolicy.choose retained prices layout)
  unless !revoked.store[7] do throw (IO.userError "cyclic revocation")
  for candidate in [ClosurePolicy.Queue.append,.chunked] do
    unless ClosureCosts.charge prices layout (ClosurePolicy.representation choice) 10 active.stats ≤
      ClosurePolicy.upper plan prices layout candidate do throw (IO.userError "selected cost bound")
  IO.println "CLOSURE-LAYOUT-EXAMPLE-OK selected-upper-bound retained-topology cyclic-revocation"
#print axioms ClosurePolicy.selected_bound
#print axioms ClosurePolicy.minimumAllocation_optimal
end LeanPoo.Examples.ClosureLayouts
