import LeanPoo.Functional.SharedSettlement

/-! Future-work client: a retained first join does not hide shared upstream
changes from the second fork or its contextual final join. -/
namespace LeanPoo.Examples.SharedSettlement
open Prototype Prototype.Generalized Functional.SharedSettlement

def run : IO Unit := do
  let original ← IO.ofExcept (publish 0)
  let unchangedSuffix ← IO.ofExcept (revise original 1 (fun stage => stage ≥ 3))
  unless unchangedSuffix.flags == [false,true,false,true,true,true,true] do throw (IO.userError "retained multi-level suffix")
  let sharedChange ← IO.ofExcept (revise original 2 (fun _ => false))
  unless sharedChange.flags == [false,true,false,true,false,true,false] do throw (IO.userError "shared dependency lost across reserve join")
  let second ← IO.ofExcept (publish 2)
  let directChange ← IO.ofExcept (revise second 3 (fun _ => false))
  unless directChange.flags == [false,true,true,true,true,true,false] do throw (IO.userError "retained branches incorrectly retained contextual join")
  unless (revise second 3 (fun stage => stage == 6)).toOption.isNone do throw (IO.userError "changed context bypassed refusing final builder")
  IO.println "SHARED-SETTLEMENT-OK seven-components two-level-fork-join shared-context survives-retained-join final-invalidates-despite-retained-branches"
#eval run
#print axioms Functional.SharedSettlement.assemble
#print axioms Functional.SharedSettlement.retained_risk
#print axioms Functional.SharedSettlement.retained_final
#print axioms DependencyFork.Refresh.joinWith_reuses
#print axioms DependencyFork.Refresh.joinWith_error
end LeanPoo.Examples.SharedSettlement
