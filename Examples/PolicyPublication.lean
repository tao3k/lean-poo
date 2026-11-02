import LeanPoo.Functional.PolicyPublication

/-! Future-work client: scoped method-policy upgrades after a multi-level shared
workflow, with actual configuration included in each dependent component key. -/
namespace LeanPoo.Examples.PolicyPublication
open Prototype Prototype.Generalized Functional.PolicyPublication
open TariffComponent (summary)

def run : IO Unit := do
  let initial : Policy := ⟨0,0,0⟩
  let original ← IO.ofExcept (publish initial 0)
  let invoiceOnly ← IO.ofExcept (revise original ⟨5,0,0⟩ 0 (fun stage => stage != 7))
  unless invoiceOnly.flags == List.replicate 7 true ++ [false,true,true] do
    throw (IO.userError "policy-only change did not refresh exactly invoice")
  unless rates (assemble invoiceOnly.publication).interface == rates (assemble original).interface do
    throw (IO.userError "method policy unexpectedly changed metadata tariffs")
  let oldValue := summary ((checkout (assemble original).interface 2).run [])
  let newValue := summary ((checkout (assemble invoiceOnly.publication).interface 2).run [])
  unless newValue.1 == oldValue.1.map (· + 5) && newValue.2.2 == oldValue.2.2 do
    throw (IO.userError "unchanged metadata returned stale method semantics")
  let releaseOnly ← IO.ofExcept (revise original ⟨0,0,7⟩ 0 (fun stage => stage != 9))
  unless releaseOnly.flags == List.replicate 9 true ++ [false] do
    throw (IO.userError "release configuration bypassed fresh admission")
  unless (revise original ⟨5,0,0⟩ 0 (fun stage => stage == 7)).toOption.isNone do
    throw (IO.userError "changed configuration bypassed refusing invoice builder")
  IO.println "POLICY-PUBLICATION-OK ten-components unchanged-metadata changed-method-policy scoped-admission retained-upstream retained-branches refused-upgrade"
#eval run
#print axioms Functional.PolicyPublication.assemble
#print axioms Functional.PolicyPublication.retained_audit
#print axioms Functional.PolicyPublication.retained_release
#print axioms Closed.reindexSelf_view
#print axioms Closed.refreshConfiguration_error
end LeanPoo.Examples.PolicyPublication
