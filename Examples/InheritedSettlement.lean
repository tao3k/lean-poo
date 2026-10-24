import LeanPoo.Functional.InheritedSettlement

/-! Source-level diamond upgrades over the same automatically closed settlement
workflow. This advances the generalized-prototype future-work proposal. -/
namespace LeanPoo.Examples.InheritedSettlement
open Functional Functional.InheritedSettlement
open Functional.ConstructionWorkflow (Policy model watches)

def check : Except String Unit :=
  let settings : Settings := {data := {input := 30}}
  match start settings .aggregate 10000 with
  | .error error => .error (failureTag error)
  | .ok old => match old.invoke model watches ⟨"Delivery","EU",2⟩ (ConstructionWorkflow.admit 10000) with
    | .error _ => .error "warm source version"
    | .ok (result,old) => do
      unless result.toOption == some 199 && old.order == ["Service","Regional","Scale","Base","Legacy"] do
        throw "original diamond order/result"
      let next : Settings := {settings with swapped := true,data := {input := 60,discount := some 5},conditional := true}
      let upgraded := migrate old next .peak 10000
      match upgraded.1 with
      | .error error => throw (failureTag error)
      | .ok revision =>
        match revision.snapshot.version.built.generic.call ⟨"Delivery","EU",2⟩ with
        | .error _ => throw "new dispatch"
        | .ok (answer,_) =>
          unless answer.toOption == some 387 && revision.snapshot.order == ["Service","Scale","Regional","Base","Legacy"] do
            throw "new topology/policy/final-self result"
      -- An unconditional replacement prunes even a cyclic inherited computation.
      match start {settings with baseInvoice := false,hazard := .cycle,overrideInvoice := some 77} .aggregate 10000 with
      | .error error => throw ("shielded legacy:" ++ failureTag error)
      | .ok shielded =>
        unless (shielded.version.built.interface.state "invoice").bind Except.toOption == some 77 do
          throw "root override did not shield super"
      let forbidden := migrate old {next with forbidden := true} .peak 10000
      match forbidden.1 with
      | .ok _ => throw "forbidden dispatch introduced"
      | .error error =>
        unless failureTag error == "negative" && forbidden.2.order == old.order &&
            forbidden.2.version.built.generic.cache.recent == old.version.built.generic.cache.recent do
          throw "refusal changed source or warm cache"
      pure ()

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "INHERITED-SETTLEMENT-OK C3-diamond ordered-super final-self conditional-override dead-parent-pruning source-policy-publication"
#print axioms GeneralizedFragments.compile_inheritance
#print axioms InheritedMOP.Snapshot.request_reference
#print axioms InheritedMOP.publish_refused
#print axioms InheritedMOP.Snapshot.resolves
#print axioms InheritedMOP.stage_inheritance_error
#print axioms Functional.InheritedSettlement.invoice_wrappers
#print axioms Functional.InheritedSettlement.order_difference
end LeanPoo.Examples.InheritedSettlement
