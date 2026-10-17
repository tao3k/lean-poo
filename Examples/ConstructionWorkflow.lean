import LeanPoo.Functional.ConstructionWorkflow

/-! Automatic graph closure and an atomic source/topology/layout/policy upgrade.
These examples advance the generalized-prototype future work. -/
namespace LeanPoo.Examples.ConstructionWorkflow
open Functional Functional.ConstructionWorkflow Functional.GeneralizedMOP

def check : Except String Unit :=
  match start {input := 30} .aggregate 1000 with
  | .error error => .error (publicationTag error)
  | .ok version => match warm version ⟨"Delivery","EU",2⟩ with
    | .error error => .error error
    | .ok (_,old) =>
      let edits : List (Redefinition String Values Policy) := [
        .setBase "input" (some (.ok 60)),
        .setBase "discount" (some (.ok 5)),
        .define "reserve" (.both (both "freight" "cover" (fun l r => 10*l+r))
          (.read "discount" fun _ value => value.getD (.ok 0))
          (fun _ reserved discount => do return (← reserved) - (← discount))),
        .define "invoice" (need "settlement" (· + 7)),
        .support keys.reverse,
        .policy .peak]
      let outcome := migrate old edits 1000
      match outcome.1 with
      | .error error => .error (publicationTag error)
      | .ok revision => do
        unless revision.snapshot.built.interface.layout == "settlement/v2" do
          throw "policy did not select the new interface"
        unless (revision.snapshot.built.inspect model watches).policy == .peak do
          throw "reflection returned stale policy"
        unless revision.snapshot.built.generic.cache.size == 0 && old.built.generic.cache.size > 0 do
          throw "publication cache lifecycle"
        let refused := migrate old [.setBase "permit" (some (.ok 1))] 1000
        match refused.1 with
        | .ok _ => throw "negative assumption admitted"
        | .error error =>
          unless publicationTag error == "negative" && refused.2.built.generic.cache.size == old.built.generic.cache.size do
            throw "negative refusal changed warm old version"
        pure ()

/-- Heterogeneous raw slots remain typed throughout automatic closure. -/
abbrev fieldType : Bool → Type
  | false => Nat
  | true => String

def heterogeneous : GeneralizedGraph.Declaration Bool fieldType where
  keys := [true,false]
  base := fun key => match key with
    | false => some (.ok 17)
    | true => none
  code := fun key => match key with
    | false => none
    | true => some (.need false fun _ number => number.map (fun value => "invoice:" ++ toString value))

def checkHeterogeneous : Except String Unit :=
  match heterogeneous.close with
  | .error _ => .error "heterogeneous schedule"
  | .ok closed => match closed.raw true,closed.raw false with
    | some (.ok text),some (.ok number) =>
      if text == "invoice:17" && number == 17 then .ok () else .error "heterogeneous values"
    | _,_ => .error "heterogeneous failure"

#eval match checkHeterogeneous with
  | .error message => throw (IO.userError message)
  | .ok () => IO.println "HETEROGENEOUS-GRAPH-OK Nat-to-String closed"

#eval match check with
  | .error message => throw (IO.userError message)
  | .ok () => IO.println "CONSTRUCTION-WORKFLOW-OK automatic-closure inferred-dependencies inspected-policy topology-source-layout-upgrade negative-refusal warm-old-preserved"
#print axioms GeneralizedGraph.Scheduled.closed
#print axioms GeneralizedGraph.Scheduled.unique
#print axioms GeneralizedGraph.Scheduled.unaffected
#print axioms Functional.ConstructionWorkflow.invoice_edit_retains
#print axioms GeneralizedMOP.Prepared.invoke_interface
#print axioms GeneralizedMOP.Prepared.closed
#print axioms GeneralizedMOP.call_definition
#print axioms GeneralizedMOP.revise_refused
end LeanPoo.Examples.ConstructionWorkflow
