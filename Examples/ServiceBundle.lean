import LeanPoo.Functional.ServiceBundle
import LeanPoo.Functional.InheritedSettlement

/-! Actual skipped construction plus atomic quote/reserve/cancel publication.
The generalized-prototype protocol here remains explicit future work. -/
namespace LeanPoo.Examples.ServiceBundle
open Functional Functional.ServiceBundle

def check : Except String Unit :=
  match start {input := 30} {} 1000 with
  | .error error => .error (failureTag error)
  | .ok initial => do
    unless initial.candidate.cache.evaluated.length == 15 do throw "cold construction did not materialize support"
    let edits : List Edit := [.define "invoice" (ConstructionWorkflow.need "settlement" (· + 9))]
    let changed := revise initial edits (["invoice","release","total"].contains ·) 1000
    match changed.1 with
    | .error error => throw (failureTag error)
    | .ok prepared =>
      let version := prepared.snapshot model
      unless version.candidate.cache.evaluated == ["invoice","release","total"] &&
          version.candidate.cache.reused.length == 12 && quoteProbe version.candidate == some 78 &&
          reserveProbe version.candidate == some (39,true) &&
          cancelProbe version.candidate == some ["customer","invoice:33"] do
        throw "selective materialization/family mismatch"
      let policy : Policy := {pricing := .peak}
      let policyOnly := revise version [.policy policy] (fun _ => false) 1000
      match policyOnly.1 with
      | .error error => throw (failureTag error)
      | .ok selected =>
        unless selected.candidate.cache.evaluated.isEmpty && selected.candidate.cache.reused.length == 15 &&
            quoteProbe selected.candidate == some 52 do throw "policy-only reconstruction ran a refusing builder"
      -- Both shared branches and their joins are rebuilt exactly once. The
      -- rejecting guard excludes every constructor outside the invalidation cone.
      let rootDirty := ["input","freight","cover","reserve","tax","risk",
        "settlement","invoice","audit","release","total"]
      let rootChanged := revise version [.setBase "input" (some (.ok 60))] rootDirty.contains 1000
      match rootChanged.1 with
      | .error error => throw (failureTag error)
      | .ok prepared =>
        unless prepared.candidate.cache.evaluated.length == 11 &&
            prepared.candidate.cache.reused.length == 4 &&
            quoteProbe prepared.candidate == some 134 &&
            reserveProbe prepared.candidate == some (65,true) &&
            cancelProbe prepared.candidate == some ["customer","invoice:51"] do
          throw "shared invalidation/cross-service stale capture"
      -- The third generic refuses after the first two have been reconstructed.
      let refused := revise version [.policy {forbiddenCancel := true}] (fun _ => false) 1000
      match refused.1 with
      | .ok _ => throw "third generic's negative assumption escaped"
      | .error error => do
        unless failureTag error == "negative:" ++ reprStr Service.cancel &&
            quoteProbe refused.2.candidate == some 78 && cancelProbe refused.2.candidate == some ["customer","invoice:33"] do
          throw "partial generic family publication"
    pure ()

/-- The same materializer accepts the existing C3/super-fragment workflow.
Only policy changes here, so its exact compiled source graph is retained. -/
def checkInherited : Except String Unit :=
  let source := InheritedSettlement.source {data := {input := 30}} .aggregate
  match Prototype.C3.linearize source.graph source.root with
  | .error _ => .error "inherited C3 preparation"
  | .ok order =>
    let initial : Request := ⟨(source.request order).graph,{}⟩
    match StagedPublication.start model initial
        (ConstructionCache.Builder.guarded initial.graph (fun _ => true)) (admit 10000) with
    | .error error => .error (failureTag error)
    | .ok prepared =>
      let original := prepared.snapshot model
      let updated := revise original [.policy {pricing := .peak}] (fun _ => false) 10000
      match updated.1 with
      | .error error => .error (failureTag error)
      | .ok next => do
        unless quoteProbe original.candidate == some 101 && quoteProbe next.candidate == some 75 &&
            reserveProbe next.candidate == some (62,true) &&
            cancelProbe next.candidate == some ["customer","invoice:51"] &&
            next.candidate.cache.evaluated.isEmpty && next.candidate.cache.reused.length == 15 do
          throw "C3/super graph policy staging"

#eval match checkInherited with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "INHERITED-SERVICE-BUNDLE-OK C3-super-graph policy-migration rebuilt=0 retained=15"

#eval match check with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "SERVICE-BUNDLE-OK materialized=15 rebuilt=3 retained=12 policy-rebuilt=0 heterogeneous-generics=3 atomic-last-generic-refusal"
#print axioms ConstructionCache.Cache.reference
#print axioms ConstructionCache.Partial.step_reused
#print axioms ConstructionCache.redefine_unchanged
#print axioms GenericFamily.Family.invoke_table
#print axioms GenericFamily.Family.invoke_other
#print axioms StagedPublication.publish_refused
#print axioms StagedPublication.Snapshot.invoke_construction
#print axioms Functional.ServiceBundle.coherent
end LeanPoo.Examples.ServiceBundle
