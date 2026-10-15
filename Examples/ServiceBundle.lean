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

local instance {E A : Type} [DecidableEq E] [DecidableEq A] : DecidableEq (Except E A) := by
  intro left right
  cases left <;> cases right <;> simp <;> infer_instance

/-- Each constructor sees only these finite service-specific inputs. -/
abbrev Slot := Option (GeneralizedGraph.Outcome String ConstructionWorkflow.Values "input")
structure QuoteInputs where
  pricing : ConstructionWorkflow.Policy
  input : Slot
  total : Slot
  permit : Bool
  deriving DecidableEq

abbrev Inputs : Service → Type
  | .quote => QuoteInputs
  | .reserve => Bool × Int × Slot
  | .cancel => Int × Bool × Slot

instance (key : Service) : DecidableEq (Inputs key) := by cases key <;> dsimp [Inputs, Slot] <;> infer_instance

def scope : (key : Service) → Inputs key → Policy × ConstructionWorkflow.Interface
  | .quote, ⟨pricing,input,total,permit⟩ =>
    (⟨pricing,0,0,false,false⟩,⟨"projected",fun name =>
      if name == "input" then input else if name == "total" then total
      else if name == "permit" && permit then some (.ok 1) else none⟩)
  | .reserve, (broken,shift,total) =>
    (⟨.aggregate,shift,0,broken,false⟩,⟨"projected",fun name => if name == "total" then total else none⟩)
  | .cancel, (shift,forbidden,invoice) =>
    (⟨.aggregate,0,shift,false,forbidden⟩,⟨"projected",fun name => if name == "invoice" then invoice else none⟩)

def source : GenericFamily.Source (G := Service) (Policy := Policy) (Cooked := ConstructionWorkflow.Interface)
    (Args := Args) (Method := Method) (Result := Result) where
  Context := Inputs
  project := fun key policy view => match key with
    | .quote => ⟨policy.pricing,view.state "input",view.state "total",(view.state "permit").isSome⟩
    | .reserve => (policy.brokenReserve,policy.reserveShift,view.state "total")
    | .cancel => (policy.cancelShift,policy.forbiddenCancel,view.state "invoice")
  seed := fun key inputs => seed key (scope key inputs).1 (scope key inputs).2
  seedEmpty := fun key inputs => model.generics.seedEmpty key (scope key inputs).1 (scope key inputs).2
  methods := fun key inputs => methods key (scope key inputs).1 (scope key inputs).2
  keys := [.quote,.reserve,.cancel]
  watches := watches

instance : (key : Service) → DecidableEq (source.projection.Context key) := fun key =>
  inferInstanceAs (DecidableEq (Inputs key))

def projectedModel : StagedPublication.Model String ConstructionWorkflow.Values Service Policy
    ConstructionWorkflow.Interface Args Method Result := {model with generics := source.asModel}

abbrev ProjectedVersion := StagedPublication.Snapshot projectedModel (fun _ _ => Unit)
def admitted (current : Request) (_ : StagedPublication.Candidate projectedModel current) : Except String Unit := .ok ()
def invokeProjected (old : ProjectedVersion) (key : Service) (args : Args key) :
    Except (Sum (Object.DispatchTableError Service) String) (Result key × ProjectedVersion) :=
  old.invoke projectedModel key args admitted

def onCall {key : Service}
    (outcome : Except (Sum (Object.DispatchTableError Service) String) (Result key × ProjectedVersion))
    (next : Result key → ProjectedVersion → Except String Unit) : Except String Unit :=
  match outcome with | .error _ => .error "projected call" | .ok (value,version) => next value version

def projectedCheck : Except String Unit :=
  let request := request {input := 30} {}
  match StagedPublication.start projectedModel request
      (ConstructionCache.Builder.guarded request.graph (fun _ => true)) admitted with
  | .error _ => .error "projected cold"
  | .ok prepared =>
    onCall (invokeProjected (prepared.snapshot projectedModel) .quote ⟨"Delivery","US",1⟩) fun _ quoted =>
    onCall (invokeProjected quoted .reserve 2) fun _ held =>
    onCall (invokeProjected held .cancel ("customer",true)) fun _ warm =>
    let edits : List Edit := [.policy {pricing := .peak}]
    let outcome := StagedPublication.publishRefresh projectedModel source.projection warm edits
      (ConstructionCache.Builder.guarded (GeneralizedMOP.redefine warm.request edits).graph (fun _ => false)) admitted
    match outcome.1 with
    | .error _ => .error "projected repricing"
    | .ok next => do
      for key in [Service.reserve,.cancel] do
        unless ((next.candidate.family.table.get? key).map fun generic => generic.cache.size) == some 1 do
          throw "warm sibling cache lost"
      unless ((next.candidate.family.table.get? .quote).map fun generic => generic.cache.size) == some 0 do
        throw "changed quote retained stale cache"
      onCall (invokeProjected (next.snapshot projectedModel) .quote ⟨"Delivery","US",1⟩) fun quote _ => do
        unless quote.toOption == some 43 do throw "repriced observation"
        let budget : (request : Request) → StagedPublication.Candidate projectedModel request → Except String Unit :=
          fun _ candidate => if [Service.quote,.reserve,.cancel].foldl (fun n key =>
            n + ((candidate.family.table.get? key).map fun generic => generic.cache.size).getD 0) 0 > 2
            then .error "budget" else .ok ()
        let refused := StagedPublication.publishRefresh projectedModel source.projection warm []
          (ConstructionCache.Builder.guarded warm.request.graph (fun _ => false)) budget
        match refused.1 with
        | .error (.admission _ _ "budget") => pure ()
        | _ => throw "retained warm caches bypassed publication budget"
        let forbidden : List Edit := [.policy {forbiddenCancel := true}]
        match StagedPublication.stageRefresh projectedModel source.projection warm forbidden
            (ConstructionCache.Builder.guarded (GeneralizedMOP.redefine warm.request forbidden).graph (fun _ => false)) admitted with
        | .error (.generic (.negative .cancel _ _)) => pure ()
        | _ => throw "dirty third-service negative assumption bypassed"

#eval match projectedCheck with
  | .error error => throw (IO.userError error)
  | .ok () => IO.println "PROJECTED-SERVICE-REFRESH-OK warm-siblings, changed-quote, joint-budget-refusal, negative-refusal"
#print axioms GenericFamily.Partial.refresh_retained
#print axioms GenericFamily.Source.projection
#print axioms StagedPublication.publishRefresh_refused

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
