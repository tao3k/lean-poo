import LeanPoo.Functional.InheritedSettlement

/-! Independent inherited arithmetic, C3 order, dispatch and first-refusal
controls. This is future-work evidence for declared pure super fragments. -/
namespace LeanPoo.Tests.InheritedSettlement
open Functional Functional.InheritedSettlement Functional.GeneralizedFragments
open Functional.ConstructionWorkflow (Values Policy Call model watches keys)

abbrev Observation := Option Int × Option String

def slot (state : ConstructionWorkflow.Raw) (key : String) : Observation :=
  match state key with
  | none => (none,none)
  | some (.ok value) => (some value,none)
  | some (.error error) => (none,some (reprStr error))

def numbers (settings : Settings) : List Int :=
  let x := settings.data.input
  let freight := 2+x/5
  let cover := 3+x/7
  let reserve := 10*freight+cover
  let tax := 2+reserve/5
  let risk := x / (if settings.data.discount.isSome then 3 else 6)
  let settled := tax+risk
  let base := settled+settings.data.invoiceFee
  let inherited := if settings.swapped then (base+settings.surcharge)*settings.scale
    else base*settings.scale+settings.surcharge
  let invoice := settings.overrideInvoice.getD
    (if settings.conditional && settings.data.discount.isSome then settled+100 else inherited)
  let audit := 1+x/4
  let release := invoice+audit
  [release+risk,release,invoice,settled,tax,risk,reserve,freight,cover,audit,0,x]

def expectedCall (settings : Settings) (policy : Policy) (call : Call) : Observation :=
  if call.service == "Forbidden" then (some 0,none)
  else if call.units < 0 then (none,some "units")
  else
    let items := if call.service == "Delivery" then
      [((numbers settings)[0]!) * call.units,settings.data.input*call.units] ++
        if call.region == "EU" && call.units > 0 then [2*call.units] else []
      else [settings.data.input*call.units]
    let result := if policy == .aggregate then items.foldl (· + ·) 0 else items.foldl max 0
    (some (result + if policy == .aggregate then 7 else 11),none)

def calls : List Call := ["Delivery","Preview","Forbidden"].flatMap fun service =>
  ["EU","US"].flatMap fun region => [-1,0,2,5].map fun units => ⟨service,region,units⟩

def checkCalls (settings : Settings) (policy : Policy) (built : ConstructionWorkflow.Built) :
    List Call → Except String Nat
  | [] => .ok 0
  | call :: rest => match built.invoke model watches call with
    | .error _ => .error "call arity"
    | .ok (answer,next) => do
      let observed := match answer with | .ok value => (some value,none) | .error error => (none,some error)
      unless observed == expectedCall settings policy call do throw s!"inherited call {repr call} {repr observed}"
      return 1 + (← checkCalls settings policy next rest)

def checkVersion (settings : Settings) (version : Version) : Except String Unit := do
  let order := if settings.swapped then ["Service","Scale","Regional","Base","Legacy"]
    else ["Service","Regional","Scale","Base","Legacy"]
  unless version.order == order && version.order.count "Base" == 1 do throw "C3 shared ancestor order"
  for (key,index) in (keys.take 12).zipIdx do
    unless slot version.version.built.interface.state key == (some ((numbers settings)[index]!),none) do
      throw s!"inherited graph {key} {repr settings}"
  let sourceMeta := version.inspect model watches
  unless sourceMeta.root == "Service" && sourceMeta.order == order &&
      sourceMeta.classes.map Prod.fst == order do throw "source inspection provenance"
  let metadata := sourceMeta.components
  unless metadata.nodes.all (fun node => !node.2.unknown) do throw "dead legacy footprint survived override"
  for key in keys ++ ["outside"] do
    unless slot (version.version.built.request.graph.resolve · version.version.built.closed.raw) key ==
        slot version.version.built.closed.raw key do throw "whole inherited closure"

def refusedSource (old : Version) (candidate : InheritedMOP.Source String Values Policy)
    (limit : Int) (expected : String) : Except String Unit :=
  let outcome := InheritedMOP.publish model watches old candidate (ConstructionWorkflow.admit limit)
  match outcome.1 with
  | .ok _ => .error ("unexpected acceptance:" ++ expected)
  | .error error => do
    unless failureTag error == expected do throw ("first refusal:" ++ failureTag error ++ " expected:" ++ expected)
    unless outcome.2.order == old.order && outcome.2.source.graph == old.source.graph &&
        outcome.2.version.built.generic.cache.recent == old.version.built.generic.cache.recent &&
        outcome.2.version.built.generic.cache.size == old.version.built.generic.cache.size do
      throw "refused source/policy/cache publication"
    for key in keys do
      unless slot outcome.2.version.built.interface.state key == slot old.version.built.interface.state key do
        throw "partial inherited graph publication"

def scenario (settings : Settings) (policy : Policy) : Except String Nat :=
  match start settings policy 10000 with
  | .error error => .error (failureTag error)
  | .ok original => match original.invoke model watches ⟨"Delivery","EU",2⟩ (ConstructionWorkflow.admit 10000) with
    | .error _ => .error "warm source admission"
    | .ok (_,old) => do
      checkVersion settings old
      let oldCalls ← checkCalls settings policy old.version.built calls
      let next : Settings := {settings with swapped := !settings.swapped, data := {settings.data with input := settings.data.input+10,invoiceFee := 4}, conditional := !settings.conditional,overrideInvoice := if settings.conditional then some 77 else none}
      let nextPolicy := if policy == .aggregate then Policy.peak else .aggregate
      let updated := migrate old next nextPolicy 10000
      let newCalls ← match updated.1 with
        | .error error => .error ("upgrade:" ++ failureTag error)
        | .ok revision => do
          checkVersion next revision.snapshot
          unless revision.snapshot.version.built.generic.cache.size == 0 do throw "stale candidate cache"
          checkCalls next nextPolicy revision.snapshot.version.built calls
      refusedSource old (source {settings with forbidden := true} policy) 10000 "negative"
      refusedSource old (source {settings with baseInvoice := false,overrideInvoice := none,conditional := false,hazard := Hazard.opaque} policy) 10000 "opaque"
      refusedSource old (source {settings with baseInvoice := false,overrideInvoice := none,conditional := false,hazard := .cycle} policy) 10000 "cycle"
      refusedSource old (source {settings with baseInvoice := false,overrideInvoice := none,conditional := false,hazard := .source} policy) 10000
        (reprStr (ComputationError.source (Key := String) "legacy"))
      refusedSource old (source {settings with data := {settings.data with blocked := true}} policy) 10000
        (reprStr (ComputationError.introduced "blocked"))
      refusedSource old (source settings policy) 0 "budget"
      pure (oldCalls+newCalls)

def edgeCases : Except String Unit :=
  let settings : Settings := {data := {input := 30}}
  match start settings .aggregate 10000 with
  | .error error => .error (failureTag error)
  | .ok original => match original.invoke model watches ⟨"Delivery","EU",2⟩ (ConstructionWorkflow.admit 10000) with
    | .error _ => .error "edge warm"
    | .ok (_,old) => do
      let badGraphs : List (Prototype.C3.Graph × C4.Error) := [
        ([("Service",[]),("Service",[])],.duplicateNode "Service"),
        ([("Service",["Ghost"])],.unknownNode "Ghost"),
        ([("Service",["Service"])],.cycle "Service"),
        ([("Service",["L","L"]),("L",[])],.inconsistentOrder),
        ([("Service",["L","R"]),("L",["X","Y"]),("R",["Y","X"]),("X",[]),("Y",[])],.inconsistentOrder)]
      for (graph,error) in badGraphs do
        refusedSource old {source {settings with forbidden := true} .peak with graph} 0 ("inheritance:" ++ reprStr error)
      for hazard in [Hazard.source,.opaque,.cycle] do
        match start {settings with baseInvoice := false,hazard,overrideInvoice := some 77} .aggregate 10000 with
        | .error error => throw ("override failed to prune:" ++ failureTag error)
        | .ok shielded => unless slot shielded.version.built.interface.state "invoice" == (some 77,none) do
            throw "override pruned wrong inherited slot"
      refusedSource old (source {settings with data := {input := 30,discount := some 5}, baseInvoice := false,conditional := true} .aggregate) 10000 "opaque"
      -- Reversing two declarations in the same class must retain source order.
      let a : Fragment String Values "invoice" := .extend (.pure fun _ inherited => inherited.map (· + 7))
      let b : Fragment String Values "invoice" := .extend (.pure fun _ inherited => inherited.map (· * 3))
      let c : Fragment String Values "invoice" := .replace (.pure fun _ => .ok 5)
      let eval := fun fragments => ((compile "invoice" none fragments).evaluate (fun _ => none) ()).bind id
      unless (eval [a,b,c]).toOption == some 22 && (eval [b,a,c]).toOption == some 36 do
        throw "within-class fragment order"
      let modifier : Modifier String Values "invoice" := .need "absent" fun _ _ value => value
      match (compile "invoice" none [.extend modifier,.replace (.failure "parent")]).evaluate (fun _ => none) () with
      | .error (.missing "absent") => pure ()
      | _ => throw "modifier failure did not precede parent"

def run : IO Unit := do
  let _ ← IO.ofExcept edgeCases
  let mut count := 0
  let mut observations := 0
  for input in [0,30,91] do
    for discount in [none,some 5] do
      for swapped in [false,true] do
        for conditional in [false,true] do
          for scale in [1,3] do
            for policy in [Policy.aggregate,.peak] do
              let settings : Settings := {data := {input,discount},scale,surcharge := 7,swapped,conditional}
              let checked ← IO.ofExcept (scenario settings policy)
              count := count+1
              observations := observations+checked
  IO.println s!"INHERITED-SETTLEMENT-CONTROLS-OK scenarios={count} calls={observations} accepted-migrations={count} matrix-refusals={count*6} inheritance-refusals=5 shielded-hazards=3 conditional-opaque-refusal=1"
#eval run
end LeanPoo.Tests.InheritedSettlement
