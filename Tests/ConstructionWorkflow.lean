import LeanPoo.Functional.ConstructionWorkflow

/-! Independent arithmetic, recurrence, matching and refusal controls for the
finite generalized MOP. The oracle does not call the analyzer or interpreter. -/
namespace LeanPoo.Tests.ConstructionWorkflow
open Functional Functional.ConstructionWorkflow Functional.GeneralizedMOP Functional.GeneralizedGraph

abbrev Observation := Option Int × Option String

def observe : Option (Outcome String Values key) → Observation
  | none => (none,none)
  | some (.ok value) => (some value,none)
  | some (.error error) => (none,some (reprStr error))

def values (config : Config) : List Int :=
  let freight := 2 + config.input/5
  let cover := 3 + config.input/7
  let reserve := 10*freight+cover - if config.expanded then config.discount.getD 0 else 0
  let tax := 2+reserve/5
  let risk := config.input / if config.discount.isSome then 3 else 6
  let settlement := tax+risk
  let invoice := settlement+config.invoiceFee
  let audit := 1+config.input/4
  let release := invoice+audit
  [release,release,invoice,settlement,tax,risk,reserve,freight,cover,audit,0,config.input]

def expected (config : Config) (key : String) : Observation :=
  if let some index := keys.idxOf? key then
    if index < 12 then
      if config.blocked && (key == "gate" || key == "total") then
        (none,some (reprStr (ComputationError.introduced "blocked")))
      else (some ((values config)[index]!),none)
    else if key == "discount" then (config.discount,none)
    else if key == "blocked" && config.blocked then (some 1,none)
    else if key == "permit" && config.permit then (some 1,none)
    else (none,none)
  else (none,none)

/-- Previous approximations, not topological in-place updates. -/
def finite (config : Config) : Nat → List Int
  | 0 => List.replicate 12 0
  | depth+1 =>
    let v := finite config depth
    [v[1]!,v[2]!+v[9]!,v[3]!+config.invoiceFee,v[4]!+v[5]!,2+v[6]!/5,
      v[11]! / (if depth > 0 && config.discount.isSome then 3 else 6),
      10*v[7]!+v[8]! - (if config.expanded && depth > 0 then config.discount.getD 0 else 0),
      2+v[11]!/5,3+v[11]!/7,1+v[11]!/4,0,config.input]

def actionView : Action Int → Observation
  | .ok value => (some value,none)
  | .error error => (none,some error)

def callExpected (config : Config) (policy : Policy) (call : Call) : Observation :=
  if call.service == "Forbidden" then (some 0,none)
  else if call.units < 0 then (none,some "units")
  else
    let contributions := if call.service == "Delivery" then
      [((values config)[0]!) * call.units, config.input * call.units] ++
        if call.region == "EU" && call.units > 0 then [2*call.units] else []
      else [config.input * call.units]
    let result := if policy == .aggregate then contributions.foldl (· + ·) 0
      else contributions.foldl max 0
    (some (result + if policy == .aggregate then 7 else 11),none)

def calls : List Call := ["Delivery","Preview","Forbidden"].flatMap fun service =>
  ["EU","US"].flatMap fun region => [-1,0,2,5].map fun units => ⟨service,region,units⟩

def checkCalls (config : Config) (policy : Policy) (built : Built) : List Call → Except String Nat
  | [] => .ok 0
  | call :: rest => match built.invoke model watches call with
    | .error _ => .error "unexpected invocation arity"
    | .ok (result,next) => do
      unless actionView result == callExpected config policy call do
        throw s!"dispatch oracle {repr call} {repr config} {repr policy}: {repr (actionView result)}"
      unless next.generic.cache.size > 0 do throw "ordinary calls did not warm the cache"
      return 1 + (← checkCalls config policy next rest)

def checkGraph (config : Config) (built : Built) : Except String Unit := do
  for key in keys ++ ["outside"] do
    unless observe (built.interface.state key) == expected config key do
      throw s!"graph oracle {key}: {repr (observe (built.interface.state key))}"
  let metadata := built.inspect model watches
  unless metadata.nodes.length == 15 && metadata.arity == 2 && metadata.declarations == 4 do
    throw "incomplete inspected metadata"
  for node in metadata.nodes do
    for dep in node.2.values ++ node.2.presences do
      unless metadata.order.idxOf dep < metadata.order.idxOf node.1 do throw "inspection lost schedule edges"
  unless built.scheduled.invalidates (· == "input") "total" &&
      !(built.scheduled.invalidates (· == "permit") "total") &&
      built.scheduled.invalidates (· == "blocked") "total" &&
      built.scheduled.invalidates (· == "discount") "risk" do
    throw "transitive value/presence invalidation"
  -- All nodes, including undeclared base slots, are covered by universal closure.
  for key in keys ++ ["outside"] do
    unless observe (built.request.graph.resolve key built.closed.raw) == observe (built.closed.raw key) do
      throw "whole raw fixed point"

/-- Every refusal is checked against the same warm old version. -/
def refused (old : Version) (edits : List (Redefinition String Values Policy))
    (limit : Int) (tag : String) : Except String Unit :=
  let outcome := migrate old edits limit
  match outcome.1 with
  | .ok _ => .error ("accepted refusal:" ++ tag)
  | .error error => do
    unless publicationTag error == tag do throw ("first refusal:" ++ publicationTag error ++ " expected:" ++ tag)
    unless outcome.2.built.generic.cache.size == old.built.generic.cache.size &&
        outcome.2.built.interface.layout == old.built.interface.layout &&
        outcome.2.approval.total == old.approval.total do throw "refusal changed old snapshot"
    for key in keys do
      unless observe (outcome.2.built.interface.state key) == observe (old.built.interface.state key) do
        throw "partial graph publication"

def checkMigration (config : Config) (old : Version) : Except String Nat :=
  match warm old ⟨"Delivery","EU",2⟩ with
  | .error error => .error error
  | .ok (_,old) => do
    let updated : Config := {config with input := config.input+10,discount := some 5,expanded := true,invoiceFee := 7}
    let newReserve : Node "reserve" := .both (both "freight" "cover" (fun l r => 10*l+r))
      (.read "discount" fun _ value => value.getD (.ok 0))
      (fun _ reserve discount => do return (← reserve) - (← discount))
    let edits : List (Redefinition String Values Policy) := [
      .setBase "input" (some (.ok updated.input)),.setBase "discount" (some (.ok 5)),
      .define "reserve" newReserve,.define "invoice" (need "settlement" (· + 7)),
      .support keys.reverse,.policy .peak]
    let outcome := migrate old edits 10000
    let accepted ← match outcome.1 with
      | .error error => .error ("joint migration:" ++ publicationTag error)
      | .ok revision => do
        unless revision.snapshot.built.interface.layout == "settlement/v2" &&
            revision.snapshot.built.generic.cache.size == 0 do throw "joint policy/cache publication"
        checkGraph updated revision.snapshot.built
        checkCalls updated .peak revision.snapshot.built calls
    refused old [.remove "input"] 10000 (reprStr (ComputationError.missing "input"))
    refused old [.define "input" (need "total" id)] 10000 "cycle"
    refused old [.support (keys.filter (· != "input"))] 10000 "unknown"
    refused old [.define "input" (.opaque fun _ _ => .ok (.ok 1))] 10000 "opaque"
    refused old [.define "input" (.choose (.pure fun _ => false) (fun _ b => b)
      (.opaque fun _ _ => .ok (.ok 1)) (.pure fun _ => .ok 2))] 10000 "opaque"
    refused old [.setBase "blocked" (some (.ok 1))] 10000 (reprStr (ComputationError.introduced "blocked"))
    refused old [.setBase "permit" (some (.ok 1))] 10000 "negative"
    refused old [.policy .malformed] 10000 "arity"
    refused old [] 0 "budget"
    refused old [.define "total" (.pure fun _ => .ok (-1))] 10000 "negative-total"
    refused old [.remove "total"] 10000 "missing:total"
    -- Construction has priority over later negative/admission failures.
    refused old [.define "input" (need "total" id),.setBase "permit" (some (.ok 1))] 0 "cycle"
    return accepted

def checkScenario (config : Config) (policy : Policy) : Except String (Nat × Nat) :=
  match start config policy 10000 with
  | .error error => .error (publicationTag error)
  | .ok version => do
    checkGraph config version.built
    let observations ← checkCalls config policy version.built calls
    let revisedCalls ← checkMigration config version
    -- Compare finite inheritance through and beyond the longest propagation path.
    for depth in (if config.input == 30 && config.invoiceFee == 7 && config.expanded && policy == .aggregate then List.range 13 else []) do
      let state := (graph config).protocol.approximate keys (graph config).base
        (fun key => if key ∈ keys.take 12 then some (.ok 0) else none) depth
      for (key,index) in (keys.take 12).zipIdx do
        unless observe (state key) == (some ((finite config depth)[index]!),none) do
          throw s!"finite recurrence {key} depth={depth}"
    pure (observations+revisedCalls,13)

/-- Presence is independent of successful evaluation: inspect must not turn a
failed optional value into absence, and deny must reject even a failed provider. -/
def checkPresenceFailures : Except String Unit :=
  match start {input := 30} .aggregate 10000 with
  | .error error => .error (publicationTag error)
  | .ok old => do
    let optionalError : Outcome String Values "discount" := .error (.source "discount")
    let outcome := migrate old [.setBase "discount" (some optionalError)] 10000
    match outcome.1 with
    | .error error => throw ("inspect invoked failed optional value:" ++ publicationTag error)
    | .ok revision =>
      unless observe (revision.snapshot.built.interface.state "risk") == (some 10,none) do
        throw "failed optional value was treated as absent"
    refused old [.setBase "blocked" (some (.error (.source "blocked")))] 10000
      (reprStr (ComputationError.introduced "blocked"))
    refused old [.define "input" (.failure "source-input")] 10000
      (reprStr (ComputationError.source (Key := String) "source-input"))
    refused old [.setBase "discount" (some optionalError),
      .define "reserve" (.read "discount" fun _ value => value.getD (.ok 0))] 10000
      (reprStr (ComputationError.source (Key := String) "discount"))

def run : IO Unit := do
  let _ ← IO.ofExcept checkPresenceFailures
  let mut scenarios := 0
  let mut observations := 0
  let mut revisions := 0
  for input in [0,6,30,91] do
    for discount in [none,some 0,some 5] do
      for expanded in [false,true] do
        for fee in [0,7] do
          for policy in [Policy.aggregate,.peak] do
            let config : Config := {input,discount,expanded,invoiceFee := fee}
            let (calls,revised) ← IO.ofExcept (checkScenario config policy)
            scenarios := scenarios+1
            observations := observations+calls
            revisions := revisions+revised
  IO.println s!"CONSTRUCTION-WORKFLOW-CONTROLS-OK scenarios={scenarios} calls={observations} migration-checks={revisions} finite-node-observations={3*13*12}"

#eval run
end LeanPoo.Tests.ConstructionWorkflow
