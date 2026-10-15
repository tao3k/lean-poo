import LeanPoo.Functional.ServiceBundle

/-! Independent numerical, invocation, invalidation and atomic-refusal controls.
Refusing builders discriminate actual skipping from trace-only reuse claims. -/
namespace LeanPoo.Tests.ServiceBundle
open Functional Functional.ServiceBundle
open Functional.GeneralizedGraph

structure Expected where
  data : ConstructionWorkflow.Config
  policy : Policy
  overrideInvoice : Option Int := none
  coupon : Option Int := none

def numbers (expected : Expected) : List Int :=
  let c := expected.data
  let freight := 2+c.input/5
  let cover := 3+c.input/7
  let reserve := 10*freight+cover - (if c.expanded then c.discount.getD 0 else 0)
  let tax := 2+reserve/5
  let risk := c.input/(if c.discount.isSome then 3 else 6)
  let settlement := tax+risk
  let invoice := expected.overrideInvoice.getD (settlement+c.invoiceFee+expected.coupon.getD 0)
  let audit := 1+c.input/4
  [invoice+audit,invoice+audit,invoice,settlement,tax,risk,reserve,freight,cover,audit,0,c.input]

abbrev Observation := Option Int × Option String

def slot {current : Request} (candidate : Candidate current) (key : String) : Observation :=
  match candidate.cache.closed.raw key with
  | none => (none,none)
  | some (.ok value) => (some value,none)
  | some (.error error) => (none,some (reprStr error))

def view : (key : Service) → Result key → String
  | .quote, .ok value => "quote:" ++ toString value
  | .reserve, .ok (remaining,allowed) => "reserve:" ++ toString remaining ++ ":" ++ toString allowed
  | .cancel, .ok events => String.intercalate "|" ("cancel" :: events)
  | .quote, .error error | .reserve, .error error | .cancel, .error error => "error:" ++ error

def oracle (expected : Expected) : (key : Service) → Args key → String
  | .quote, call =>
    if call.service == "Forbidden" then "quote:0"
    else if call.units < 0 then "error:units"
    else
      let items := if call.service == "Delivery" then
        [((numbers expected)[0]!)*call.units,expected.data.input*call.units] ++
          (if call.region == "EU" && call.units > 0 then [2*call.units] else [])
        else [expected.data.input*call.units]
      let result := if expected.policy.pricing == .peak then items.foldl max 0 else items.foldl (· + ·) 0
      "quote:" ++ toString (result + if expected.policy.pricing == .peak then 11 else 7)
  | .reserve, units =>
    let total := (numbers expected)[0]!
    "reserve:" ++ toString (total-(units : Int)) ++ ":" ++ toString (decide ((units : Int) ≤ total))
  | .cancel, args =>
    if args.1 == "forbidden" then "error:missing:cancel"
    else if !args.2 then "error:cancel.guard"
    else "cancel|" ++ args.1 ++ "|invoice:" ++ toString ((numbers expected)[2]!)

abbrev Invocation := (key : Service) × Args key

def invocations : List Invocation :=
  (["Delivery","Preview","Forbidden"].flatMap fun service => ["EU","US"].flatMap fun region =>
    [-1,0,2,7].map fun units => ⟨.quote,⟨service,region,units⟩⟩) ++
  [⟨.reserve,0⟩,⟨.reserve,2⟩,⟨.reserve,100⟩,
    ⟨.cancel,("customer",true)⟩,⟨.cancel,("customer",false)⟩,⟨.cancel,("forbidden",true)⟩]

def checkCalls {current : Request} (expected : Expected) (candidate : Candidate current) : List Invocation → Except String Nat
  | [] => .ok 0
  | ⟨key,args⟩ :: rest =>
    match candidate.family.invoke model.generics current.policy candidate.interface key args with
    | .error _ => .error "typed family invocation"
    | .ok (result,family) => do
      unless view key result == oracle expected key args do
        throw ("family oracle:" ++ reprStr key ++ ":" ++ view key result)
      return 1 + (← checkCalls expected ⟨candidate.cache,family⟩ rest)

def stamp (version : Version) : List (Nat × List Object.DispatchShape) :=
  [Service.quote,.reserve,.cancel].map fun key =>
    ((version.candidate.family.table.get? key).map fun generic => (generic.cache.size,generic.cache.recent)).getD (0,[])

def warm (version : Version) : Except String Version :=
  match version.invoke model .quote ⟨"Delivery","EU",2⟩ (admit 10000) with
  | .error _ => .error "warm quote"
  | .ok (_,version) => match version.invoke model .reserve 2 (admit 10000) with
    | .error _ => .error "warm reserve"
    | .ok (_,version) => match version.invoke model .cancel ("customer",true) (admit 10000) with
      | .error _ => .error "warm cancel"
      | .ok (_,version) => .ok version

def checkGraph {current : Request} (expected : Expected) (candidate : Candidate current) : Except String Unit := do
  for (key,index) in (ConstructionWorkflow.keys.take 12).zipIdx do
    unless slot candidate key == (some ((numbers expected)[index]!),none) do throw ("cached graph oracle:" ++ key)
  unless slot candidate "discount" == (expected.data.discount,none) &&
      slot candidate "coupon" == (expected.coupon,none) do throw "cached optional capability"
  for key in ["blocked","permit","outside"] do
    unless slot candidate key == (none,none) do throw "cached absence"

structure Plan where
  edits : List Edit
  expected : Expected
  dirty : List String

def plans (expected : Expected) : List Plan :=
  let c := expected.data
  let flipped : Policy := {pricing := if expected.policy.pricing == .peak then .aggregate else .peak}
  let inputDirty := ["input","freight","cover","reserve","tax","risk","settlement","invoice","audit","release","total"]
  let discount := if c.discount.isSome then none else some 5
  let discountDirty := ["discount","risk","settlement","invoice","release","total"] ++
    if c.expanded then ["reserve","tax"] else []
  [⟨[],expected,[]⟩,
   ⟨[.policy flipped],{expected with policy := flipped},[]⟩,
   ⟨[.define "invoice" (ConstructionWorkflow.need "settlement" (· + (c.invoiceFee+9)))],
     {expected with data := {c with invoiceFee := c.invoiceFee+9}},["invoice","release","total"]⟩,
   ⟨[.setBase "input" (some (.ok (c.input+10)))],{expected with data := {c with input := c.input+10}},inputDirty⟩,
   ⟨[.setBase "discount" (discount.map Except.ok)],{expected with data := {c with discount}},discountDirty⟩,
   ⟨[.remove "permit"],expected,["permit"]⟩,
   ⟨[.support ConstructionWorkflow.keys.reverse],expected,ConstructionWorkflow.keys⟩,
   ⟨[.setBase "input" (some (.ok (c.input+10))),.define "invoice" (.pure fun _ => .ok 77)],
     {expected with data := {c with input := c.input+10},overrideInvoice := some 77},inputDirty⟩,
   ⟨[.setBase "blocked" none],expected,["blocked","gate","total"]⟩,
   ⟨[.define "coupon" (.pure fun _ => .ok 4),.define "invoice" (ConstructionWorkflow.both "settlement" "coupon" (· + ·))],
     {expected with data := {c with invoiceFee := 0},coupon := some 4},["coupon","invoice","release","total"]⟩]

def refused (old : Version) (edits : List Edit) (allow : String → Bool) (limit : Int) (tag : String) : Except String Unit :=
  let outcome := revise old edits allow limit
  match outcome.1 with
  | .ok _ => .error ("unexpected acceptance:" ++ tag)
  | .error error => do
    unless failureTag error == tag do throw ("first refusal:" ++ failureTag error ++ " expected:" ++ tag)
    unless stamp outcome.2 == stamp old do throw "refused candidate changed a warm generic cache"
    for key in ConstructionWorkflow.keys do
      unless slot outcome.2.candidate key == slot old.candidate key do throw "partial construction publication"
    unless (quoteProbe outcome.2.candidate,reserveProbe outcome.2.candidate,cancelProbe outcome.2.candidate) ==
        (quoteProbe old.candidate,reserveProbe old.candidate,cancelProbe old.candidate) do throw "mixed generic generation"

def scenario (expected : Expected) : Except String (Nat × Nat × Nat) :=
  match start expected.data expected.policy 10000 with
  | .error error => .error (failureTag error)
  | .ok original => match warm original with
    | .error error => .error error
    | .ok old => do
      unless old.candidate.cache.evaluated.length == 15 && (stamp old).all (fun entry => entry.1 > 0) do
        throw "cold materialization/warm heterogeneous caches"
      checkGraph expected old.candidate
      let mut observations ← checkCalls expected old.candidate invocations
      let mut rebuilds := 0
      let mut retained := 0
      for plan in plans expected do
        -- Every clean constructor is refusing, rather than merely uncounted.
        let outcome := revise old plan.edits (plan.dirty.contains ·) 10000
        match outcome.1 with
        | .error error => throw ("selective stage:" ++ failureTag error)
        | .ok prepared =>
          let candidate := prepared.candidate
          unless candidate.cache.evaluated.length == plan.dirty.length &&
              candidate.cache.evaluated.all (plan.dirty.contains ·) &&
              plan.dirty.all (candidate.cache.evaluated.contains ·) &&
              candidate.cache.reused.length + candidate.cache.evaluated.length ==
                (GeneralizedMOP.redefine old.request plan.edits).graph.keys.length do
            throw "actual fresh/reused materialization trace"
          unless (candidate.family.table.get? .quote).all (fun generic => generic.cache.size == 0) &&
              (candidate.family.table.get? .reserve).all (fun generic => generic.cache.size == 0) &&
              (candidate.family.table.get? .cancel).all (fun generic => generic.cache.size == 0) do throw "stale method cache in new family"
          checkGraph plan.expected candidate
          observations := observations + (← checkCalls plan.expected candidate invocations)
          rebuilds := rebuilds + candidate.cache.evaluated.length
          retained := retained + candidate.cache.reused.length
      refused old [.policy {expected.policy with brokenReserve := true}] (fun _ => false) 10000 ("registration:" ++ reprStr Service.reserve)
      refused old [.policy {expected.policy with forbiddenCancel := true}] (fun _ => false) 10000 ("negative:" ++ reprStr Service.cancel)
      refused old [.policy {expected.policy with reserveShift := 1}] (fun _ => false) 10000 "generic-coherence"
      refused old [.policy {expected.policy with cancelShift := 1}] (fun _ => false) 10000 "generic-coherence"
      refused old [.setBase "blocked" (some (.ok 1))] (fun _ => true) 10000 "construction-result"
      refused old [.setBase "permit" (some (.ok 1))] (· == "permit") 10000 ("negative:" ++ reprStr Service.quote)
      refused old [.remove "input"] (fun _ => true) 10000 "construction-result"
      refused old [.define "input" (ConstructionWorkflow.need "total" id)] (fun _ => false) 10000 "cycle"
      refused old [.define "invoice" (.failure "invoice")] (fun _ => true) 10000 "construction-result"
      refused old [.define "invoice" (ConstructionWorkflow.need "settlement" (· + 9))] (fun _ => false) 10000 "builder:invoice"
      refused old [] (fun _ => false) 0 "budget"
      refused old [.support (ConstructionWorkflow.keys.filter (· != "input"))] (fun _ => false) 10000 "unknown"
      return (observations,rebuilds,retained)

def run : IO Unit := do
  let mut cases := 0
  let mut observations := 0
  let mut rebuilds := 0
  let mut retained := 0
  for input in [0,30,91] do
    for discount in [none,some 5] do
      for expanded in [false,true] do
        for pricing in [ConstructionWorkflow.Policy.aggregate,.peak] do
          let expected : Expected := ⟨{input,discount,expanded,invoiceFee := 2},{pricing},none,none⟩
          let (calls,fresh,reused) ← IO.ofExcept (scenario expected)
          cases := cases+1
          observations := observations+calls
          rebuilds := rebuilds+fresh
          retained := retained+reused
  IO.println s!"SERVICE-BUNDLE-CONTROLS-OK settings={cases} accepted={cases*10} refused={cases*12} heterogeneous-call-observations={observations} revision-resolver-evaluations={rebuilds} retained-resolvers={retained} retained-builders-refuse=true"
#eval run
end LeanPoo.Tests.ServiceBundle
