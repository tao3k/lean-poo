import LeanPoo.Functional.PolicyPublication

/-! Future-work controls: configuration equality, data dependency equality,
method observations and refusal order are compared independently. -/
namespace LeanPoo.Tests.PolicyPublication
open Prototype Prototype.Generalized Functional.PolicyPublication
open TariffComponent (Account Local Fragment Action summary)

def expectedRates (key : Int) : List Int :=
  let price := 6+key
  let freight := 2+price/5
  let cover := 3+price/7
  let held := 1+10*(freight/3)+cover/3
  let levy := 2+10*(price/4)+held/5
  let exposure := 3+price/6
  let settled := 1+1000*(price/9)+100*(held/7)+10*(levy/4)+exposure/4
  let invoiced := 2+settled/10
  let audited := 3+price/4
  [price,freight,cover,held,levy,exposure,settled,invoiced,audited,1+10*(invoiced/4)+audited/4]

def expectedInputs (policy : Policy) (key : Int) : List (List Int) :=
  let v := expectedRates key
  [[key],[v[0]!/5],[v[0]!/7],[v[1]!/3,v[2]!/3],[v[0]!/4,v[3]!/5],[v[0]!/6],
    [v[0]!/9,v[3]!/7,v[4]!/4,v[5]!/4],
    [policy.invoiceFee,v[6]!/10],[policy.auditFee,v[0]!/4],[policy.releaseFee,v[7]!/4,v[8]!/4]]

def initial : Policy := ⟨0,0,0⟩
def allFees : Policy := ⟨5,3,7⟩
def expectedFlags (policy : Policy) (key : Int) : List Bool :=
  (expectedInputs initial 0).zipWith (· == ·) (expectedInputs policy key)
def refusal (mask stage : Nat) : Bool := (mask / 2^stage) % 2 == 1
def names := ["pricing","shipping","insurance","reserve","tax","risk","settlement","invoice","audit","release"]
def fees (policy : Policy) : List Int := List.replicate 7 0 ++ [policy.invoiceFee,policy.auditFee,policy.releaseFee]

def expectedError (policy : Policy) (key : Int) (mask : Nat) : Option String :=
  let flags := expectedFlags policy key
  names.zipIdx |>.findSome? fun (name,stage) =>
    if refusal mask stage && !flags[stage]! then some (name ++ ".construction") else none

def expectedOutcome (policy : Policy) (values : List Int) (units : Int) (ledger : List String) :
    Option Int × Option String × List String := Id.run do
  let mut trace := ledger
  let mut total := 0
  for ((name,value),fee) in (names.zip values).zip (fees policy) do
    trace := trace ++ [name ++ ".enter"]
    if units < 0 then return (none,some "units",trace)
    if (name == "shipping" && units > 8) || (name == "tax" && units > 6) ||
        (name == "settlement" && units > 4) || (name == "invoice" && units > 3) || (name == "release" && units > 2) then
      return (none,some (name ++ ".limit"),trace)
    trace := trace ++ [name,name ++ ".exit"]
    total := total + units*value+fee
  return (some total,none,trace)

def finiteRates (key : Int) : Nat → List Int
  | 0 => List.replicate 10 1
  | depth+1 =>
    let v := finiteRates key depth
    [6+key,2+v[0]!/5,3+v[0]!/7,1+10*(v[1]!/3)+v[2]!/3,
      2+10*(v[0]!/4)+v[3]!/5,3+v[0]!/6,
      1+1000*(v[0]!/9)+100*(v[3]!/7)+10*(v[4]!/4)+v[5]!/4,
      2+v[6]!/10,3+v[0]!/4,1+10*(v[7]!/4)+v[8]!/4]

-- A nonidentity raw/public layout, including the explicit policy context.
def swapLayout (A B C : Type) : DictionaryBridge ((A × B) × C) (C × (B × A)) :=
  ⟨(fun raw => (raw.2,raw.1.2,raw.1.1)),(fun raw => ((raw.2.2,raw.2.1),raw.1)),fun _ => rfl,fun _ => rfl⟩

def run : IO Unit := do
  let original ← IO.ofExcept (publish initial 0)
  let mut revisions := 0
  let mut accepted := 0
  let mut refused := 0
  let mut observations := 0
  let mut finite := 0
  let scenarios : List (Policy × Int) := [
    (initial,0),(⟨5,0,0⟩,0),(⟨0,3,0⟩,0),(⟨0,0,7⟩,0),(allFees,0),(initial,14),(allFees,2)]
  let ledgers : List (List String) := [[],["prefix"]]
  let unitsCases : List Int := [-1,0,2,3,4,5,7,9]
  for (policy,key) in scenarios do
    for mask in List.range 1024 do
      revisions := revisions+1
      match revise original policy key (refusal mask) with
      | .error error =>
        refused := refused+1
        unless expectedError policy key mask == some error do throw (IO.userError "policy/data first refusal")
        unless summary ((checkout (assemble original).interface 2).run ["retained"]) ==
            expectedOutcome initial (expectedRates 0) 2 ["retained"] do throw (IO.userError "refused policy revision changed old publication")
      | .ok revision =>
        accepted := accepted+1
        unless (expectedError policy key mask).isNone && revision.flags == expectedFlags policy key do
          throw (IO.userError "configuration omitted from construction key")
        let closed := assemble revision.publication
        unless rates closed.interface == expectedRates key do throw (IO.userError "policy altered numerical metadata")
        let fields := closed.transport (swapLayout _ _ _) (swapLayout _ _ _)
        for units in ([2,3] : List Int) do
          for ledger in ledgers do
            for service in [closed.interface,(swapLayout _ _ _).fromFields fields.interface] do
              observations := observations+1
              unless summary ((checkout service units).run ledger) == expectedOutcome policy (expectedRates key) units ledger do
                throw (IO.userError "ten-component complete action / policy / representation")
    let revised ← IO.ofExcept (revise original policy key (fun _ => false))
    for units in unitsCases do
      for ledger in ledgers do
        observations := observations+1
        unless summary ((checkout (assemble revised.publication).interface units).run ledger) ==
            expectedOutcome policy (expectedRates key) units ledger do throw (IO.userError "ten-stage distinct error prefix")
  for policy in [initial,allFees] do
    for key in ([0,14] : List Int) do
      for depth in List.range 9 do
        let service := (wholeProtocol policy key).observe fragments wholeBase wholeBase depth
        unless rates service == finiteRates key depth do throw (IO.userError "configured finite metadata")
        for units in unitsCases do
          for ledger in ledgers do
            finite := finite+1
            let expected := if depth == 0 then (none,some "missing",ledger)
              else expectedOutcome policy (if depth == 8 then expectedRates key else finiteRates key (depth-1)) units ledger
            unless summary ((checkout service units).run ledger) == expected do throw (IO.userError "configured method self timing")
  -- Use the configuration API directly: same dependency, changed policy.
  let oldInvoice := original.branches.leftClosed
  let refusedConfig := oldInvoice.refreshConfiguration (family := configured) 5
    (fork.selectLeft (initial,(Base.assemble original.upstream).interface)).2
    (fun _ _ => Except.error "changed policy needs fresh admission")
  unless refusedConfig.toOption.isNone do throw (IO.userError "configuration API trusted dependency equality alone")
  IO.println s!"POLICY-PUBLICATION-CONTROLS-OK revisions={revisions} accepted={accepted} refused={refused} complete-observations={observations} finite-observations={finite} ten-components actual-policy keys full-refusal-masks retained-upstream recooked-interface"
#eval run

#print axioms Functional.PolicyPublication.assemble
#print axioms Functional.PolicyPublication.retained_audit
#print axioms Functional.PolicyPublication.retained_release
#print axioms Functional.PolicyPublication.changed_policy_observation
#print axioms Functional.PolicyPublication.policyCook_error
#print axioms Closed.reindexSelf_view
#print axioms Closed.refreshConfiguration_reuses
#print axioms Closed.refreshConfiguration_error
end LeanPoo.Tests.PolicyPublication
