import LeanPoo.Functional.SharedSettlement

/-! Independent controls for the future-work seven-component shared-context
workflow. Arithmetic, invalidation and failure order do not use its compiler. -/
namespace LeanPoo.Tests.SharedSettlement
open Prototype Prototype.Generalized Functional.SharedSettlement
open TariffComponent (Account Local Fragment Action family summary)

def expectedRates (key : Int) : List Int :=
  let price := 6+key
  let freight := 2+price/5
  let cover := 3+price/7
  let held := 1+10*(freight/3)+cover/3
  let levy := 2+10*(price/4)+held/5
  let exposure := 3+price/6
  [price,freight,cover,held,levy,exposure,1+1000*(price/9)+100*(held/7)+10*(levy/4)+exposure/4]

def expectedInputs (key : Int) : List (List Int) :=
  let v := expectedRates key
  [[key],[v[0]!/5],[v[0]!/7],[v[1]!/3,v[2]!/3],[v[0]!/4,v[3]!/5],
    [v[0]!/6],[v[0]!/9,v[3]!/7,v[4]!/4,v[5]!/4]]

def expectedFlags (old revised : Int) : List Bool := (expectedInputs old).zipWith (· == ·) (expectedInputs revised)
def refusal (mask stage : Nat) : Bool := (mask / 2^stage) % 2 == 1
def names := ["pricing","shipping","insurance","reserve","tax","risk","settlement"]

def expectedError (old revised : Int) (mask : Nat) : Option String :=
  let flags := expectedFlags old revised
  names.zipIdx |>.findSome? fun (name,stage) =>
    if refusal mask stage && !flags[stage]! then some (name ++ ".construction") else none

def expectedOutcome (values : List Int) (units : Int) (ledger : List String) :
    Option Int × Option String × List String := Id.run do
  let mut trace := ledger
  let mut total := 0
  for (name,value) in names.zip values do
    trace := trace ++ [name ++ ".enter"]
    if units < 0 then return (none,some "units",trace)
    if (name == "shipping" && units > 8) || (name == "tax" && units > 6) || (name == "settlement" && units > 4) then
      return (none,some (name ++ ".limit"),trace)
    trace := trace ++ [name,name ++ ".exit"]
    total := total + units*value
  return (some total,none,trace)

-- Each edge reads the preceding whole raw approximation. The root and reserve
-- have direct edges to later stages as well as paths through earlier joins.
def finiteRates (key : Int) : Nat → List Int
  | 0 => [1,1,1,1,1,1,1]
  | depth+1 =>
      let v := finiteRates key depth
      [6+key,2+v[0]!/5,3+v[0]!/7,1+10*(v[1]!/3)+v[2]!/3,
        2+10*(v[0]!/4)+v[3]!/5,3+v[0]!/6,
        1+1000*(v[0]!/9)+100*(v[3]!/7)+10*(v[4]!/4)+v[5]!/4]

def layout (A : Type) :
    DictionaryBridge ((((A × (A × A)) × A) × (A × A)) × A) (A × (A × (A × (A × (A × (A × A)))))) :=
  ⟨(fun raw => (raw.1.1.1.1,raw.1.1.1.2.1,raw.1.1.1.2.2,raw.1.1.2,raw.1.2.1,raw.1.2.2,raw.2)),
    (fun raw => ((((raw.1,(raw.2.1,raw.2.2.1)),raw.2.2.2.1),(raw.2.2.2.2.1,raw.2.2.2.2.2.1)),raw.2.2.2.2.2.2)),
    fun _ => rfl,fun _ => rfl⟩

def run : IO Unit := do
  let mut revisions := 0
  let mut accepted := 0
  let mut refused := 0
  let mut observations := 0
  let mut finite := 0
  let keys : List Int := [0,1,2,3,14]
  let unitsCases : List Int := [-1,0,2,5,7,9]
  let ledgers : List (List String) := [[],["prefix"]]
  for old in keys do
    let original ← IO.ofExcept (publish old)
    unless rates (assemble original).interface == expectedRates old do throw (IO.userError "initial multi-level arithmetic")
    for revised in keys do
      for mask in List.range 128 do
        revisions := revisions + 1
        match revise original revised (refusal mask) with
        | .error error =>
          refused := refused + 1
          unless expectedError old revised mask == some error do throw (IO.userError "multi-level first construction refusal")
          unless summary ((checkout (assemble original).interface 2).run ["retained"]) ==
              expectedOutcome (expectedRates old) 2 ["retained"] do throw (IO.userError "refusal changed old shared publication")
        | .ok revision =>
          accepted := accepted + 1
          unless (expectedError old revised mask).isNone && revision.flags == expectedFlags old revised do
            throw (IO.userError "shared dependency or contextual join omitted from invalidation")
          let closed := assemble revision.publication
          unless rates closed.interface == expectedRates revised do throw (IO.userError "revised shared arithmetic")
          let fields := closed.transport (layout Account) (layout Local)
          for units in unitsCases do
            for ledger in ledgers do
              for service in [closed.interface,(layout Local).fromFields fields.interface] do
                observations := observations + 1
                unless summary ((checkout service units).run ledger) == expectedOutcome (expectedRates revised) units ledger do
                  throw (IO.userError "shared component cardinality / seven-stage ledger / representation")
    for depth in List.range 7 do
      let service := (wholeProtocol old).observe fragments wholeBase wholeBase depth
      unless rates service == finiteRates old depth do throw (IO.userError "shared context finite propagation")
      for units in unitsCases do
        for ledger in ledgers do
          finite := finite + 1
          let expected := if depth == 0 then (none,some "missing",ledger)
            else expectedOutcome (finiteRates old (depth-1)) units ledger
          unless summary ((checkout service units).run ledger) == expected do throw (IO.userError "multi-level method self timing")
  let original ← IO.ofExcept (publish 2)
  let contextOnly ← IO.ofExcept (revise original 3 (fun _ => false))
  unless contextOnly.later.left.reused && contextOnly.later.right.reused && !contextOnly.final.reused do
    throw (IO.userError "both reused branches were mistaken for unchanged contextual join")
  match revise original 3 (fun stage => stage == 6) with
  | .error "settlement.construction" => pure ()
  | _ => throw (IO.userError "context-only invalidation bypassed refusing final constructor")
  IO.println s!"SHARED-SETTLEMENT-CONTROLS-OK revisions={revisions} accepted={accepted} refused={refused} complete-observations={observations} finite-observations={finite} seven-components full-refusal-masks shared-context retained-branches-changed-join"
#eval run

-- Keeping the remaining branch/reserve metadata fixed does not license retaining a
-- join when its explicitly selected shared-root band changes.
theorem changed_shared_context_not_fixed (oldRoot revisedRoot : Int) (tail : Int × (Int × Int))
    (rate : Int) (rest : List Fragment)
    (original : Closed (finalFamily (oldRoot,tail)) (.inl rate :: rest) base)
    (changed : revisedRoot ≠ oldRoot) :
    (finalFamily (revisedRoot,tail)).step (.inl rate :: rest) original.raw base ≠ original.raw := by
  intro fixed
  have before := congrArg Account.rate original.fixed
  have after := congrArg Account.rate fixed
  have rate_step (root : Int) (raw : Account) :
      ((finalFamily (root,tail)).step (.inl rate :: rest) raw base).rate =
        rate + (1000*root + 100*tail.1 + 10*tail.2.1 + tail.2.2) := by
    change ((family (finalWeight (root,tail))).step (.inl rate :: rest) raw base).rate = _
    rw [TariffComponent.family_step]
    rfl
  rw [rate_step] at before after
  omega

-- Pulling a fork into a wider context preserves its complete two interfaces.
theorem pulled_back_interfaces (context : EarlyService)
    (publication : laterSpec.Publication (sharedView context)) :
    (publication.pullback sharedView context).closed.interface = publication.closed.interface :=
  publication.pullback_interface sharedView context

#print axioms Functional.SharedSettlement.assemble
#print axioms Functional.SharedSettlement.retained_risk
#print axioms Functional.SharedSettlement.retained_final
#print axioms changed_shared_context_not_fixed
#print axioms pulled_back_interfaces
#print axioms DependencyFork.Refresh.joinWith_same_view
end LeanPoo.Tests.SharedSettlement
