import LeanPoo.Prototype.GeneralizedChain
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: pricing → shipping → insurance → settlement permit.
The four closures are joined through nested existing dependent components.
Construction refusal and public method refusal have distinct observable traces. -/
namespace LeanPoo.Tests.GeneralizedChain
open Prototype Prototype.Generalized
open TariffComponent (Account Local Fragment Action family closeLocal mark summary)

def stageFragments (rate : Int) (name : String) (limit : Option Int := none) : List Fragment := [
  .inl rate,
  .inr (fun _ => .around (fun next units => do
    mark (name ++ ".enter")
    if units < 0 then throw "units"
    match limit with
    | some bound => if units > bound then throw (name ++ ".limit")
    | none => pure ()
    let result ← next ()
    mark (name ++ ".exit")
    return result)),
  .inr (fun self => .primary (fun _ units => do mark name; return units * self.get))]

def pricing := stageFragments 6 "pricing"
def shipping := stageFragments 2 "shipping" (some 8)
def insurance := stageFragments 3 "insurance"
def permit := stageFragments 1 "permit" (some 4)
def base : Account := ⟨1,{}⟩
def priceView (viewed : Local) : Int := viewed.rate / 5
def shipView (viewed : Local) : Int := viewed.rate / 3
def insuranceView (viewed : Local) : Int := viewed.rate / 2

abbrev chain : DependencyChain Int :=
  .link family pricing base priceView (
    .link family shipping base shipView (
      .link family insurance base insuranceView (
        .link family permit base (fun _ => ()) .done)))

def builder (name : String) (fragments : List Fragment) (refuse : Bool) (dependency : Int) :
    Except String (Closed (family dependency) fragments base) :=
  if refuse then .error (name ++ ".construction") else closeLocal dependency fragments base

def builders (refuse : Nat → Bool := fun _ => false) : chain.Builders String :=
  (builder "pricing" pricing (refuse 0),
   builder "shipping" shipping (refuse 1),
   builder "insurance" insurance (refuse 2),
   builder "permit" permit (refuse 3),())

def pairFragments (left : List A) (right : List B) : List (Sum A B) :=
  left.map Sum.inl ++ right.map Sum.inr

def first (dependency : Int) := DependentComponents.pair (family dependency) family priceView
def second (dependency : Int) := DependentComponents.pair (first dependency).protocol family (fun viewed => shipView viewed.2)
def third (dependency : Int) := DependentComponents.pair (second dependency).protocol family (fun viewed => insuranceView viewed.2)
def fragments := pairFragments (pairFragments (pairFragments pricing shipping) insurance) permit
def wholeBase := (((base,base),base),base)

/-- Convert the chain's typed local evidence into a whole fixed-point witness.
Each nested prefix is the next edge's upstream component. -/
def assemble {dependency : Int} (published : chain.Publication dependency) :
    Closed (third dependency).protocol fragments wholeBase := by
  let two := DependentComponents.closePair priceView published.1 published.2.1
  let middle := published.2.2.1.reuseDependency (shipView two.interface.2)
    (by rw [DependentComponents.closePair_interface])
  let three := DependentComponents.closePair (fun viewed => shipView viewed.2) two middle
  let last := published.2.2.2.1.reuseDependency (insuranceView three.interface.2)
    (by rw [DependentComponents.closePair_interface]; rfl)
  exact DependentComponents.closePair (fun viewed => insuranceView viewed.2) three last

theorem assemble_interface {dependency : Int} (published : chain.Publication dependency) :
    (assemble published).interface =
      (((published.1.interface,published.2.1.interface),published.2.2.1.interface),published.2.2.2.1.interface) := by rfl

abbrev Service := ((Local × Local) × Local) × Local

def checkout (service : Service) (units : Int) : Action Int := do
  let price ← service.1.1.1.price units
  let freight ← service.1.1.2.price units
  let cover ← service.1.2.price units
  let permitCost ← service.2.price units
  return price + freight + cover + permitCost

def rates (service : Service) : List Int :=
  [service.1.1.1.rate,service.1.1.2.rate,service.1.2.rate,service.2.rate]

-- These controls calculate rates/dependencies without the chain or compiler.
def expectedRates (dependency : Int) : List Int :=
  let root := 6 + dependency
  let freight := 2 + root / 5
  let cover := 3 + freight / 3
  [root,freight,cover,1 + cover / 2]

def expectedInputs (dependency : Int) : List Int :=
  let values := expectedRates dependency
  [dependency,values[0]! / 5,values[1]! / 3,values[2]! / 2]

def expectedFlags (old revised : Int) : List Bool :=
  (expectedInputs revised).zipWith (· == ·) (expectedInputs old)

def refusal (mask stage : Nat) : Bool := (mask / 2^stage) % 2 == 1

def expectedError (old revised : Int) (mask : Nat) : Option String :=
  let flags := expectedFlags old revised
  (["pricing","shipping","insurance","permit"].zipIdx).findSome? fun (name,stage) =>
    if refusal mask stage && !flags[stage]! then some (name ++ ".construction") else none

def expectedOutcome (values : List Int) (units : Int) (ledger : List String) :
    Option Int × Option String × List String := Id.run do
  let mut trace := ledger
  let mut total := 0
  for (name,rate) in ["pricing","shipping","insurance","permit"].zip values do
    trace := trace ++ [name ++ ".enter"]
    if units < 0 then return (none,some "units",trace)
    if (name == "shipping" && units > 8) || (name == "permit" && units > 4) then
      return (none,some (name ++ ".limit"),trace)
    trace := trace ++ [name,name ++ ".exit"]
    total := total + units * rate
  return (some total,none,trace)

-- Source synchronous timing: every edge reads the previous complete raw state.
def finiteRates (dependency : Int) : Nat → List Int
  | 0 => [1,1,1,1]
  | depth+1 =>
    let previous := finiteRates dependency depth
    [6+dependency,2+previous[0]!/5,3+previous[1]!/3,1+previous[2]!/2]

-- A different layout tests exact transfer of the whole nested construction.
def reassociate (A : Type) : DictionaryBridge (((A × A) × A) × A) (A × (A × (A × A))) :=
  ⟨(fun raw => (raw.1.1.1,raw.1.1.2,raw.1.2,raw.2)),
    (fun raw => (((raw.1,raw.2.1),raw.2.2.1),raw.2.2.2)),fun _ => rfl,fun _ => rfl⟩

-- Distinct storage, cooked types, fragment types and selected dependency types.
def numbers : Int → Protocol Nat Nat Unit := fun _ => ⟨id,fun _ _ parent => parent.get⟩
def labels : Bool → Protocol String Nat Bool := fun _ => ⟨String.length,fun _ _ parent => parent.get⟩
abbrev heterogeneous : DependencyChain Int :=
  .link numbers [] 7 (fun value => decide (value > 5))
    (.link labels [] "approved" (fun _ => ()) .done)
def heterogeneousBuilders : heterogeneous.Builders String :=
  ((fun _ => .ok ⟨7,rfl⟩),(fun _ => .ok ⟨"approved",rfl⟩),())

def run : IO Unit := do
  let mut revisions := 0
  let mut accepted := 0
  let mut refused := 0
  let mut observations := 0
  let mut finite := 0
  let dependencies : List Int := [0,2,4,14,29,44]
  let unitsCases : List Int := [-1,0,2,5,9]
  let ledgers : List (List String) := [[],["prefix"]]
  for old in dependencies do
    let original ← IO.ofExcept (chain.publish old (builders (fun _ => false)))
    unless rates (assemble original).interface == expectedRates old do throw (IO.userError "initial chain rate oracle")
    for revised in dependencies do
      for mask in List.range 16 do
        revisions := revisions + 1
        match chain.refresh original revised (builders (refusal mask)) with
        | .error error =>
          refused := refused + 1
          unless expectedError old revised mask == some error do throw (IO.userError "first construction refusal")
          unless summary ((checkout (assemble original).interface 2).run ["retained"]) ==
              expectedOutcome (expectedRates old) 2 ["retained"] do throw (IO.userError "refusal changed old chain")
        | .ok refreshed =>
          accepted := accepted + 1
          unless (expectedError old revised mask).isNone && refreshed.reused == expectedFlags old revised do
            throw (IO.userError "stale dependency accepted or unchanged suffix rebuilt")
          let closed := assemble refreshed.publication
          unless rates closed.interface == expectedRates revised do throw (IO.userError "revised chain rate oracle")
          let grouped := (third revised).regroup closed
          let fields := closed.transport (reassociate Account) (reassociate Local)
          for units in unitsCases do
            for ledger in ledgers do
              let expected := expectedOutcome (expectedRates revised) units ledger
              for service in [closed.interface,grouped.interface,(reassociate Local).fromFields fields.interface] do
                observations := observations + 1
                unless summary ((checkout service units).run ledger) == expected do
                  throw (IO.userError "whole chain value/error/full-ledger oracle")
    for depth in List.range 7 do
      let service := (third old).protocol.observe fragments wholeBase wholeBase depth
      unless rates service == finiteRates old depth do throw (IO.userError "chained previous-state rate timing")
      for units in unitsCases do
        for ledger in ledgers do
          finite := finite + 1
          let expected := if depth == 0 then (none,some "missing",ledger)
            else expectedOutcome (finiteRates old (depth-1)) units ledger
          unless summary ((checkout service units).run ledger) == expected do
            throw (IO.userError "chained finite method self timing")
  let hetero ← IO.ofExcept (heterogeneous.publish 0 heterogeneousBuilders)
  let changed ← IO.ofExcept (heterogeneous.refresh hetero 1 heterogeneousBuilders)
  unless changed.reused == [false,true] && changed.publication.2.1.interface == 8 do
    throw (IO.userError "heterogeneous chain selected-view reuse")
  IO.println s!"GENERALIZED-CHAIN-OK revisions={revisions} accepted={accepted} refused={refused} complete-observations={observations} finite-observations={finite} heterogeneous selected-suffix first-refusal old-publication grouping representation"
#eval run

-- Reusing any stale tariff component under a changed edge cannot satisfy its
-- fixed point, regardless of what methods were captured in its old interface.
theorem stale_edge (old revised rate : Int) (rest : List Fragment) (parent : Account)
    (closed : Closed (family old) (.inl rate :: rest) parent) (changed : revised ≠ old) :
    (family revised).step (.inl rate :: rest) closed.raw parent ≠ closed.raw := by
  intro fixed
  have previous := congrArg Account.rate closed.fixed
  have current := congrArg Account.rate fixed
  have rate_step (dependency : Int) (final : Account) :
      ((family dependency).step (.inl rate :: rest) final parent).rate = rate+dependency := by
    rw [TariffComponent.family_step]
    rfl
  rw [rate_step] at previous current
  omega

-- A reused suffix preserves its complete published interfaces, not just the
-- tariff projection that decides the next refresh branch.
theorem reused_suffix {old revised : Int} {original : chain.Publication old}
    (refresh : chain.Refresh original revised)
    (retained : ∀ flag ∈ refresh.2.2.reused, flag = true) :
    (refresh.2.2.publication.1.interface = original.2.2.1.interface) ∧
    (refresh.2.2.publication.2.1.interface = original.2.2.2.1.interface) := by
  have interfaces := refresh.2.2.interfaces_same retained
  exact ⟨interfaces.1,interfaces.2.1⟩

#print axioms assemble
#print axioms stale_edge
#print axioms reused_suffix
#print axioms DependencyChain.Refresh.interfaces_same
#print axioms DependentComponents.closePair_interface
end LeanPoo.Tests.GeneralizedChain
