import LeanPoo.Prototype.GeneralizedChain
import LeanPoo.Prototype.GeneralizedTariff

/-! Future-work client: pricing → shipping → insurance → settlement permit.
The four closures are joined through nested existing dependent components.
Construction refusal and public method refusal have distinct observable traces. -/
namespace LeanPoo.Examples.ChainedCheckout
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

/-- A reused leaf retains every action outcome, including error and ledger, even
when all three earlier components have new closure evidence. -/
theorem retained_permit {old revised : Int} {original : chain.Publication old}
    (refresh : chain.Refresh original revised) (retained : refresh.2.2.2.1.reused = true)
    (units : Int) (ledger : List String) :
    (((assemble refresh.publication).interface.2.price units).run ledger) =
      ((original.2.2.2.1.interface.price units).run ledger) := by
  rw [assemble_interface]
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger)
    (refresh.2.2.2.1.interface_same retained)

def run : IO Unit := do
  let original ← IO.ofExcept (chain.publish 0 (builders (fun _ => false)))
  for (dependency,expectedFlags,expectedRates) in [
      (0,[true,true,true,true],[6,3,4,3]),
      (2,[false,true,true,true],[8,3,4,3]),
      (4,[false,false,true,true],[10,4,4,3]),
      (14,[false,false,false,true],[20,6,5,3]),
      (29,[false,false,false,false],[35,9,6,4])] do
    let refreshed ← IO.ofExcept (chain.refresh original dependency (builders (fun _ => false)))
    unless refreshed.reused == expectedFlags && rates (assemble refreshed.publication).interface == expectedRates do
      throw (IO.userError "chain dependency/reuse boundary")
  let stopped ← IO.ofExcept (chain.refresh original 4 (builders (fun stage => stage ≥ 2)))
  unless stopped.reused == [false,false,true,true] do throw (IO.userError "unchanged suffix called refusing builders")
  unless (chain.refresh original 29 (builders (fun stage => stage == 2))).toOption.isNone &&
      (summary ((checkout (assemble original).interface 2).run [])).1 == some 32 do
    throw (IO.userError "partial construction escaped or old publication changed")
  IO.println "CHAINED-CHECKOUT-OK four-level-closure selected-view-invalidation stops-at-unchanged-suffix construction-refusal"
#eval run
#print axioms assemble
#print axioms assemble_interface
#print axioms retained_permit
#print axioms DependencyChain.refresh_head_error
#print axioms DependencyChain.refresh_tail_error
end LeanPoo.Examples.ChainedCheckout
