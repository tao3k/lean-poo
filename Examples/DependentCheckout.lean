import LeanPoo.Prototype.GeneralizedTariff
import LeanPoo.Deriving.DictionaryCompiler

/-! Future-work client: fulfillment construction depends on the selected public
pricing tier. Equal tiers retain closure; changed tiers need fresh evidence. -/
namespace LeanPoo.Examples.DependentCheckout
open Prototype Prototype.Generalized Functional Object.MethodCombination
export Prototype.Generalized.TariffComponent (Action Methods Account Local Method Fragment
  rateFocus methodsFocus narrow localCook family upstreamProtocol family_step rate_stable closeLocal mark summary)

structure Storage where
  accounts : Account × Account
  tenant : String
structure Interface where
  pricing : Local
  shipping : Local
  checkout : Int → Action Int

derive_dictionary Storage
derive_dictionary Interface

def firstFocus : Focus Storage Account :=
  ⟨(fun raw => raw.accounts.1),(fun value raw => {raw with accounts := (value,raw.accounts.2)}),
    fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
def secondFocus : Focus Storage Account :=
  ⟨(fun raw => raw.accounts.2),(fun value raw => {raw with accounts := (raw.accounts.1,value)}),
    fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
def tier (pricing : Local) : Int := pricing.rate / 5

def components : DependentComponents upstreamProtocol family Storage Interface where
  upstreamFocus := firstFocus
  downstreamFocus := secondFocus
  independent := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
  select := tier
  upstreamView := Interface.pricing
  downstreamView := Interface.shipping
  cook := fun raw =>
    let pricing := localCook raw.accounts.1
    let shipping := localCook raw.accounts.2
    ⟨pricing,shipping,fun units => do
      let subtotal ← pricing.price units
      let delivery ← shipping.price units
      return subtotal + delivery⟩
  upstreamCompatible := fun _ => rfl
  downstreamCompatible := fun _ => rfl

def method (body : Method) : Fragment := .inr body
def graph : Prototype.C3.Graph :=
  [("Checkout",["Pricing","Shipping"]),("Pricing",["Base"]),("Shipping",["Base"]),("Base",[])]
def declarations (rate flat fee capacity : Int) (name : String) : List (Sum Fragment Fragment) :=
  if name == "Checkout" then [.inl (.inl rate),.inr (.inl flat)]
  else if name == "Pricing" then [
    .inl (method (fun _ => .around (fun next units => do mark "price.enter"; if units < 0 then throw "units" else
      let result ← next (); mark "price.exit"; return result))),
    .inl (method (fun _ => .primary (fun next _ => do mark "fee"; return (← next ()) + fee))),
    .inl (method (fun _ => .after (fun _ => mark "price.after")))]
  else if name == "Shipping" then [
    .inr (method (fun _ => .around (fun next units => do mark "ship.enter"; if units > capacity then throw "capacity" else
      let result ← next (); mark "ship.exit"; return result))),
    .inr (method (fun _ => .after (fun _ => mark "ship.after")))]
  else if name == "Base" then [
    .inl (method (fun self => .primary (fun _ units => do mark "subtotal"; return units * self.get))),
    .inr (method (fun self => .primary (fun _ units => do mark "shipping"; return units * self.get)))]
  else []

def base : Storage := ⟨(⟨1,{}⟩,⟨1,{}⟩),"tenant-A"⟩
structure Published (fragments : List (Sum Fragment Fragment)) where
  pricing : Closed upstreamProtocol (leftFragments fragments) (components.upstreamFocus.get base)
  shipping : Closed (family (tier pricing.interface)) (rightFragments fragments) (components.downstreamFocus.get base)

def Published.closed {fragments} (published : Published fragments) : Closed components.protocol fragments base :=
  components.close fragments base published.pricing published.shipping

def publish (fragments : List (Sum Fragment Fragment)) : Except String (Published fragments) := do
  let pricing ← closeLocal 0 (leftFragments fragments) (components.upstreamFocus.get base)
  let shipping ← closeLocal (tier pricing.interface) (rightFragments fragments) (components.downstreamFocus.get base)
  return ⟨pricing,shipping⟩

structure Revision where
  fragments : List (Sum Fragment Fragment)
  published : Published fragments
  reused : Bool

def revise {fragments} (old : Published fragments) (rate : Int) (refuse : Bool := false) : Except String Revision := do
  let revised := ((.inl rate :: (leftFragments fragments).tail).map Sum.inl) ++ (rightFragments fragments).map Sum.inr
  let pricing ← closeLocal 0 (leftFragments revised) (components.upstreamFocus.get base)
  let retained := old.shipping.reindexFragments (rightFragments revised)
    (by simp only [revised,rightFragments_append,rightFragments_map_left,rightFragments_map_right,List.nil_append])
  let refreshed ← retained.refreshDependency (tier pricing.interface) (fun dependency =>
    if refuse && dependency ≥ 2 then .error "tier construction refused"
    else closeLocal dependency (rightFragments revised) (components.downstreamFocus.get base))
  return ⟨revised,⟨pricing,refreshed.closed⟩,refreshed.reused⟩


theorem retained_shipping {old : Int} {fragments : List Fragment} {parent : Account}
    {original : Closed (family old) fragments parent} {revised : Int}
    (refresh : DependencyRefresh original revised) (reused : refresh.reused = true) (units : Int) (ledger : List String) :
    ((refresh.closed.interface.price units).run ledger) = ((original.interface.price units).run ledger) :=
  congrArg (fun viewed : Local => (viewed.price units).run ledger) (refresh.interface_same reused)

theorem publication_reuses_shipping {fragments : List (Sum Fragment Fragment)}
    (pricing : Closed upstreamProtocol (leftFragments fragments) (components.upstreamFocus.get base))
    (oldDependency : Int)
    (shipping : Closed (family oldDependency) (rightFragments fragments) (components.downstreamFocus.get base))
    (same : tier pricing.interface = oldDependency) (units : Int) (ledger : List String) :
    (((components.close fragments base pricing (shipping.reuseDependency _ same)).interface.shipping.price units).run ledger) =
      ((shipping.interface.price units).run ledger) := by
  have exposed := components.close_downstream fragments base pricing (shipping.reuseDependency _ same)
  have retained := shipping.reuseDependency_interface _ same
  exact congrArg (fun viewed : Local => (viewed.price units).run ledger) (exposed.trans retained)

def run : IO Unit := do
  let plan ← IO.ofExcept ((components.protocol.prepare graph (declarations 6 2 0 4) "Checkout").mapError reprStr)
  let published ← IO.ofExcept (publish plan.fragments)
  unless (summary ((published.closed.interface.checkout 3).run [])).1 == some 27 do throw (IO.userError "dependent initial price")
  let reused ← IO.ofExcept (revise published 8 true)
  unless reused.reused && (summary ((reused.published.closed.interface.checkout 3).run [])).1 == some 33 do
    throw (IO.userError "unchanged dependency should retain shipping")
  let rebuilt ← IO.ofExcept (revise published 11)
  unless !rebuilt.reused && (summary ((rebuilt.published.closed.interface.checkout 3).run [])).1 == some 45 do
    throw (IO.userError "changed dependency reused stale shipping")
  let bypassed ← IO.ofExcept (revise rebuilt.published 12 true)
  unless bypassed.reused && (summary ((bypassed.published.closed.interface.checkout 3).run [])).1 == some 48 do
    throw (IO.userError "same tier did not bypass a refusing rebuilder")
  unless (revise published 11 true).toOption.isNone &&
      (summary ((published.closed.interface.checkout 3).run [])).1 == some 27 do throw (IO.userError "refusal changed old publication")
  unless summary ((rebuilt.published.closed.interface.checkout 5).run ["prefix"]) ==
      (none,some "capacity",["prefix","price.enter","fee","subtotal","price.after","price.exit","ship.enter"]) do
    throw (IO.userError "dependent shipping refusal lost pricing prefix")
  let grouped := components.regroup rebuilt.published.closed
  unless summary ((grouped.interface.checkout 3).run []) == summary ((rebuilt.published.closed.interface.checkout 3).run []) do
    throw (IO.userError "dependent grouping changed result")
  let fields := rebuilt.published.closed.transport Storage.dictionaryBridge Interface.dictionaryBridge
  unless summary (((Interface.fromFields fields.interface).checkout 3).run []) ==
      summary ((rebuilt.published.closed.interface.checkout 3).run []) do throw (IO.userError "dependent representation transfer")
  IO.println "DEPENDENT-CHECKOUT-OK original=27 same-tier=33 changed-tier=45 refusing-builder-bypassed=48 refused-publication retained-errors exact-dependency raw/public-transfer"
#eval run
#print axioms publication_reuses_shipping
#print axioms retained_shipping
#print axioms DependentComponents.step_partition
#print axioms DependentComponents.close
#print axioms Closed.refreshDependency_same
end LeanPoo.Examples.DependentCheckout
