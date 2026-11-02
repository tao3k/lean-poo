import LeanPoo.Prototype.GeneralizedInheritance
import LeanPoo.Object.SimplePolicies

/-! Research example: independently extensible validation and cost policies
share cooked final self. Existing all/sum policies own execution and stopping. -/
namespace LeanPoo.Examples.GeneralizedCheckout
open Prototype Prototype.Generalized Object.MethodCombination
abbrev Action := EStateM String (List String)
abbrev Costs := SimpleMethods Int Action Int Int
abbrev Checks := SimpleMethods Int Action Bool Bool
structure Storage where
  rate : Int
  groups : Costs × Checks := ({},{})
  tenant : String := "A"
structure Interface where
  rate : Int
  offer : Int → Action Int
abbrev Cost := Thunk Interface → SimpleContribution Int Action Int Int
abbrev Check := Thunk Interface → SimpleContribution Int Action Bool Bool
abbrev Fragment := Sum Int (Sum Cost Check)
def rateFocus : MonoLens Storage Int := MonoLens.ofGetSet (·.rate) (fun value raw => {raw with rate := value})
def groupsFocus : MonoLens Storage (Costs × Checks) := MonoLens.ofGetSet (·.groups) (fun value raw => {raw with groups := value})
def costFocus : MonoLens (Costs × Checks) Costs := MonoLens.ofGetSet Prod.fst (fun value raw => (value,raw.2))
def checkFocus : MonoLens (Costs × Checks) Checks := MonoLens.ofGetSet Prod.snd (fun value raw => (raw.1,value))
def protocol : Protocol Storage Interface Fragment where
  cook := fun raw => ⟨raw.rate,fun units => do
    let accepted ← simpleEffective SimplePolicy.all raw.groups.2 units
    if !accepted then throw "refused"
    simpleEffective (SimplePolicy.sum Int) raw.groups.1 units⟩
  compile := sumCompiler (lensCompiler rateFocus (fun rate _ _ => rate))
    (sumCompiler (simpleCompiler (groupsFocus.compose costFocus)) (simpleCompiler (groupsFocus.compose checkFocus)))
def mark (event : String) : Action Unit := modify (· ++ [event])
def cost (fragment : Cost) : Fragment := .inr (.inl fragment)
def check (fragment : Check) : Fragment := .inr (.inr fragment)
def graph : Prototype.C3.Graph :=
  [("Checkout",["Local","Shipping"]),("Local",["Base"]),("Shipping",["Base"]),("Base",[])]
def declarations (name : String) : List Fragment :=
  if name == "Checkout" then [.inl 5,
    check (fun _ => .item (fun units => do mark "range"; return units ≥ 0 && units ≤ 6)),
    cost (fun _ => .around (fun next _ => do mark "cost.enter"; let result ← next (); mark "cost.exit"; return result))]
  else if name == "Local" then [
    check (fun _ => .item (fun units => do mark "stock"; return units != 3)),
    cost (fun _ => .item (fun _ => do mark "handling"; return 2))]
  else if name == "Shipping" then [
    cost (fun _ => .item (fun _ => do mark "shipping"; return 4))]
  else if name == "Base" then [.inl 1,
    check (fun _ => .item (fun _ => do mark "base.check"; return true)),
    cost (fun self => .item (fun units => do mark "merchandise"; return units * self.get.rate))]
  else []
def base : Storage := ⟨1,({},{}),"tenant-A"⟩
def summary : EStateM.Result String (List String) Int → Option Int × Option String × List String
  | .ok value state => (some value,none,state)
  | .error error state => (none,some error,state)
def run : IO Unit := do
  let plan ← IO.ofExcept ((protocol.prepare graph declarations "Checkout").mapError reprStr)
  let service := plan.observe base base 2
  unless summary ((service.offer 4).run []) ==
      (some 26,none,["range","stock","base.check","cost.enter","handling","shipping","merchandise","cost.exit"]) do
    throw (IO.userError "independent policies or diamond duplication")
  unless summary ((service.offer 3).run ["prefix"]) == (none,some "refused",["prefix","range","stock"]) do
    throw (IO.userError "all did not short-circuit before costs")
  unless summary ((service.offer 7).run []) == (none,some "refused",["range"]) do
    throw (IO.userError "range did not short-circuit stock")
  let raw := protocol.approximate plan.fragments base base 2
  unless raw.tenant == "tenant-A" && raw.groups.1.items.length == 3 && raw.groups.2.items.length == 3 do
    throw (IO.userError "unrelated focus changed or shared base repeated")
  IO.println "GENERALIZED-CHECKOUT-OK shared-C3 all/sum groups final-self=26 short-circuit retained-prefix nested-frames"
#eval run
#print axioms Protocol.approximate_transport
#print axioms Protocol.approximate_frame
end LeanPoo.Examples.GeneralizedCheckout
