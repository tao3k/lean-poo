import LeanPoo.Prototype.GeneralizedComponents
import LeanPoo.Deriving.DictionaryCompiler

/-! Future-work client: separately closed billing/shipping protocols mounted
in one C3 service. Assembly grouping does not reorder public ledger effects. -/
namespace LeanPoo.Examples.ComponentCheckout
open Prototype Prototype.Generalized Functional Object.MethodCombination
abbrev Action := EStateM String (List String)
abbrev Methods := Object.MethodCombination.Methods Int Action Int
structure Account where
  rate : Int
  methods : Methods := {}
structure Local where
  rate : Int
  price : Int → Action Int
abbrev Method := Thunk Int → Contribution Int Action Int
abbrev Fragment := Sum Int Method

def rateFocus : MonoLens Account Int := MonoLens.ofGetSet (·.rate) (fun value raw => {raw with rate := value})
def methodsFocus : MonoLens Account Methods := MonoLens.ofGetSet (·.methods) (fun value raw => {raw with methods := value})
def narrow : Protocol Account Int Fragment :=
  ⟨Account.rate,sumCompiler (lensCompiler rateFocus (fun rate _ _ => rate)) (standardCompiler methodsFocus)⟩
def localCook (raw : Account) : Local := ⟨raw.rate,effective raw.methods (fun _ => throw "missing")⟩
def localProtocol : Protocol Account Local Fragment := narrow.reindexSelf (·.rate) localCook

theorem local_step (fragments : List Fragment) : localProtocol.step fragments = narrow.step fragments :=
  narrow.step_reindexSelf Local.rate localCook (fun _ => rfl) fragments

theorem rate_stable (rate : Int) (rest : List Fragment) (base : Account) :
    localProtocol.approximate (.inl rate :: rest) base base 3 =
      localProtocol.approximate (.inl rate :: rest) base base 2 := by
  simp only [Protocol.approximate, local_step]
  exact narrow.stable_two _ base base rate (fun _ => rfl)

def closeLocal (fragments : List Fragment) (base : Account) : Except String (Closed localProtocol fragments base) :=
  match fragments with
  | .inl rate :: rest => .ok (localProtocol.closeAt (.inl rate :: rest) base base 2 (rate_stable rate rest base))
  | _ => .error "leading rate witness required"

structure Storage where
  accounts : Account × Account
  tenant : String
structure Interface where
  billing : Local
  shipping : Local
  checkout : Int → Action Int

derive_dictionary Storage
derive_dictionary Interface

def accountsFocus : Focus Storage (Account × Account) :=
  ⟨Storage.accounts,(fun value raw => {raw with accounts := value}),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
def firstFocus : Focus (Account × Account) Account :=
  ⟨Prod.fst,(fun value raw => (value,raw.2)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
def secondFocus : Focus (Account × Account) Account :=
  ⟨Prod.snd,(fun value raw => (raw.1,value)),fun _ _ => rfl,fun _ => rfl,fun _ _ _ => rfl⟩
def billingFocus := accountsFocus.compose firstFocus
def shippingFocus := accountsFocus.compose secondFocus

def components : Components localProtocol localProtocol Storage Interface where
  leftFocus := billingFocus
  rightFocus := shippingFocus
  independent := ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => rfl⟩
  leftView := Interface.billing
  rightView := Interface.shipping
  cook := fun raw =>
    let billing := localCook raw.accounts.1
    let shipping := localCook raw.accounts.2
    ⟨billing,shipping,fun units => do
      let billed ← billing.price units
      let shipped ← shipping.price units
      return billed + shipped⟩
  leftCompatible := fun _ => rfl
  rightCompatible := fun _ => rfl

def mark (event : String) : Action Unit := modify (· ++ [event])
def method (body : Method) : Fragment := .inr body
def graph : Prototype.C3.Graph :=
  [("Checkout",["Billing","Shipping"]),("Billing",["Base"]),("Shipping",["Base"]),("Base",[])]
def declarations (billingRate shippingRate fee capacity : Int) (name : String) : List (Sum Fragment Fragment) :=
  if name == "Checkout" then [.inl (.inl billingRate),.inr (.inl shippingRate)]
  else if name == "Billing" then [
    .inl (method (fun _ => .around (fun next units => do
      mark "bill.enter"; if units < 0 then throw "units" else
        let result ← next (); mark "bill.exit"; return result))),
    .inl (method (fun _ => .before (fun _ => mark "bill.before"))),
    .inl (method (fun _ => .primary (fun next _ => do mark "fee"; return (← next ()) + fee))),
    .inl (method (fun _ => .primary (fun next _ => do mark "markup"; return 2 * (← next ())))),
    .inl (method (fun _ => .after (fun _ => mark "bill.after")))]
  else if name == "Shipping" then [
    .inr (method (fun _ => .around (fun next units => do
      mark "ship.enter"; if units > capacity then throw "capacity" else
        let result ← next (); mark "ship.exit"; return result))),
    .inr (method (fun _ => .before (fun _ => mark "ship.before"))),
    .inr (method (fun _ => .after (fun _ => mark "ship.after")))]
  else if name == "Base" then [
    .inl (method (fun self => .primary (fun _ units => do mark "bill.base"; return units * self.get))),
    .inr (method (fun self => .primary (fun _ units => do mark "ship.base"; return units * self.get)))]
  else []

def base : Storage := ⟨(⟨1,{}⟩,⟨1,{}⟩),"tenant-A"⟩
def close (fragments : List (Sum Fragment Fragment)) : Except String (Closed components.protocol fragments base) := do
  let billing ← closeLocal (leftFragments fragments) base.accounts.1
  let shipping ← closeLocal (rightFragments fragments) base.accounts.2
  return components.close fragments base billing shipping

def summary : EStateM.Result String (List String) Int → Option Int × Option String × List String
  | .ok value state => (some value,none,state)
  | .error error state => (none,some error,state)

theorem retained_billing {old : List (Sum Fragment Fragment)}
    (closed : Closed components.protocol old base) (revised : List (Sum Fragment Fragment))
    (sameLeft : leftFragments revised = leftFragments old)
    (rightClosed : Closed localProtocol (rightFragments revised) (components.rightFocus.get base))
    (units : Int) (ledger : List String) :
    (((components.replaceRight closed revised sameLeft rightClosed).interface.billing.price units).run ledger) =
      ((closed.interface.billing.price units).run ledger) :=
  congrArg (fun viewed : Local => (viewed.price units).run ledger)
    (components.replaceRight_left closed revised sameLeft rightClosed)


def run : IO Unit := do
  let plan ← IO.ofExcept ((components.protocol.prepare graph (declarations 5 3 2 4) "Checkout").mapError reprStr)
  let closed ← IO.ofExcept (close plan.fragments)
  let service := closed.interface
  unless (summary ((service.checkout 4).run [])).1 == some 54 do throw (IO.userError "mounted pricing")
  unless summary ((service.checkout 5).run ["prefix"]) ==
      (none,some "capacity",["prefix","bill.enter","bill.before","fee","markup","bill.base","bill.after","bill.exit","ship.enter"]) do
    throw (IO.userError "failed shipping lost billing prefix")
  let regrouped := components.regroup closed
  unless summary ((regrouped.interface.checkout 4).run []) == summary ((service.checkout 4).run []) do
    throw (IO.userError "grouped component assembly")
  let fields := closed.transport Storage.dictionaryBridge Interface.dictionaryBridge
  let restored := Interface.fromFields fields.interface
  unless summary ((restored.checkout 4).run []) == summary ((service.checkout 4).run []) do
    throw (IO.userError "mounted closed representation transfer")
  -- Reuse the original billing witness when replacing only shipping construction.
  let revised ← IO.ofExcept (closeLocal (.inl 1 :: (rightFragments plan.fragments).tail) (components.rightFocus.get base))
  let changedFragments := (leftFragments plan.fragments).map Sum.inl ++
    ((.inl 1 :: (rightFragments plan.fragments).tail).map Sum.inr)
  let changed := components.replaceRight closed changedFragments
    (by simp only [changedFragments,leftFragments_append,leftFragments_map_left,leftFragments_map_right,List.append_nil])
    (by simpa only [changedFragments,rightFragments_append,rightFragments_map_left,rightFragments_map_right,List.nil_append] using revised)
  unless (summary ((changed.interface.checkout 4).run [])).1 == some 46 &&
      (summary ((service.checkout 4).run [])).1 == some 54 do throw (IO.userError "component revision retention")
  unless closed.raw.tenant == "tenant-A" do throw (IO.userError "mount changed tenant")
  IO.println "COMPONENT-CHECKOUT-OK joined-closure=54 revised=46 retained-prefix independent-grouping raw/public-transfer"
#eval run
#print axioms retained_billing
#print axioms Components.assemble_partition
#print axioms Components.approximate_left
#print axioms Components.close_left
#print axioms Components.projectRight
end LeanPoo.Examples.ComponentCheckout
