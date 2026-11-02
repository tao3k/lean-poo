import LeanPoo.Prototype.GeneralizedComponents
import LeanPoo.Deriving.DictionaryCompiler

/-! Future-work client: separately closed billing/shipping protocols mounted
in one C3 service. Assembly grouping does not reorder public ledger effects. -/
namespace LeanPoo.Tests.GeneralizedComponents
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

def control (billingRate shippingRate fee capacity units : Int) : Option Int × Option String × List String :=
  let billed := ["prefix","bill.enter","bill.before","fee","markup","bill.base","bill.after","bill.exit"]
  if units < 0 then (none,some "units",["prefix","bill.enter"])
  else if units > capacity then (none,some "capacity",billed ++ ["ship.enter"])
  else (some (units*(2*billingRate+shippingRate)+fee),none,
    billed ++ ["ship.enter","ship.before","ship.base","ship.after","ship.exit"])

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
  let mut cases := 0
  for billingRate in [2,5] do
    for shippingRate in [1,3] do
      for fee in [0,2] do
        for capacity in [0,3,6] do
          let plan ← IO.ofExcept ((components.protocol.prepare graph
            (declarations billingRate shippingRate fee capacity) "Checkout").mapError reprStr)
          let closed ← IO.ofExcept (close plan.fragments)
          let grouped := components.regroup closed
          let raw := closed.transport Storage.dictionaryBridge (DictionaryBridge.identity Interface)
          let both := closed.transport Storage.dictionaryBridge Interface.dictionaryBridge
          let projected := components.projectLeft closed
          let revisedFragments := (leftFragments plan.fragments).map Sum.inl ++
            ((.inl (shippingRate+1) :: (rightFragments plan.fragments).tail).map Sum.inr)
          let revisedLocal ← IO.ofExcept (closeLocal
            (.inl (shippingRate+1) :: (rightFragments plan.fragments).tail) (components.rightFocus.get base))
          let revised := components.replaceRight closed revisedFragments
            (by simp only [revisedFragments,leftFragments_append,leftFragments_map_left,leftFragments_map_right,List.append_nil])
            (by simpa only [revisedFragments,rightFragments_append,rightFragments_map_left,rightFragments_map_right,List.nil_append] using revisedLocal)
          for units in [-1,0,2,4,7] do
            let expected := control billingRate shippingRate fee capacity units
            for service in [closed.interface,grouped.interface,raw.interface,Interface.fromFields both.interface] do
              let actual := summary ((service.checkout units).run ["prefix"])
              unless actual == expected do throw (IO.userError s!"component control {billingRate}/{shippingRate}/{fee}/{capacity}/{units}: {repr actual} != {repr expected}")
            unless summary ((revised.interface.checkout units).run ["prefix"]) ==
                control billingRate (shippingRate+1) fee capacity units do throw (IO.userError "revision control")
            unless summary ((projected.interface.price units).run ["prefix"]) ==
                summary ((revised.interface.billing.price units).run ["prefix"]) do throw (IO.userError "left witness changed")
            unless closed.raw.tenant == "tenant-A" && revised.raw.tenant == "tenant-A" &&
                closed.raw.accounts.1.methods.primary.length == 3 && closed.raw.accounts.2.methods.primary.length == 1 do
              throw (IO.userError "outside frame or shared base duplication")
            cases := cases + 1
  unless cases == 120 do throw (IO.userError "inventory")
  -- Grouping components is allowed; reversing one component's methods is not.
  let plan ← IO.ofExcept ((components.protocol.prepare graph (declarations 5 3 2 6) "Checkout").mapError reprStr)
  match leftFragments plan.fragments with
  | .inl rate :: rest =>
    let changed ← IO.ofExcept (close ((.inl rate :: rest.reverse).map Sum.inl ++
      (rightFragments plan.fragments).map Sum.inr))
    unless (summary ((changed.interface.checkout 4).run [])).1 == some 32 do
      throw (IO.userError "local-order discriminator")
  | _ => throw (IO.userError "leading rate")
  unless (closeLocal [] base.accounts.1).toOption.isNone do throw (IO.userError "missing closure premise")
  IO.println s!"GENERALIZED-COMPONENTS-OK cases={cases} executions={cases*4} revisions={cases} exact-result/error/ledger grouping representations witness-reuse order-discriminator"
#eval run
#print axioms retained_billing

-- The grouping theorem must not admit overlapping focuses.
example : ¬ Focus.Independent firstFocus firstFocus := by
  intro independent
  have impossible := congrArg Account.rate (independent.left_read (⟨1,{}⟩ : Account) (⟨0,{}⟩,⟨0,{}⟩))
  change (1 : Int) = 0 at impossible
  omega

#print axioms Protocol.assemble_mount
#print axioms Components.assemble_equiv
#print axioms Components.assemble_grouped
#print axioms Components.close
#print axioms Components.replaceRight_left
#print axioms Components.approximate_left
#print axioms Components.approximate_right
#print axioms Components.frame
end LeanPoo.Tests.GeneralizedComponents
