import LeanPoo.Prototype.GeneralizedDependencies
import LeanPoo.Deriving.DictionaryCompiler

/-! Future-work client: fulfillment construction depends on the selected public
pricing tier. Equal tiers retain closure; changed tiers need fresh evidence. -/
namespace LeanPoo.Tests.GeneralizedDependencies
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
def narrow (dependency : Int) : Protocol Account Int Fragment :=
  ⟨Account.rate,sumCompiler (lensCompiler rateFocus (fun rate _ _ => rate+dependency)) (standardCompiler methodsFocus)⟩
def localCook (raw : Account) : Local := ⟨raw.rate,effective raw.methods (fun _ => throw "missing")⟩
def family (dependency : Int) : Protocol Account Local Fragment := (narrow dependency).reindexSelf Local.rate localCook
abbrev upstreamProtocol := family 0

theorem family_step (dependency : Int) (fragments : List Fragment) :
    (family dependency).step fragments = (narrow dependency).step fragments :=
  (narrow dependency).step_reindexSelf Local.rate localCook (fun _ => rfl) fragments

theorem rate_stable (dependency rate : Int) (rest : List Fragment) (base : Account) :
    (family dependency).approximate (.inl rate :: rest) base base 3 =
      (family dependency).approximate (.inl rate :: rest) base base 2 := by
  simp only [Protocol.approximate,family_step]
  exact (narrow dependency).stable_two _ base base (rate+dependency) (fun _ => rfl)

def closeLocal (dependency : Int) (fragments : List Fragment) (base : Account) :
    Except String (Closed (family dependency) fragments base) :=
  match fragments with
  | .inl rate :: rest => .ok ((family dependency).closeAt (.inl rate :: rest) base base 2 (rate_stable dependency rate rest base))
  | _ => .error "leading rate witness required"

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

def mark (event : String) : Action Unit := modify (· ++ [event])
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

def summary : EStateM.Result String (List String) Int → Option Int × Option String × List String
  | .ok value state => (some value,none,state)
  | .error error state => (none,some error,state)

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

def control (rate flat fee capacity units : Int) (depth : Nat := 3) : Option Int × Option String × List String :=
  let priced := ["prefix","price.enter","fee","subtotal","price.after","price.exit"]
  if depth == 0 then (none,some "missing",["prefix"])
  else if units < 0 then (none,some "units",["prefix","price.enter"])
  else if units > capacity then (none,some "capacity",priced ++ ["ship.enter"])
  else
    let pricedRate := if depth == 1 then 1 else rate
    let shippingRate := if depth == 1 then 1 else if depth == 2 then flat else flat + rate / 5
    (some (units*(pricedRate+shippingRate)+fee),none,priced ++ ["ship.enter","shipping","ship.after","ship.exit"])

def run : IO Unit := do
  let mut cases := 0
  let mut revisions := 0
  for rate in [4,6,8,11] do
    for flat in [1,3] do
      for fee in [0,2] do
        for capacity in [0,4] do
          let plan ← IO.ofExcept ((components.protocol.prepare graph (declarations rate flat fee capacity) "Checkout").mapError reprStr)
          let original ← IO.ofExcept (publish plan.fragments)
          let closed := original.closed
          let grouped := components.regroup closed
          let raw := closed.transport Storage.dictionaryBridge (DictionaryBridge.identity Interface)
          let both := closed.transport Storage.dictionaryBridge Interface.dictionaryBridge
          for units in [-1,0,2,5] do
            let expected := control rate flat fee capacity units
            for service in [closed.interface,grouped.interface,raw.interface,Interface.fromFields both.interface] do
              let actual := summary ((service.checkout units).run ["prefix"])
              unless actual == expected do throw (IO.userError s!"dependent closed control {rate}/{flat}/{fee}/{capacity}/{units}: {repr actual} != {repr expected}")
            for depth in [0,1,2,3] do
              unless summary ((((plan.observe base base depth).checkout units).run ["prefix"])) ==
                  control rate flat fee capacity units depth do throw (IO.userError s!"dependency approximation offset depth={depth}")
            for delta in [1,5] do
              for refuse in [false,true] do
                let revisedRate := rate + delta
                let same := revisedRate / 5 == rate / 5
                let shouldRefuse := !same && refuse && revisedRate / 5 ≥ 2
                match revise original revisedRate refuse with
                | .error error =>
                  unless shouldRefuse && error == "tier construction refused" do throw (IO.userError "unexpected construction refusal")
                | .ok revised =>
                  unless !shouldRefuse && revised.reused == same do throw (IO.userError "dependent reuse marker")
                  unless summary ((revised.published.closed.interface.checkout units).run ["prefix"]) ==
                      control revisedRate flat fee capacity units do throw (IO.userError "revised dependency price/trace")
                  if same then
                    unless summary ((revised.published.closed.interface.shipping.price units).run ["prefix"]) ==
                        summary ((original.shipping.interface.price units).run ["prefix"]) do throw (IO.userError "same-tier shipping changed")
                  unless revised.published.closed.raw.tenant == "tenant-A" do throw (IO.userError "revision frame")
                unless summary ((closed.interface.checkout units).run ["prefix"]) == expected do throw (IO.userError "old publication changed")
                revisions := revisions + 1
            unless closed.raw.accounts.1.rate == rate && closed.raw.accounts.2.rate == flat + rate/5 &&
                closed.raw.tenant == "tenant-A" && closed.raw.accounts.1.methods.primary.length == 2 &&
                closed.raw.accounts.2.methods.primary.length == 1 do throw (IO.userError "dependent raw/C3/frame control")
            cases := cases + 1
  unless cases == 128 && revisions == 512 do throw (IO.userError "inventory")
  IO.println s!"GENERALIZED-DEPENDENCIES-OK cases={cases} closed-observations={cases*4} finite-observations={cases*4} revisions={revisions} tiers/refusal/prefixes/grouping/representations"
#eval run

theorem family_rate_step (dependency rate : Int) (rest : List Fragment) (final parent : Account) :
    ((family dependency).step (.inl rate :: rest) final parent).rate = rate + dependency := by
  rw [family_step]
  rfl

-- A changed tier invalidates the old raw fixed-point equation, even if its
-- fragment order and previously returned public values are retained.
theorem stale_not_fixed (old revised rate : Int) (rest : List Fragment) (parent : Account)
    (closed : Closed (family old) (.inl rate :: rest) parent) (changed : revised ≠ old) :
    (family revised).step (.inl rate :: rest) closed.raw parent ≠ closed.raw := by
  intro fixed
  have previous := congrArg Account.rate closed.fixed
  have current := congrArg Account.rate fixed
  rw [family_rate_step] at previous current
  omega

#print axioms publication_reuses_shipping
#print axioms stale_not_fixed
#print axioms DependentComponents.downstream_succ
#print axioms DependentComponents.advance_downstream
#print axioms DependentComponents.approximate_upstream
#print axioms DependentComponents.close_downstream
#print axioms DependencyRefresh.interface_same
#print axioms Closed.refreshDependency_reuses
#print axioms Closed.refreshDependency_error
end LeanPoo.Tests.GeneralizedDependencies
