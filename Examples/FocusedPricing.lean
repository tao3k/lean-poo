import LeanPoo.Functional.FocusedUpdate
import LeanPoo.Functional.Codec
import LeanPoo.Functional.StatefulValidation

namespace LeanPoo.Examples.FocusedPricing
open Functional Prototype

structure Context where
  rate : Nat
  handling : Nat
  ceiling : Nat

structure Policy where
  quote : Nat → Nat
  stock : Nat

structure Shop where
  pricing : Policy
  owner : String

def policy : Focus Shop Policy where
  get := Shop.pricing
  set value shop := { shop with pricing := value }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def method : Focus Policy (Nat → Nat) where
  get := Policy.quote
  set value pricing := { pricing with quote := value }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

def quote : Focus Shop (Nat → Nat) := policy.compose method

def inventory : Focus Shop Nat where
  get shop := shop.pricing.stock
  set value shop := { shop with pricing := { shop.pricing with stock := value } }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

theorem separate : Focus.Independent quote inventory := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

def base (stock : Nat) : Factory Context (fun _ => Shop) :=
  fun context => ⟨⟨fun quantity => quantity * context.rate, stock⟩, "shop-A"⟩

def addHandling (context : Context) (old : Nat → Nat) : Nat → Nat :=
  fun quantity => old quantity + context.handling
def scale (factor : Nat) (_ : Context) (old : Nat → Nat) : Nat → Nat :=
  fun quantity => old quantity * factor

def priced (stock factor : Nat) : Factory Context (fun _ => Shop) :=
  Factory.focus (fun _ => quote) (scale factor)
    (Factory.focus (fun _ => quote) addHandling (base stock))

theorem price_formula (stock factor : Nat) (context : Context) (quantity : Nat) :
    (priced stock factor context).pricing.quote quantity =
      (quantity * context.rate + context.handling) * factor := rfl

/-- The actual delayed prototype chain produces exactly the factory-built shop. -/
theorem delayed_factory (stock factor : Nat) (context : Context) :
    DelayedProto.compose (quote.prototype (scale factor)) (quote.prototype addHandling)
      (Thunk.pure context) (Thunk.pure (base stock context)) = priced stock factor context := rfl

theorem price_frame (stock factor : Nat) (context : Context) :
    (priced stock factor context).owner = "shop-A" ∧
      (priced stock factor context).pricing.stock = stock := ⟨rfl, rfl⟩

abbrev Wire := Bool × Nat
def input : Codec (Bool × {amount : Nat // 0 < amount ∧ amount ≤ 5}) Wire String :=
  (Codec.identity Bool String).product
    ((Codec.identity Nat String).refine (fun amount => 0 < amount ∧ amount ≤ 5) "amount")

/-- Check every supported quantity, including zero and the stock endpoint. -/
def Within (stock ceiling : Nat) (price : Nat → Nat) : Prop :=
  (List.range (stock + 1)).all (fun quantity => decide (price quantity ≤ ceiling)) = true
instance (stock ceiling : Nat) : DecidablePred (Within stock ceiling) :=
  fun price => inferInstanceAs (Decidable ((List.range (stock + 1)).all
    (fun quantity => decide (price quantity ≤ ceiling)) = true))

def output (stock ceiling : Nat) : Codec {price : Nat → Nat // Within stock ceiling price} (Nat → Nat) String :=
  (Codec.identity (Nat → Nat) String).refine (Within stock ceiling) "ceiling"

structure Certificate where
  price : Nat → Nat
  stock : Nat
  ceiling : Nat
  admitted : Within stock ceiling price

theorem Certificate.bound (certificate : Certificate) (quantity : Nat) (available : quantity ≤ certificate.stock) :
    certificate.price quantity ≤ certificate.ceiling := by
  have member := List.mem_range.mpr (Nat.lt_succ_of_le available)
  have checked := List.all_eq_true.mp certificate.admitted quantity member
  exact of_decide_eq_true checked

def admit (context : Context) (shop : Shop)
    (command : Bool × {amount : Nat // 0 < amount ∧ amount ≤ 5}) (old : Nat → Nat) : Except String Certificate :=
  let fragment := Factory.choose (fun _ : Context => command.1)
    (fun context old quantity => old quantity + context.handling * command.2.val)
    (fun _ old quantity => old quantity * command.2.val)
  ((output shop.pricing.stock context.ceiling).decode (fragment context old)).map
    (fun approved => ⟨approved.val, shop.pricing.stock, context.ceiling, approved.property⟩)

theorem admit_contract (context : Context) (shop : Shop)
    (command : Bool × {amount : Nat // 0 < amount ∧ amount ≤ 5}) (old : Nat → Nat)
    (certificate : Certificate) (accepted : admit context shop command old = .ok certificate) :
    certificate.stock = shop.pricing.stock ∧ certificate.ceiling = context.ceiling := by
  unfold admit Except.map at accepted
  dsimp only at accepted
  split at accepted <;> first | contradiction | (cases accepted; exact ⟨rfl, rfl⟩)

def step (context : Context) (shop : Shop) (wire : Wire) : Except String Certificate × Shop :=
  match input.decode wire with
  | .error error => (.error error, shop)
  | .ok command => quote.checkedWith Certificate.price (admit context shop command) shop

def batch (context : Context) (shop : Shop) (commands : List Wire) :=
  Validation.traverseState (step context) shop commands

theorem refused_input (context : Context) (shop : Shop) (wire : Wire) (error : String)
    (refused : input.decode wire = .error error) : step context shop wire = (.error error, shop) := by
  simp [step, refused]

theorem step_frame (context : Context) (shop : Shop) (wire : Wire) :
    (step context shop wire).2.owner = shop.owner ∧
      (step context shop wire).2.pricing.stock = shop.pricing.stock := by
  unfold step
  cases input.decode wire with
  | error error => exact ⟨rfl, rfl⟩
  | ok command =>
    exact ⟨Focus.checkedWith_frame _ _ _ Shop.owner (fun _ _ => rfl) shop,
      Focus.checkedWith_frame _ _ _ (fun value => value.pricing.stock) (fun _ _ => rfl) shop⟩

theorem step_installed (context : Context) (shop next : Shop) (wire : Wire) (certificate : Certificate)
    (success : step context shop wire = (.ok certificate, next)) :
    next.pricing.quote = certificate.price := by
  unfold step at success
  cases decoded : input.decode wire with
  | error error => simp [decoded] at success
  | ok command =>
    simp only [decoded] at success
    have installed := Focus.checkedWith_installed quote Certificate.price (admit context shop command)
      shop certificate (congrArg Prod.fst success)
    rw [success] at installed
    exact installed

theorem step_bound (context : Context) (shop next : Shop) (wire : Wire) (certificate : Certificate)
    (success : step context shop wire = (.ok certificate, next))
    (quantity : Nat) (available : quantity ≤ next.pricing.stock) :
    next.pricing.quote quantity ≤ context.ceiling := by
  have frame := (step_frame context shop wire).2
  rw [success] at frame
  change next.pricing.stock = shop.pricing.stock at frame
  have contract : certificate.stock = shop.pricing.stock ∧ certificate.ceiling = context.ceiling := by
    unfold step at success
    cases decoded : input.decode wire with
    | error error => simp [decoded] at success
    | ok command =>
      simp only [decoded] at success
      have accepted := congrArg Prod.fst success
      rw [Focus.checkedWith_outcome] at accepted
      exact admit_contract context shop command _ certificate accepted
  rw [step_installed context shop next wire certificate success]
  rw [← contract.2]
  exact certificate.bound quantity (by rw [contract.1, ← frame]; exact available)

theorem batch_first_error (context : Context) (shop final : Shop) (commands : List Wire) (error : String) :
    batch context shop commands = (.error error, final) ↔
      ∃ before command after certificates next, commands = before ++ command :: after ∧
        batch context shop before = (.ok certificates, next) ∧
        step context next command = (.error error, final) := Validation.traverseState_error_iff _ _ _ _ _

#eval do
  let context : Context := ⟨2, 3, 30⟩
  let original := base 4 context
  let (result, retained) := batch context original [(true, 1), (false, 2), (true, 5), (false, 3)]
  unless result matches .error "ceiling" do throw (IO.userError "expected price ceiling refusal")
  unless retained.pricing.quote 0 == 6 && retained.pricing.quote 4 == 22 &&
      retained.pricing.stock == 4 && retained.owner == "shop-A" do
    throw (IO.userError "nested failure lost successful price updates or outside fields")
  let (resumed, next) := batch context retained [(true, 1)]
  unless resumed.toOption.isSome && next.pricing.quote 4 == 25 && original.pricing.quote 4 == 8 do
    throw (IO.userError "continued pricing or original snapshot differs")
  let reverse := quote.modify (addHandling context) (quote.modify (scale 2 context) original)
  unless (priced 4 2 context).pricing.quote 4 == 22 && reverse.pricing.quote 4 == 19 do
    throw (IO.userError "noncommuting wrappers lost order")
  IO.println "FOCUSED-PRICING-OK refused=ceiling retained=22 resumed=25 reversed=19"

#print axioms Certificate.bound
#print axioms delayed_factory
#print axioms step_frame
#print axioms step_installed
#print axioms step_bound
#print axioms admit_contract
#print axioms batch_first_error
end LeanPoo.Examples.FocusedPricing
