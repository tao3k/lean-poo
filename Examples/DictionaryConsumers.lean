import LeanPoo.Deriving.DictionaryCompiler
import LeanPoo.Functional.DictionaryTransport

/-! Compose price-policy prototypes, select their typeclass dictionaries through
C3, convert to generated fields and serve proof-aware consumers from that cache. -/
namespace LeanPoo.Examples.DictionaryConsumers
open Functional Requirements Prototype

class Tariff (budget : Nat) where
  rate : Nat
  charge : {units : Nat // units ≤ budget} → Nat
  charge_eq : ∀ units, charge units = rate * units.val
derive_dictionary Tariff

class QuotePolicy (budget : Nat) extends Tariff budget where
  fee : Nat
  feeBound : fee ≤ budget+10
  quote : {units : Nat // units ≤ budget} → Nat
  quote_eq : ∀ units, quote units = toTariff.charge units + fee
derive_dictionary QuotePolicy

@[instance_reducible] def makePolicy (budget rate fee : Nat) (bounded : fee ≤ budget+10) : QuotePolicy budget :=
  { rate, charge := fun units => rate * units.val, charge_eq := fun _ => rfl,
    fee, feeBound := bounded, quote := fun units => rate * units.val + fee, quote_eq := fun _ => rfl }
@[instance_reducible] def base (budget : Nat) := makePolicy budget 2 1 (by omega)

@[instance_reducible] def changeFee (budget : Nat) (change : Nat → Nat) : Proto (QuotePolicy budget) (QuotePolicy budget) (QuotePolicy budget) :=
  fun _ inherited => makePolicy budget inherited.rate (min (change inherited.fee) (budget+10)) (by omega)
@[instance_reducible] def addFee (budget : Nat) := changeFee budget (·+2)
@[instance_reducible] def scaleFee (budget : Nat) := changeFee budget (·*3)
@[instance_reducible] def premium (budget : Nat) : QuotePolicy budget :=
  (compose (scaleFee budget) (addFee budget)) (base budget) (base budget)

/-- The generated representation follows the same child/parent composition,
including method closures, the inherited tariff and dependent fee proofs. -/
theorem productionCommutes (budget : Nat) :
    (QuotePolicy.dictionaryBridge (budget := budget)).toPrototype
      (QuotePolicy.dictionaryBridge (budget := budget)) (QuotePolicy.dictionaryBridge (budget := budget))
      (compose (scaleFee budget) (addFee budget)) =
    compose ((QuotePolicy.dictionaryBridge (budget := budget)).toPrototype
      (QuotePolicy.dictionaryBridge (budget := budget)) (QuotePolicy.dictionaryBridge (budget := budget)) (scaleFee budget))
      ((QuotePolicy.dictionaryBridge (budget := budget)).toPrototype
      (QuotePolicy.dictionaryBridge (budget := budget)) (QuotePolicy.dictionaryBridge (budget := budget)) (addFee budget)) :=
  DictionaryBridge.toPrototype_compose _ _ _ _ _ _

inductive Capability where
  | policy | quota | note | missing
  deriving DecidableEq, Repr
def Value (budget : Nat) : Capability → Type
  | .policy | .missing => QuotePolicy budget
  | .quota => {capacity : Nat // budget+10 ≤ capacity}
  | .note => String
def Fields (budget : Nat) : Capability → Type 1
  | .policy | .missing => QuotePolicy.Fields (budget := budget)
  | .quota => ULift.{1} {capacity : Nat // budget+10 ≤ capacity}
  | .note => ULift.{1} String
def liftBridge (Carrier : Type) : DictionaryBridge Carrier (ULift.{1} Carrier) :=
  ⟨ULift.up, ULift.down, fun _ => rfl, fun value => by cases value; rfl⟩
def bridge : DictionaryTransport.Family Value Fields
  | _, .policy | _, .missing => QuotePolicy.dictionaryBridge
  | c, .quota => liftBridge {capacity : Nat // c+10 ≤ capacity}
  | _, .note => liftBridge String

def graph : C4.Graph := {nodes := [{name := "Checkout", parentOrders := [["Premium", "Standard"]]},
  {name := "Premium"}, {name := "Standard"}]}
def providers (name : String) : Provider Nat Capability Value := fun key =>
  if name == "Premium" then match key with
    | .policy => some premium
    | _ => none
  else if name == "Standard" then match key with
    | .policy => some base
    | .quota => some (fun c => ⟨c+10, by omega⟩)
    | .note => some (fun _ => "internal-stock")
    | .missing => none
  else none

abbrev broad : List Capability := [.policy, .quota, .note]
abbrev billed : List Capability := [.policy, .quota]
abbrev monitored : List Capability := [.quota]
def Joint (c : Nat) (data : Results Value c broad) : Prop := data.1.fee ≤ data.2.1.val
theorem admit (provider : Provider Nat Capability Value) (factories : Factories Nat Value broad)
    (_selected : Selected provider broad factories) (c : Nat) : Joint c (build factories c) :=
  Nat.le_trans (build factories c).1.feeBound (build factories c).2.1.property

theorem billedIncluded : ∀ key ∈ billed, key ∈ broad := by intro key; cases key <;> simp [billed, broad]
theorem monitoredIncluded : ∀ key ∈ monitored, key ∈ broad := by intro key; cases key <;> simp [monitored, broad]
def Billing (c : Nat) (data : Results Value c billed) : Prop := data.1.fee ≤ data.2.1.val
theorem billingProof (c : Nat) (data : Results Value c broad) (valid : Joint c data) :
    Billing c (observeResults (fun _ _ value => value) (projectResults data billed billedIncluded)) := by
  change data.1.fee ≤ data.2.1.val
  exact valid

structure Quote (budget : Nat) where
  amount : Nat
  rate : Nat
  capacity : Nat
  fits : amount ≤ rate * budget + capacity
  label : String

def quote (label : String) (c : Nat) (data : Results Value c billed) (valid : Billing c data) : Quote c :=
  let policy : QuotePolicy c := data.1
  letI : QuotePolicy c := policy
  let units : {n : Nat // n ≤ c} := ⟨c, by omega⟩
  let amount := QuotePolicy.quote units
  ⟨amount, policy.rate, data.2.1.val, by
    change policy.quote units ≤ policy.rate * c + data.2.1.val
    rw [policy.quote_eq, policy.toTariff.charge_eq]
    exact Nat.add_le_add_left valid _, label⟩

def consumers {ready : Certified broad Joint} (label : String) (c : Nat) (data : Snapshot ready c) : Quote c × Nat :=
  (data.consumeView billed billedIncluded (fun _ _ value => value) Billing billingProof (quote label),
   data.consumeView monitored monitoredIncluded (fun _ _ value => value) (fun _ _ => True)
     (fun _ _ _ => True.intro) (fun _ values _ => values.1.val))

/-- Consumers invoking the actual reconstructed typeclass methods agree with
the original dictionary family for every cache state and budget. -/
theorem consumerCommutes (ready : Certified broad Joint) (slot : ContextSlot (DictionaryTransport.certified bridge ready))
    (label : String) (c : Nat) :
    (DictionaryTransport.consumeSnapshot bridge slot (consumers label) c).1 =
      consumers label c ⟨build ready.factories c, rfl, ready.valid c⟩ :=
  DictionaryTransport.consumeSnapshot_value _ _ _ _

structure Receipt where
  budget : Nat
  amount : Nat
  rate : Nat
  available : Nat
  label : String
  hit : Bool
  fee : Nat
  baseFee : Nat
  reversedFee : Nat

def requests {ready : Certified broad Joint} (slot : ContextSlot (DictionaryTransport.certified bridge ready)) :
    List (Nat × String) → List Receipt
  | [] => []
  | (budget, label) :: rest =>
    let ((result, available), next, hit) := DictionaryTransport.consumeSnapshot bridge slot (consumers label) budget
    let fields := (next.read budget).1.val.1
    let reconstructed := QuotePolicy.fromFields fields
    let reverse := (compose (addFee budget) (scaleFee budget)) (base budget) (base budget)
    ⟨budget, result.amount, result.rate, available, result.label, hit, reconstructed.fee,
      (base budget).fee, reverse.fee⟩ :: requests next rest

#eval do
  let .ok order := C4.linearizeVerified graph "Checkout" | throw (IO.userError "dictionary graph")
  let provider := assemble order providers
  let .ok ready := prepareCertified provider broad Joint (admit provider) | throw (IO.userError "dictionary requirements")
  let original := ((ContextSlot.empty ready).read 2).2.1
  let slot := DictionaryTransport.slot bridge original
  let mut previous := some 2
  for (raw, expectedLabel) in (requests slot [(2, "first"), (2, "second"), (6, "third"), (6, "fourth"), (2, "fifth")]).zip
      ["first", "second", "third", "fourth", "fifth"] do
    let result : Receipt := raw
    unless result.hit == (previous == some result.budget) && result.amount == 2*result.budget+9 &&
        result.rate == 2 && result.available == result.budget+10 && result.label == expectedLabel do
      throw (IO.userError "generated dictionary consumer differs from independent price/cache control")
    unless result.fee == 9 && result.baseFee == 1 && result.reversedFee == 5 do
      throw (IO.userError "noncommuting prototypes or retained base changed")
    IO.println s!"{result.label}: quote={result.amount}, available={result.available}, generated-field hit={result.hit}"
    previous := some result.budget
  match prepare (DictionaryTransport.provider bridge provider) [.missing, .policy] with
  | .error .missing => pure ()
  | _ => throw (IO.userError "dictionary conversion changed first missing capability")

end LeanPoo.Examples.DictionaryConsumers
