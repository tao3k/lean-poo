import LeanPoo.Functional.RequestHandling
import LeanPoo.Functional.ContractJoin

/-! Join independent price/stock certificates, admit order inputs before reading
their cache, and check actual producer outputs before publishing receipts. -/
namespace LeanPoo.Examples.ValidatedOrders
open Functional Requirements

abbrev Value (_ _ : Nat) := Nat
abbrev keys : List Nat := [0,1,2]
def factories : Factories Nat Value keys := (fun c => c+2, fun c => c+8, fun c => c+90, PUnit.unit)
def Price (c : Nat) (values : Results Value c keys) : Prop := values.1 = c+2
def Stock (c : Nat) (values : Results Value c keys) : Prop := values.2.1 = c+8
def priced : Certified keys Price := ⟨factories, fun _ => rfl⟩
def stocked : Certified keys Stock := ⟨factories, fun _ => rfl⟩
def ready := priced.conjoin stocked rfl

-- Context/quantity, request label and an intentionally defective producer flag.
abbrev Wire := (Nat × Nat) × (String × Bool)
abbrev Input := {wire : Wire // 0 < wire.1.2 ∧ wire.1.2 ≤ 16 ∧ wire.2.1 ≠ ""}
def schema : Codec Input Wire String :=
  (((Codec.identity Nat String).product (Codec.identity Nat String)).product
    ((Codec.identity String String).product (Codec.identity Bool String))).refine
      (fun wire => 0 < wire.1.2 ∧ wire.1.2 ≤ 16 ∧ wire.2.1 ≠ "") "invalid order"
def context (input : Input) := input.val.1.1

structure Receipt where
  context : Nat
  amount : Nat
  stock : Nat
  rate : Nat
  priced : rate = context+2
  stocked : stock = context+8
  fits : amount ≤ rate * stock
  label : String

def outputSchema (input : Input) (rate : Nat) :
    Codec {reply : Nat × String // reply.1 = rate * input.val.1.2 ∧ reply.2 = input.val.2.1}
      (Nat × String) String :=
  ((Codec.identity Nat String).product (Codec.identity String String)).refine
    (fun reply => reply.1 = rate * input.val.1.2 ∧ reply.2 = input.val.2.1) "invalid producer output"

def serve (input : Input) (data : Snapshot ready (context input)) : Except String Receipt :=
  let quantity := input.val.1.2
  let rate := data.val.1
  let stock := data.val.2.1
  if fits : quantity ≤ stock then
    let producer : Factory Input (fun _ => Nat × String) := Factory.choose
      (fun request => request.val.2.2)
      (fun request => (rate * request.val.1.2 + 1, request.val.2.1))
      (fun request => (rate * request.val.1.2, request.val.2.1))
    ((outputSchema input rate).decode (producer input)).map fun reply =>
      ⟨context input, reply.val.1, stock, rate, data.property.2.1, data.property.2.2,
        by rw [reply.property.1]; exact Nat.mul_le_mul_left rate fits, reply.val.2⟩
  else .error "insufficient stock"

def warm : ContextSlot ready := (((ContextSlot.empty priced).read 2).2.1).conjoin stocked rfl

theorem inputRefusal (slot : ContextSlot ready) (wire : Wire) (error : String)
    (refused : schema.decode wire = .error error) :
    slot.call schema context serve wire = ⟨.error error, slot, none⟩ :=
  slot.call_input_error _ _ _ _ _ refused

theorem cachedOutcome (slot : ContextSlot ready) (wire : Wire) :
    (slot.call schema context serve wire).outcome =
      match schema.decode wire with
      | .error error => .error error
      | .ok input => serve input ⟨build ready.factories (context input), rfl, ready.valid (context input)⟩ :=
  by
    cases admitted : schema.decode wire <;>
      simpa only [admitted] using slot.call_outcome schema context serve wire

def describe : Except String Receipt → String
  | .error error => error
  | .ok receipt => s!"{receipt.label}:{receipt.amount}/{receipt.stock}@{receipt.rate}"

#eval do
  let requests : List (Wire × String × Option Bool) :=
    [(((2,3),("first",false)), "first:12/10@4", some true),
     (((2,3),("second",false)), "second:12/10@4", some true),
     (((5,0),("input-refusal",true)), "invalid order", none),
     (((5,14),("stock-refusal",false)), "insufficient stock", some false),
     (((5,2),("output-refusal",true)), "invalid producer output", some true),
     (((5,2),("resumed",false)), "resumed:14/13@7", some true),
     (((2,2),("return",false)), "return:8/10@4", some false)]
  let mut slot := warm
  for entry in requests do
    let (wire, expected, hit) : Wire × String × Option Bool := entry
    let result := slot.call schema context serve wire
    unless describe result.outcome == expected && result.reused == hit do
      throw (IO.userError "admitted order changed independent price/error/cache control")
    IO.println s!"{describe result.outcome}; dependencyRead={result.reused}"
    slot := result.next
  unless (warm.read 2).2.2 && (slot.read 2).2.2 do
    throw (IO.userError "persistent original cache or final request cache changed")

end LeanPoo.Examples.ValidatedOrders
