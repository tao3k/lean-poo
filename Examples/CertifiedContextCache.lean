import LeanPoo.Functional.ContextPullback

/-! A certified allocation family shares dependency data across request labels.
Changing the full base budget replaces the one-context cache. -/
namespace LeanPoo.Examples.CertifiedContextCache
open Functional Requirements

inductive Capability where
  | allocation | capacity
  deriving Repr

def Value (budget : Nat) : Capability → Type
  | .allocation => {amount : Nat // budget ≤ amount}
  | .capacity => Nat

def allocation : Factory Nat (fun budget => Value budget .allocation) :=
  fun budget => ⟨budget + 2, by omega⟩
def capacity : Factory Nat (fun budget => Value budget .capacity) := fun budget => budget + 4

def provider : Provider Nat Capability Value
  | .allocation => some allocation
  | .capacity => some capacity

abbrev requested : List Capability := [.allocation, .capacity]
def Fits (_budget : Nat) (data : Results Value _budget requested) : Prop := data.1.val ≤ data.2.1

theorem admit (factories : Factories Nat Value requested) (selected : Selected provider requested factories) :
    ∀ budget, Fits budget (build factories budget) := by
  rcases factories with ⟨first, second, tail⟩
  have firstEq : first = allocation := by simpa [provider] using selected.1.symm
  have secondEq : second = capacity := by simpa [provider] using selected.2.1.symm
  subst first
  subst second
  intro budget
  simp [Fits, build, allocation, capacity]

structure Request where
  budget : Nat
  label : String

structure Plan (request : Request) where
  reserved : Nat
  covers : request.budget ≤ reserved
  capacity : Nat
  fits : reserved ≤ capacity
  label : String

def construct (request : Request) (data : Results Value request.budget requested)
    (valid : Fits request.budget data) : Plan request :=
  ⟨data.1.val, data.1.property, data.2.1, valid, request.label⟩

def scenario : Except Capability (List (Nat × String × Bool)) := do
  let ready ← prepareCertified provider requested Fits admit
  let mut slot := ContextSlot.empty ready
  let mut outputs := []
  for request in [Request.mk 3 "first", ⟨3, "second"⟩, ⟨8, "third"⟩,
      ⟨8, "fourth"⟩, ⟨3, "fifth"⟩] do
    let (plan, next, hit) := slot.consumeAlong Request.budget construct request
    slot := next
    outputs := outputs ++ [(plan.reserved, plan.label, hit)]
  return outputs

#guard scenario.toOption == some [
  (5, "first", false), (5, "second", true), (10, "third", false),
  (10, "fourth", true), (5, "fifth", false)]
#eval IO.println s!"certified allocations (reserved, current label, dependency hit): {repr scenario.toOption}"

end LeanPoo.Examples.CertifiedContextCache
