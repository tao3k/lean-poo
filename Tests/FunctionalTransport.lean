import LeanPoo.Functional.Transport

namespace LeanPoo.Tests.FunctionalTransport
open Functional

universe u v w x y z r
variable {Context : Type u} {Key : Type v}
variable {Old : Context → Key → Type w} {New : Context → Key → Type x}
variable {Public : Context → Key → Type y} {Data : Context → Type z}

/- Connect observation compatibility directly to a data-indexed certificate.
The original evidence can be an arbitrary dependent record, not just Prop. -/
example (expose : ∀ c k, Old c k → Public c k)
    (reveal : ∀ c k, New c k → Public c k)
    (keys : List Key) (left : Requirements.Factories Context Old keys)
    (right : Requirements.Factories Context New keys)
    (compatible : Requirements.Related (fun c k a b => expose c k a = reveal c k b) keys left right)
    (consume : Requirements.Factories Context Public keys → Factory Context Data)
    (Witness : (c : Context) → Data c → Type r)
    (existing : Factory Context (fun c => Witness c (consume (Requirements.observe expose left) c))) :
    Factory Context (fun c => Witness c (consume (Requirements.observe reveal right) c)) :=
  Factory.transport Witness
    (fun c => congrFun (Requirements.observed_consumer_stable expose reveal keys left right compatible consume) c)
    existing

private structure Inputs where
  minimum : Nat
private def original : Factory Inputs (fun _ => Nat) := fun c => c.minimum + 3
private def replacement : Factory Inputs (fun _ => Nat) := fun c => 3 + c.minimum
private def finalData : Factory Inputs (fun _ => Nat) := fun c => (c.minimum + 1) + 2
private theorem same (c : Inputs) : original c = replacement c := by
  simp [original, replacement, Nat.add_comm]
private theorem next (c : Inputs) : replacement c = finalData c := by
  simp [replacement, finalData, Nat.add_comm, Nat.add_assoc]

private structure Certificate (context : Inputs) (data : Nat) where
  amount : Nat
  agrees : amount = data
  bounded : context.minimum ≤ data
private def existing : Factory Inputs (fun c => Certificate c (original c)) :=
  fun c => ⟨original c, rfl, by simp [original]⟩
private def migrated : Factory Inputs (fun c => Certificate c (replacement c)) :=
  Factory.transport Certificate same existing
private def twice : Factory Inputs (fun c => Certificate c (finalData c)) :=
  Factory.transport Certificate next migrated
private def direct : Factory Inputs (fun c => Certificate c (finalData c)) :=
  Factory.transport Certificate (fun c => (same c).trans (next c)) existing

example : twice = direct := Factory.transport_trans Certificate same next existing
example : Factory.transport Certificate (fun c => (same c).symm) migrated = existing :=
  Factory.transport_roundtrip Certificate same existing
example (context : Inputs) : context.minimum ≤ replacement context := (migrated context).bounded
example (context : Inputs) : (migrated context).amount = replacement context := (migrated context).agrees

private def Claim (c : Inputs) (data : Nat) : Prop := c.minimum ≤ data
private theorem known (c : Inputs) : Claim c (original c) := (existing c).bounded
private theorem migratedProof : ∀ c, Claim c (replacement c) :=
  Factory.transportProof Claim same known
private def lifted := Factory.fromProof migratedProof
example (c : Inputs) : Claim c (replacement c) := (lifted c).down

/- The equality premise cannot be omitted for non-definitional replacements,
and evidence at one context is not evidence at a different context. -/
example (_context : Inputs) : True := by
  fail_if_success have _ : Certificate _context (replacement _context) := existing _context
  trivial
example (_old : Certificate ⟨0⟩ (original ⟨0⟩)) : True := by
  fail_if_success have _ : Certificate ⟨8⟩ (replacement ⟨8⟩) := _old
  trivial
example : ¬ (∀ c, original c = replacement c + 1) := by
  intro wrong
  have contradiction := wrong ⟨0⟩
  change (3 : Nat) = 4 at contradiction
  omega

private def check : Bool := [0, 5, 100].all fun n =>
  let context : Inputs := ⟨n⟩
  (migrated context).amount == n + 3 &&
    (twice context).amount == (direct context).amount &&
    ((Factory.transport Certificate (fun c => (same c).symm) migrated) context).amount == (existing context).amount
#guard check

#print axioms Factory.transport_refl
#print axioms Factory.transport_trans
#print axioms Factory.transport_roundtrip
#print axioms Factory.transportProof
#eval IO.println "FUNCTIONAL-TRANSPORT-OK indexed records/claims, observation bridge, composition and roundtrip"
end LeanPoo.Tests.FunctionalTransport
