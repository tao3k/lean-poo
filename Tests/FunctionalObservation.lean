import LeanPoo.Functional.Observation

namespace LeanPoo.Tests.FunctionalObservation
open Functional

universe u v w x y
variable {Context : Type u} {Key : Type v}
variable {OldValue : Context → Key → Type w} {NewValue : Context → Key → Type x}
variable {PublicValue : Context → Key → Type y}

/- Arbitrary claims over arbitrary observation consumers transfer by equality.
The two original representation families need not have the same type. -/
example (expose : ∀ context key, OldValue context key → PublicValue context key)
    (reveal : ∀ context key, NewValue context key → PublicValue context key)
    (keys : List Key) (left : Requirements.Factories Context OldValue keys)
    (right : Requirements.Factories Context NewValue keys)
    (related : Requirements.Related (fun c k a b => expose c k a = reveal c k b) keys left right)
    (consume : Requirements.Factories Context PublicValue keys → Result)
    (Claim : Result → Prop) (proof : Claim (consume (Requirements.observe expose left))) :
    Claim (consume (Requirements.observe reveal right)) := by
  rw [← Requirements.observed_consumer_stable expose reveal keys left right related consume]
  exact proof

private inductive Capability where
  | field | norm | hidden
  deriving DecidableEq
private structure Inputs where
  minimum : Nat
private structure Packet (context : Inputs) where
  path : Nat
  bound : context.minimum ≤ path
  metadata : Bool
private def Legacy (context : Inputs) : Capability → Type
  | .field => {n : Nat // context.minimum ≤ n}
  | .norm => Nat
  | .hidden => Bool
private def Replacement (context : Inputs) : Capability → Type
  | .field => Packet context
  | .norm => {n : Nat // n ≤ context.minimum + 10}
  | .hidden => Nat
private def Public (context : Inputs) : Capability → Type
  | .field => {n : Nat // context.minimum ≤ n}
  | .norm => Nat
  | .hidden => PUnit
private def expose (context : Inputs) : (key : Capability) → Legacy context key → Public context key
  | .field, value => value
  | .norm, value => value
  | .hidden, _ => PUnit.unit
private def reveal (context : Inputs) : (key : Capability) → Replacement context key → Public context key
  | .field, value => ⟨value.path, value.bound⟩
  | .norm, value => value.val
  | .hidden, _ => PUnit.unit
private def original : Provider Inputs Capability Legacy
  | .field => some (fun c => ⟨c.minimum + 3, by omega⟩)
  | .norm => some (fun c => c.minimum + 4)
  | .hidden => some (fun _ => true)
private def revised : Provider Inputs Capability Replacement
  | .field => some (fun c => ⟨c.minimum + 3, by omega, false⟩)
  | .norm => some (fun c => ⟨c.minimum + 4, by omega⟩)
  | .hidden => none
private abbrev before : List Capability := [.field, .hidden, .norm]
private abbrev after : List Capability := [.norm, .field]
private abbrev needs : List Capability := [.field, .norm, .field]
private theorem includedBefore : ∀ key ∈ needs, key ∈ before := by
  intro key member; cases key <;> simp_all [needs, before]
private theorem includedAfter : ∀ key ∈ needs, key ∈ after := by
  intro key member; cases key <;> simp_all [needs, after]
private theorem compatible : Requirements.RelatedOn original revised needs
    (fun c k a b => expose c k a = reveal c k b) := by
  intro key member left right first second context
  cases key with
  | field =>
    have a := Option.some.inj first
    have b := Option.some.inj second
    rw [← a, ← b]
    rfl
  | norm =>
    have a := Option.some.inj first
    have b := Option.some.inj second
    rw [← a, ← b]
    rfl
  | hidden => simp [needs] at member

private def changed : Provider Inputs Capability Replacement
  | .field => some (fun c => ⟨c.minimum + 4, by omega, false⟩)
  | key => revised key
example : ¬ Requirements.RelatedOn original changed needs
    (fun c k a b => expose c k a = reveal c k b) := by
  intro agreement
  have different := agreement .field (by simp [needs]) _ _ rfl rfl ⟨0⟩
  have unequal := congrArg (fun value : Public ⟨0⟩ .field => value.val) different
  change (3 : Nat) = 4 at unequal
  omega

private def consume (observed : Requirements.Factories Inputs Public needs) : Inputs → Nat :=
  fun c => Nat.add (observed.1 c).val (observed.2.1 c)
private def check : Bool :=
  match Requirements.prepare original before, Requirements.prepare revised after with
  | .ok left, .ok right =>
    let a := Requirements.observe expose (Requirements.project left needs includedBefore)
    let b := Requirements.observe reveal (Requirements.project right needs includedAfter)
    [0, 5, 100].all fun n => consume a ⟨n⟩ == consume b ⟨n⟩ && consume b ⟨n⟩ == 2 * n + 7
  | _, _ => false
#guard check
#guard (Requirements.prepare revised before).toOption.isNone

/- Representation change is not ordinary factory equality. Hidden observations
may change and cannot be inserted into the preserved consumer interface. -/
example (_old : Requirements.Factories Inputs Legacy needs) : True := by
  fail_if_success have _ : Requirements.Factories Inputs Replacement needs := _old
  fail_if_success have _ : Capability.hidden ∈ needs := by simp [needs]
  trivial
example (observed : Requirements.Factories Inputs Public needs) (context : Inputs) :
    context.minimum ≤ (observed.1 context).val := (observed.1 context).property
example (_context : Inputs) (_packet : Packet ⟨0⟩) : True := by
  fail_if_success have _ : _context.minimum ≤ _packet.path := _packet.bound
  trivial

example (left : Requirements.Factories Inputs Legacy before)
    (right : Requirements.Factories Inputs Replacement after)
    (a : Requirements.prepare original before = .ok left)
    (b : Requirements.prepare revised after = .ok right) :
    consume (Requirements.observe expose (Requirements.project left needs includedBefore)) =
      consume (Requirements.observe reveal (Requirements.project right needs includedAfter)) := by
  exact Requirements.observed_consumer_stable expose reveal needs _ _
    (Requirements.project_related original revised _ left right a b needs includedBefore includedAfter compatible) consume

#print axioms Requirements.selected_related
#print axioms Requirements.project_related
#print axioms Requirements.observe_congr
#print axioms Requirements.observed_consumer_stable
#eval IO.println "FUNCTIONAL-OBSERVATION-OK distinct representations, repeated keys, exact public consumers and claims"
end LeanPoo.Tests.FunctionalObservation
