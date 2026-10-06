import LeanPoo.Functional.View

namespace LeanPoo.Tests.FunctionalView
open Functional

universe u v w x
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}

/- The preservation contract covers arbitrary consumers and arbitrary claims;
it does not enumerate fixture consumers or reprove their internal theorems. -/
example [DecidableEq Key] (provider other : Provider Context Key Value)
    (left : Requirements.Factories Context Value leftKeys)
    (right : Requirements.Factories Context Value rightKeys)
    (leftReady : Requirements.prepare provider leftKeys = .ok left)
    (rightReady : Requirements.prepare other rightKeys = .ok right)
    (keys : List Key) (a : ∀ key ∈ keys, key ∈ leftKeys)
    (b : ∀ key ∈ keys, key ∈ rightKeys)
    (same : ∀ key ∈ keys, other key = provider key)
    (consume : Requirements.Factories Context Value keys → Result)
    (Claim : Result → Prop) (proof : Claim (consume (Requirements.project left keys a))) :
    Claim (consume (Requirements.project right keys b)) := by
  rw [← Requirements.consumer_stable provider other left right leftReady rightReady keys a b same consume]
  exact proof

private inductive Capability where
  | background | derivative | residual | budget
  deriving DecidableEq
private structure Inputs where
  minimum : Nat
private def SampleValue (c : Inputs) : Capability → Type
  | .background => Nat
  | .derivative => Bool
  | .residual => {n : Nat // c.minimum ≤ n}
  | .budget => Nat
private def original : Provider Inputs Capability SampleValue
  | .background => some (fun c => c.minimum + 1)
  | .derivative => some (fun _ => true)
  | .residual => some (fun c => ⟨c.minimum + 3, by omega⟩)
  | .budget => some (fun _ => (100 : Nat))
private def revised : Provider Inputs Capability SampleValue
  | .derivative => none
  | .budget => some (fun _ => (200 : Nat))
  | key => original key
private abbrev oldKeys : List Capability := [.background, .derivative, .residual, .budget]
private abbrev newKeys : List Capability := [.budget, .residual, .background]
private abbrev needs : List Capability := [.background, .residual]
private def consume (view : Requirements.Factories Inputs SampleValue needs) : Inputs → Nat :=
  fun context => Nat.add (view.1 context) (view.2.1 context).val

private theorem includedOld : ∀ key ∈ needs, key ∈ oldKeys := by
  intro key member; simp only [needs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [oldKeys]
private theorem includedNew : ∀ key ∈ needs, key ∈ newKeys := by
  intro key member; simp only [needs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [newKeys]
private theorem unchanged : ∀ key ∈ needs, revised key = original key := by
  intro key member; simp only [needs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/- Deleting an unrelated capability prevents global preparation. Independent
local preparation still succeeds; projection requires an available source. -/
#guard (Requirements.prepare revised oldKeys).toOption.isNone
#guard (Requirements.prepare revised needs).toOption.isSome

private def check : Bool :=
  match Requirements.prepare original oldKeys, Requirements.prepare revised newKeys with
  | .ok left, .ok right =>
    let a := Requirements.project left needs includedOld
    let b := Requirements.project right needs includedNew
    [0, 5, 100].all fun n => consume a ⟨n⟩ == consume b ⟨n⟩ && consume b ⟨n⟩ == 2 * n + 4
  | _, _ => false
#guard check

example (left : Requirements.Factories Inputs SampleValue oldKeys)
    (right : Requirements.Factories Inputs SampleValue newKeys)
    (a : Requirements.prepare original oldKeys = .ok left)
    (b : Requirements.prepare revised newKeys = .ok right) :
    consume (Requirements.project left needs includedOld) =
      consume (Requirements.project right needs includedNew) :=
  Requirements.consumer_stable original revised left right a b needs includedOld includedNew unchanged consume

/- All contexts retain their original dependent witness. Missing keys cannot
be smuggled into the narrow consumer interface by positional access. -/
example (view : Requirements.Factories Inputs SampleValue needs) (context : Inputs) :
    context.minimum ≤ (view.2.1 context).val := (view.2.1 context).property
example (_view : Requirements.Factories Inputs SampleValue needs) : True := by
  fail_if_success have _ : Capability.derivative ∈ needs := by simp [needs]
  trivial

#print axioms Requirements.project_selected
#print axioms Requirements.project_ready
#print axioms Requirements.project_stable
#print axioms Requirements.consumer_stable
#eval IO.println "FUNCTIONAL-VIEW-OK provider edit/deletion, narrow preparation, consumer/proof transport"
end LeanPoo.Tests.FunctionalView
