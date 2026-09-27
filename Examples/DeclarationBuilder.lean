import LeanPoo.Object.Builder
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.DeclarationBuilder

inductive Key where
  | active
  | retries
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Value : Key → Type
  | .active => Bool
  | .retries => Nat

open Object.Declaration.Builder

/-- Lean's dependent key family checks each declaration as it is written. -/
def base : Object.Declaration Key Value := Object.Declaration.build do
  value .active true
  value .retries (2 : Nat)

/-- The same program type can revise a declaration without rebuilding C4. -/
def revised : Object.Declaration Key Value :=
  Object.Declaration.buildOn base do
    value .retries (5 : Nat)

example : revised.default .retries = none := rfl
example : revised.directKeys = [.active, .retries] := rfl

/-- A method can use both delayed inheritance and the final object's self. -/
def layer : Object.Declaration Key Value := Object.Declaration.build do
  slot .retries (.computed fun self inherited =>
    let previous : Nat := (inherited ()).getD (0 : Nat)
    let active : Bool := (self .active).getD false
    some (previous + if active then 1 else 0))

/-- The builder is a notation-free arrangement of the existing operations. -/
example : base =
    ((Object.Declaration.empty : Object.Declaration Key Value)
      |>.withValue .active true |>.withValue .retries (2 : Nat)) := rfl

def result : Except C4.Error (Option Nat) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let extended ← LeanPoo.extend basePlan.schema "Layer" "Base" layer
  return extended.memoize.read .retries

#guard match result with
  | .ok (some 3) => true
  | _ => false

end LeanPoo.Examples.DeclarationBuilder
