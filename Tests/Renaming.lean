import LeanPoo.Object.Renaming
import LeanPoo.Object.Definition

namespace LeanPoo.Tests.Renaming

inductive Old where
  | number | title | run | limit | missing
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

inductive New where
  | amount | label | call | ceiling | absent
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Value : Old → Type
  | .number | .limit => Nat
  | .title => String
  | .run => Nat → Nat
  | .missing => Unit

abbrev rename : Object.Renaming Old New :=
  { forward := fun
      | .number => .amount | .title => .label | .run => .call
      | .limit => .ceiling | .missing => .absent
    inverse := fun
      | .amount => .number | .label => .title | .call => .run
      | .ceiling => .limit | .absent => .missing
    inverse_forward := by intro key; cases key <;> rfl
    forward_inverse := by intro key; cases key <;> rfl }

private def source : Except C4.Error (Object.Memoized Old Value) := do
  let seed ← Object.define (Key := Old) (Value := Value) "Seed" do
    Object.Declaration.Builder.value .number 1
    Object.Declaration.Builder.default .limit 5
    Object.Declaration.Builder.slot .title (.self fun self =>
      (self .number).map (fun n => s!"value={n}"))
    Object.Declaration.Builder.slot .run (.self fun self =>
      (self .number).map (fun n => fun input => input * n))
  let left ← seed.extendWith "Left" do
    Object.Declaration.Builder.modifyInherited .number (Option.map (· + 10))
  let right ← left.defineWith "Right" ["Seed"] do
    Object.Declaration.Builder.modifyInherited .number (Option.map (· * 2))
  let unused ← right.defineWith "Unused" [] do
    Object.Declaration.Builder.value .number 99
  unused.defineWith "Diamond" ["Left", "Right"] do pure ()

private def checks : Except C4.Error Bool := do
  let original ← source
  let translated := rename.memoized original
  let compiled := rename.memoized original.plan.memoizeCompiled
  let indexed := rename.memoized original.plan.memoizeIndexed
  let future ← compiled.extendWith "Future" do
    Object.Declaration.Builder.value .amount 7
  let unused ← Object.compile translated.plan.schema "Unused"
  let other ← translated.defineNodeWith
    { name := "Reverse", parentOrders := [["Right"], ["Left"]] } do pure ()
  return translated.read .amount == some 12 && compiled.read .amount == some 12 &&
    indexed.read .amount == some 12 && translated.read .label == some "value=12" &&
    (translated.read .call).map (fun f => f 3) == some 36 &&
    translated.read .ceiling == some 5 && translated.read .absent == none &&
    translated.mode == .onDemand && compiled.mode == .compiled && indexed.mode == .indexed &&
    translated.plan.precedence == original.plan.precedence &&
    translated.plan.schema.graph.nodes == original.plan.schema.graph.nodes &&
    future.read .label == some "value=7" && future.read .ceiling == some 5 &&
    (future.read .call).map (fun f => f 3) == some 21 &&
    unused.memoize.read .amount == some 99 && other.read .amount == some 22 &&
    original.read .number == some 12

#guard match checks with | .ok true => true | _ => false

-- Ordered duplicates and delayed overriding survive the translation.
private def overrides : Except C4.Error Bool := do
  let original ← Object.define (Key := Old) (Value := Value) "Danger" do
    Object.Declaration.Builder.slot .number (.thunk fun _ => panic! "forced parent")
  let overridden ← original.extendWith "Safe" do
    Object.Declaration.Builder.value .number 4
    Object.Declaration.Builder.value .number 8
    Object.Declaration.Builder.default .limit 2
    Object.Declaration.Builder.default .limit 9
  let translated := rename.memoized overridden
  return translated.read .amount == some 8 && translated.read .ceiling == some 9

#guard match overrides with | .ok true => true | _ => false

-- Missing declarations are retained throughout the schema, including names
-- outside the current root; no method discovery is performed.
example (schema : Object.Schema Old Value) (name : String)
    (missing : schema.declaration name = none) :
    (rename.schema schema).declaration name = none := by
  simp [Object.Renaming.schema, missing]

example (plan : Object.Plan Old Value) (instanceValue : Object.Instance Old Value plan) :
    (rename.instantiate instanceValue).state .amount = instanceValue.state .number := rfl

#print axioms Object.Renaming.resolve
#print axioms Object.Renaming.instantiate

end LeanPoo.Tests.Renaming
