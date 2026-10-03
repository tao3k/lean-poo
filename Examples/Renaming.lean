import LeanPoo.Object.Renaming
import LeanPoo.Object.Definition

namespace LeanPoo.Examples.Renaming

inductive Before where
  | x | double
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

inductive After where
  | amount | twice
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev rename : Object.Renaming Before After :=
  { forward := fun | .x => .amount | .double => .twice
    inverse := fun | .amount => .x | .twice => .double
    inverse_forward := by intro key; cases key <;> rfl
    forward_inverse := by intro key; cases key <;> rfl }

abbrev Value (_ : Before) := Nat

private def scenario : Except C4.Error (Nat × Nat × Nat) := do
  let original ← Object.define (Key := Before) (Value := Value) "Counter" do
    Object.Declaration.Builder.value .x 3
    Object.Declaration.Builder.slot .double (.self fun self =>
      (self .x).map (· * 2))
  let translated := rename.memoized original.plan.memoizeCompiled
  let extended ← translated.extendWith "Seven" do
    Object.Declaration.Builder.value .amount 7
  return ((original.read .double).getD 0, (translated.read .twice).getD 0,
    (extended.read .twice).getD 0)

#guard match scenario with | .ok result => result == (6, 6, 14) | .error _ => false
#eval match scenario with
  | .ok (before, after, future) =>
      s!"old double={before}; renamed twice={after}; extended final-self twice={future}"
  | .error error => s!"error: {repr error}"

end LeanPoo.Examples.Renaming
