import LeanPoo.Object.Lens
import LeanPoo.Object.Builder

namespace LeanPoo.Examples.NestedPrototype

abbrev InnerValue (_ : String) := Nat
abbrev Inner := Object.Memoized String InnerValue

def innerBase : Object.Declaration String InnerValue :=
  Object.Declaration.build do
    Object.Declaration.Builder.value "limit" 2

def innerInitial : Except C4.Error Inner := do
  let empty : Object.Schema String InnerValue :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let plan ← LeanPoo.mix empty "Base" [] innerBase
  return plan.memoize

inductive OuterKey where
  | service
  | enabled
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable, Repr

def OuterValue : OuterKey → Type
  | .service => Inner
  | .enabled => Bool

abbrev Outer := Object.Memoized OuterKey OuterValue

def outerInitial : Except C4.Error Outer := do
  let inner ← innerInitial
  let declaration : Object.Declaration OuterKey OuterValue :=
    Object.Declaration.build do
      Object.Declaration.Builder.value .service inner
      Object.Declaration.Builder.value .enabled true
  let empty : Object.Schema OuterKey OuterValue :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let plan ← LeanPoo.mix empty "Outer" [] declaration
  return plan.memoize

inductive NestedError where
  | outer (error : Object.SlotLensError OuterKey)
  | inner (error : Object.SlotLensError String)
  | c4 (error : C4.Error)
  deriving Repr

def service : Object.Lens Outer Inner NestedError :=
  (Object.Lens.slot (Key := OuterKey) (Value := OuterValue) .service)
    |>.mapError .outer

def limit : Object.Lens Inner Nat NestedError :=
  (Object.Lens.slot (Key := String) (Value := InnerValue) "limit")
    |>.mapError .inner

/-- Both instance targets are reconstructed from their revised specifications. -/
def nestedLimit : Object.Lens Outer Nat NestedError :=
  service.compose limit

def changedValue : Except NestedError (Option Nat × Option Nat × Bool) := do
  let original ← outerInitial.mapError .c4
  let updated ← nestedLimit.modify (· + 1) original
  let oldInner ← service.get original
  let newInner ← service.get updated
  return (oldInner.read "limit", newInner.read "limit",
    original.plan.precedence == updated.plan.precedence)

#guard match changedValue with
  | .ok (some 2, some 3, true) => true
  | _ => false

def boost : Object.Declaration String InnerValue :=
  Object.Declaration.build do
    Object.Declaration.Builder.slot "limit"
      (.computed fun _ inherited => some ((inherited ()).getD 0 + 10))

/-- Inner inheritance changes while the outer C4 topology remains fixed. -/
def extendedInner : Except NestedError (Option Nat × Option Nat × Bool × Bool) := do
  let original ← outerInitial.mapError .c4
  let updated ← service.modifyM
    (fun inner => (inner.extend "Boost" boost).mapError .c4) original
  let oldInner ← service.get original
  let newInner ← service.get updated
  return (oldInner.read "limit", newInner.read "limit",
    original.plan.precedence == updated.plan.precedence,
    oldInner.plan.precedence != newInner.plan.precedence)

#guard match extendedInner with
  | .ok (some 2, some 12, true, true) => true
  | _ => false

/- A failed inner extension does not produce an updated outer object. -/
#guard match outerInitial with
  | .error _ => false
  | .ok original =>
      match service.modifyM
        (fun inner => (inner.extend "Base" boost).mapError .c4) original with
      | .error (.c4 (.duplicateNode "Base")) =>
          match original.read .service with
          | some inner => inner.read "limit" == some 2
          | none => false
      | _ => false

end LeanPoo.Examples.NestedPrototype
