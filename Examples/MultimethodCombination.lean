import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.MultimethodCombination

abbrev Payload : String → Type := fun _ => Nat

/-- Both dispatch arguments and the non-dispatch quantity are captured before
method selection. Every selected method receives the same typed call record. -/
structure Call where
  left : Object.Plan String Payload
  right : Object.Plan String Payload
  quantity : Nat

def shape : Except C4.Error Call := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let l0 ← LeanPoo.mix empty "L0" [] Object.Declaration.empty
  let l1 ← LeanPoo.extend l0.schema "L1" "L0" Object.Declaration.empty
  let l2 ← LeanPoo.extend l1.schema "L2" "L0" Object.Declaration.empty
  let left ← LeanPoo.mix l2.schema "LF" ["L1", "L2"]
    Object.Declaration.empty
  let r0 ← LeanPoo.mix empty "R0" [] Object.Declaration.empty
  let right ← LeanPoo.extend r0.schema "R1" "R0"
    Object.Declaration.empty
  return ⟨left, right, 3⟩

def precedence (call : Call) : List (List String) :=
  [call.left.precedence, call.right.precedence]

abbrev Trace := StateT (List String) (Except String)

def mark (name : String) : Trace Unit := modify (name :: ·)

def standard : Object.Multimethod Call
    (Object.MethodCombination.Contribution Call Trace Nat) (Trace Nat) :=
  Object.Multimethod.standard 2 precedence
    (fun _ => throw "no primary method")

def standardExercise : Except String
    (Nat × List String × Nat × List String × Nat) := do
  let call ← shape.mapError (fun _ => "invalid C4 graph")
  let g ← (standard.register [.any, .any]
    (.around (fun next _ => do
      mark "around-enter"
      let value ← next ()
      mark "around-exit"
      return value + 1))).mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L0", .prototype "R0"]
    (.primary (fun _ args => do
      mark "primary-base"
      return args.quantity))).mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L1", .prototype "R1"]
    (.primary (fun next _ => do
      mark "primary-specific"
      return (← next ()) + 10))).mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L1", .prototype "R0"]
    (.before (fun _ => mark "before"))).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L0", .prototype "R1"]
    (.after (fun _ => mark "after"))).mapError
    (fun _ => "invalid method arity")
  let g ← (g.registerWhen [.prototype "L1", .prototype "R1"]
    (fun args => args.quantity == 4)
    (.before (fun _ => mark "guarded-before"))).mapError
    (fun _ => "invalid method arity")
  let (first, cached) ← (g.call call).mapError
    (fun _ => "invalid call arity")
  let (firstValue, firstTrace) ← first.run []
  let (second, reused) ← (cached.call { call with quantity := 4 })
    |>.mapError (fun _ => "invalid call arity")
  let (secondValue, secondTrace) ← second.run []
  return (firstValue, firstTrace.reverse, secondValue,
    secondTrace.reverse, reused.cache.size)

#guard match standardExercise with
  | .ok (14, first, 15, second, 1) =>
    first == ["around-enter", "before", "primary-specific",
      "primary-base", "after", "around-exit"] &&
    second == ["around-enter", "guarded-before", "before",
      "primary-specific", "primary-base", "after", "around-exit"]
  | _ => false

def sumPolicy : Object.MethodCombination.SimplePolicy Nat Nat Nat :=
  { stop := fun _ => false
    empty := 0
    first := id
    step := Nat.add
    finish := id }

def simple : Object.Multimethod Call
    (Object.MethodCombination.SimpleContribution Call (Except String) Nat Nat)
    (Except String Nat) :=
  Object.Multimethod.simple 2 precedence sumPolicy

def simpleExercise : Except String (Nat × Nat) := do
  let call ← shape.mapError (fun _ => "invalid C4 graph")
  let g ← (simple.register [.prototype "L0", .prototype "R0"]
    (.item (fun _ => .ok 2))).mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L1", .prototype "R1"]
    (.item (fun args => .ok args.quantity))).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.any, .any]
    (.around (fun next _ => do return (← next ()) + 100)))
    |>.mapError (fun _ => "invalid method arity")
  let (result, cached) ← (g.call call).mapError
    (fun _ => "invalid call arity")
  return (← result, cached.cache.size)

#guard match simpleExercise with
  | .ok (105, 1) => true
  | _ => false

end LeanPoo.Examples.MultimethodCombination
