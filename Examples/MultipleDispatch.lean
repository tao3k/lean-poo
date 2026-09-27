import LeanPoo.Object.Multimethod
import LeanPoo.Object.MethodCombination
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.MultipleDispatch

abbrev Payload : String → Type := fun _ => Nat

structure Call where
  left : Object.Plan String Payload
  right : Object.Plan String Payload
  quantity : Nat

abbrev Method := Object.MethodCombination.SubMethod
  Call (Except String) (List String)

def baseMethod : Method :=
  fun next _ => do
    return "L0/R0" :: (← next ())

def universalMethod : Method :=
  fun _ _ => .ok ["any/any"]

def layer (name : String) : Method :=
  fun next _ => do
    return name :: (← next ())

/-- The generic owns its combination policy and the tuple-indexed methods.
Each argument supplies the C4 order of its own prototype graph. -/
def generic : Object.Multimethod Call Method (Except String (List String)) :=
  { arity := 2
    precedence := fun call => [call.left.precedence, call.right.precedence]
    combine := fun methods call =>
      Object.MethodCombination.callChain methods.toList
        (fun _ => .error "no applicable method") call }

def callShape : Except C4.Error Call := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let l0 ← LeanPoo.mix empty "L0" [] Object.Declaration.empty
  let l1 ← LeanPoo.extend l0.schema "L1" "L0" Object.Declaration.empty
  let l2 ← LeanPoo.extend l1.schema "L2" "L0" Object.Declaration.empty
  let left ← LeanPoo.mix l2.schema "LF" ["L1", "L2"]
    Object.Declaration.empty
  let r0 ← LeanPoo.mix empty "R0" [] Object.Declaration.empty
  let r1 ← LeanPoo.extend r0.schema "R1" "R0" Object.Declaration.empty
  return ⟨left, r1, 1⟩

/-- Lexicographic tuple order follows a C4 diamond on the left argument.
Reusing the same shape hits the effective-method cache; registering a new
method creates a fresh generic with an empty cache. -/
def exercise : Except String
    (List String × Nat × Nat × List String × Nat × List String) := do
  let call ← callShape.mapError (fun _ => "invalid C4 graph")
  let g ← (generic.register [.any, .any] universalMethod).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.any, .prototype "R1"]
    (layer "any/R1")).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L0", .prototype "R0"] baseMethod).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L1", .prototype "R0"]
    (layer "L1/R0")).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L0", .prototype "R1"]
    (layer "L0/R1")).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L1", .prototype "R1"]
    (layer "L1/R1")).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "L2", .prototype "R0"]
    (layer "L2/R0")).mapError
    (fun _ => "invalid method arity")
  let g ← (g.registerWhen [.prototype "L1", .prototype "R1"]
    (fun call => call.quantity == 42) (layer "quantity=42")).mapError
    (fun _ => "invalid method arity")
  let (first, cached) ← (g.call call).mapError (fun _ => "invalid call arity")
  let labels ← first
  let (again, reused) ← (cached.call call).mapError
    (fun _ => "invalid call arity")
  let _ ← again
  let (exact, exactCached) ← (reused.call { call with quantity := 42 })
    |>.mapError (fun _ => "invalid call arity")
  let exactLabels ← exact
  let revised ← (exactCached.register [.prototype "L1", .prototype "R1"]
    (layer "replacement"))
    |>.mapError (fun _ => "invalid method arity")
  let (changed, _) ← (revised.call call).mapError (fun _ => "invalid call arity")
  return (labels, cached.cache.size, revised.cache.size, ← changed,
    exactCached.cache.size, exactLabels)

#guard match exercise with
  | .ok (first, 1, 0, changed, 1, exact) =>
    first == ["L1/R1", "L1/R0", "L2/R0", "L0/R1", "L0/R0",
      "any/R1", "any/any"] &&
      exact == ["quantity=42", "L1/R1", "L1/R0", "L2/R0",
        "L0/R1", "L0/R0", "any/R1", "any/any"] &&
      changed == ["replacement", "L1/R0", "L2/R0", "L0/R1", "L0/R0",
        "any/R1", "any/any"]
  | _ => false

#guard match callShape with
  | .ok call =>
    call.left.precedence == ["LF", "L1", "L2", "L0"] &&
      call.right.precedence == ["R1", "R0"]
  | _ => false

-- Registration enforces the generic function's fixed arity.
#guard match generic.register [.prototype "L0"] baseMethod with
  | .error (.arity 2 1) => true
  | _ => false

end LeanPoo.Examples.MultipleDispatch
