import LeanPoo.Object.StaticDispatch
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.StaticDispatch

abbrev Payload : String → Type := fun _ => Nat
abbrev Item := Object.Plan String Payload

def plans : Except C4.Error (Item × Item) := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base ← LeanPoo.mix empty "Base" [] Object.Declaration.empty
  let child ← LeanPoo.extend base.schema "Child" "Base"
    Object.Declaration.empty
  return (base, child)

def generic : Object.Multimethod (Item × Nat) Nat Nat :=
  { arity := 1
    precedence := fun call => [call.1.precedence]
    combine := fun methods call => methods.foldl Nat.add call.2 }

def exercise : Except String (Nat × Nat × Nat × Nat × Bool × Nat) := do
  let (base, child) ← plans.mapError (fun _ => "invalid C4 graph")
  let g ← (generic.register [.prototype "Base"] 1).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Child"] 10).mapError
    (fun _ => "invalid method arity")
  let g ← (g.registerWhen [.prototype "Child"]
    (fun call => call.2 == 7) 100).mapError
    (fun _ => "invalid method arity")
  let compiled ← (g.compile (child, 2)).mapError
    (fun _ => "invalid dispatch shape")
  let fixed := compiled.call compiled.witness rfl
  let selected ← (compiled.callChecked (child, 7)).mapError
    (fun _ => "unexpected shape change")
  let (dynamic, _) ← (g.call (child, 7)).mapError
    (fun _ => "invalid dynamic call")
  let revised ← (g.register [.prototype "Child"] 20).mapError
    (fun _ => "invalid method arity")
  let (newValue, _) ← (revised.call (child, 2)).mapError
    (fun _ => "invalid revised call")
  let wrongShape := match compiled.callChecked (base, 2) with
    | .error (.shapeMismatch _ _) => true
    | _ => false
  return (fixed, selected, dynamic, newValue, wrongShape,
    compiled.candidates.size)

#guard match exercise with
  | .ok (13, 118, 118, 23, true, 3) => true
  | _ => false

end LeanPoo.Examples.StaticDispatch
