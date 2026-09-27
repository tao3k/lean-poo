import LeanPoo.Object.MultimethodCombination
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.Chapter9Combination

abbrev Payload : String → Type := fun _ => Nat
abbrev Call := Object.Plan String Payload × Nat

def shape : Except C4.Error Call := do
  let empty : Object.Schema String Payload :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let base ← LeanPoo.mix empty "Base" [] Object.Declaration.empty
  let left ← LeanPoo.extend base.schema "Left" "Base"
    Object.Declaration.empty
  let right ← LeanPoo.extend left.schema "Right" "Base"
    Object.Declaration.empty
  let final ← LeanPoo.mix right.schema "Final" ["Left", "Right"]
    Object.Declaration.empty
  return (final, 2)

def precedence (call : Call) : List (List String) :=
  [call.1.precedence]

abbrev Trace := StateT (List String) (Except String)

def mark (name : String) : Trace Unit := modify (name :: ·)

def innerBody (name : String) :
    Object.MethodCombination.SubMethod Call Trace Unit :=
  fun inner _ => do
    mark s!"enter-{name}"
    inner ()
    mark s!"exit-{name}"

def beta : Object.Multimethod Call
    (Object.MethodCombination.SubMethod Call Trace Unit) (Trace Unit) :=
  Object.Multimethod.inner 1 precedence (fun _ => mark "leaf")

def betaExercise : Except String (List String × List String) := do
  let call ← shape.mapError (fun _ => "invalid C4 graph")
  let g ← (beta.register [.prototype "Base"] (innerBody "Base"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Right"] (innerBody "Right"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Left"] (innerBody "Left"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Final"] (innerBody "Final"))
    |>.mapError (fun _ => "invalid method arity")
  let (full, cached) ← (g.call call).mapError
    (fun _ => "invalid call arity")
  let (_, fullTrace) ← full.run []
  let blocked ← (cached.register [.prototype "Right"]
    (fun _ _ => mark "stop-Right"))
    |>.mapError (fun _ => "invalid method arity")
  let (short, _) ← (blocked.call call).mapError
    (fun _ => "invalid call arity")
  let (_, shortTrace) ← short.run []
  return (fullTrace.reverse, shortTrace.reverse)

#guard match betaExercise with
  | .ok (full, blocked) =>
    full == ["enter-Base", "enter-Right", "enter-Left",
      "enter-Final", "leaf", "exit-Final", "exit-Left",
      "exit-Right", "exit-Base"] &&
    blocked == ["enter-Base", "stop-Right", "exit-Base"]
  | _ => false

def simulaBody (name : String) :
    Object.MethodCombination.SimulaBody Call Trace :=
  { prefixPart := fun _ => mark s!"prefix-{name}"
    suffixPart := fun _ => mark s!"suffix-{name}" }

def simulaExercise : Except String (List String) := do
  let call ← shape.mapError (fun _ => "invalid C4 graph")
  let generic : Object.Multimethod Call
      (Object.MethodCombination.SimulaBody Call Trace) (Trace Unit) :=
    Object.Multimethod.simula 1 precedence
  let g ← (generic.register [.prototype "Base"] (simulaBody "Base"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Right"] (simulaBody "Right"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Left"] (simulaBody "Left"))
    |>.mapError (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Final"] (simulaBody "Final"))
    |>.mapError (fun _ => "invalid method arity")
  let (action, _) ← (g.call call).mapError
    (fun _ => "invalid call arity")
  let (_, trace) ← action.run []
  return trace.reverse

#guard match simulaExercise with
  | .ok trace => trace == ["prefix-Base", "prefix-Right",
      "prefix-Left", "prefix-Final", "suffix-Final",
      "suffix-Left", "suffix-Right", "suffix-Base"]
  | _ => false

abbrev Contribution := Object.MethodCombination.Contribution Call Id Nat
abbrev Prepared := Object.PreparedMultimethod Call Contribution
  (Call → Nat) Nat

def prepared : Prepared :=
  Object.Multimethod.preparedStandard 1 precedence (fun _ => 0)

def add (value : Nat) : Contribution :=
  .primary (fun next _ => do return (← next ()) + value)

def preparedExercise : Except String
    (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let call ← shape.mapError (fun _ => "invalid C4 graph")
  let g ← (prepared.register [.prototype "Base"]
    (.primary (fun _ current => current.2))).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Right"] (add 100)).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Left"] (add 10)).mapError
    (fun _ => "invalid method arity")
  let g ← (g.register [.prototype "Final"] (add 1000)).mapError
    (fun _ => "invalid method arity")
  let (first, cached) ← (g.call call).mapError
    (fun _ => "invalid call arity")
  let (second, reused) ← (cached.call (call.1, 5)).mapError
    (fun _ => "invalid call arity")
  let stableCache := reused.effectiveCache.size
  let guarded ← (reused.registerWhen [.prototype "Final"]
    (fun current => current.2 == 7) (add 10000)).mapError
    (fun _ => "invalid method arity")
  let cleared := guarded.effectiveCache.size
  let (special, guardedCached) ← (guarded.call (call.1, 7)).mapError
    (fun _ => "invalid call arity")
  let (ordinary, guardedReused) ← (guardedCached.call (call.1, 5))
    |>.mapError (fun _ => "invalid call arity")
  let guardedCache := guardedReused.effectiveCache.size
  let replaced ← (guardedReused.register [.prototype "Final"] (add 2))
    |>.mapError (fun _ => "invalid method arity")
  let (changed, _) ← (replaced.call call).mapError
    (fun _ => "invalid call arity")
  return (first, second, stableCache, cleared, special, ordinary,
    guardedCache, changed)

#guard match preparedExercise with
  | .ok (1112, 1115, 1, 0, 11117, 1115, 0, 114) => true
  | _ => false

end LeanPoo.Examples.Chapter9Combination
