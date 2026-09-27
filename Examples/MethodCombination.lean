import LeanPoo.Object.MethodCombination
import LeanPoo.Object.Class
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.MethodCombination

open Object.MethodCombination

structure Rectangle where
  width : Nat
  height : Nat
  scale : Nat

abbrev Trace := StateT (List String) (Except String)

def mark (name : String) : Trace Unit :=
  modify (name :: ·)

inductive Key where
  | methods
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Value : Key → Type
  | .methods => Methods Rectangle Trace Nat

def base : Object.ClassSpec Key Value :=
  { name := "Rectangle"
    rules := [{ key := .methods
                compute := some (specifications [
                  .before (fun _ => mark "before-base"),
                  .primary (fun _ receiver => do
                    mark "primary-base"
                    return receiver.width * receiver.height),
                  .after (fun _ => mark "after-base")]) }] }

def scaled : Object.ClassSpec Key Value :=
  { name := "Scaled"
    rules := [{ key := .methods
                compute := some (specifications [
                  .before (fun _ => mark "before-scaled"),
                  .primary (fun next receiver => do
                    mark "primary-scaled"
                    return receiver.scale * (← next ())),
                  .after (fun _ => mark "after-scaled"),
                  .around (fun next _ => do
                    mark "around-enter"
                    let result ← next ()
                    mark "around-exit"
                    return result + 10)]) }] }

def audited : Object.ClassSpec Key Value :=
  { name := "Audited"
    rules := [{ key := .methods
                compute := some (specifications [
                  .before (fun _ => mark "before-audited"),
                  .primary (fun next _ => do
                    mark "primary-audited"
                    return (← next ()) + 1),
                  .after (fun _ => mark "after-audited")]) }] }

def result : Except C4.Error (List String × Except String (Nat × List String)) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Rectangle" [] base.toDeclaration
  let left ← LeanPoo.extend basePlan.schema "Scaled" "Rectangle"
    scaled.toDeclaration
  let right ← LeanPoo.extend left.schema "Audited" "Rectangle"
    audited.toDeclaration
  let joined ← LeanPoo.mix right.schema "Final" ["Scaled", "Audited"]
    Object.Declaration.empty
  let methods := (joined.memoize.read .methods).getD {}
  let receiver : Rectangle := ⟨3, 4, 2⟩
  let action := (effective methods fun _ => throw "no primary method") receiver
  return (joined.precedence, action.run [])

#guard match result with
  | .ok (precedence, .ok (value, reverseTrace)) =>
    precedence == ["Final", "Scaled", "Audited", "Rectangle"] &&
      value == 36 && reverseTrace.reverse == [
        "around-enter",
        "before-scaled", "before-audited", "before-base",
        "primary-scaled", "primary-audited", "primary-base",
        "after-base", "after-audited", "after-scaled",
        "around-exit"]
  | _ => false

end LeanPoo.Examples.MethodCombination
