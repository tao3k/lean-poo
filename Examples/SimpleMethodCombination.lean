import LeanPoo.Object.MethodCombination
import LeanPoo.Object.Class
import LeanPoo.Object.Memo

namespace LeanPoo.Examples.SimpleMethodCombination

open Object.MethodCombination

abbrev Trace := StateT (List String) (Except String)

def mark (name : String) : Trace Unit :=
  modify (name :: ·)

inductive Key where
  | checks
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

def Value : Key → Type
  | .checks => SimpleMethods String Trace Bool Bool

def allChecks : SimplePolicy Bool Bool Bool :=
  { stop := not
    empty := true
    first := id
    step := fun value previous => previous && value
    finish := id }

def base : Object.ClassSpec Key Value :=
  { name := "Base"
    rules := [{ key := .checks
                compute := some (simpleSpecifications [
                  .item (fun _ => do mark "base"; return true)]) }] }

def left : Object.ClassSpec Key Value :=
  { name := "Left"
    rules := [{ key := .checks
                compute := some (simpleSpecifications [
                  .item (fun _ => do mark "left"; return false),
                  .around (fun next _ => do
                    mark "around-enter"
                    let result ← next ()
                    mark "around-exit"
                    return result)]) }] }

def right : Object.ClassSpec Key Value :=
  { name := "Right"
    rules := [{ key := .checks
                compute := some (simpleSpecifications [
                  .item (fun _ => do mark "right"; return true)]) }] }

/-- `and` stops after the first false contribution, while `around` still
wraps the result. The inherited right and base bodies are never run. -/
def result : Except C4.Error (List String × Except String (Bool × List String)) := do
  let empty : Object.Schema Key Value :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let root ← LeanPoo.mix empty "Base" [] base.toDeclaration
  let leftPlan ← LeanPoo.extend root.schema "Left" "Base" left.toDeclaration
  let rightPlan ← LeanPoo.extend leftPlan.schema "Right" "Base" right.toDeclaration
  let final ← LeanPoo.mix rightPlan.schema "Final" ["Left", "Right"]
    Object.Declaration.empty
  let methods := (final.memoize.read .checks).getD {}
  return (final.precedence, (simpleEffective allChecks methods "receiver").run [])

#guard (match result with
  | .ok (precedence, .ok (value, reverseTrace)) =>
    precedence == ["Final", "Left", "Right", "Base"] &&
      !value && reverseTrace.reverse == ["around-enter", "left", "around-exit"]
  | _ => false)

-- The paper's neutral element is returned when no sub-method is present.
#guard (match (simpleEffective allChecks
    ({} : SimpleMethods String Trace Bool Bool) "receiver").run [] with
  | .ok (true, []) => true
  | _ => false)

end LeanPoo.Examples.SimpleMethodCombination
