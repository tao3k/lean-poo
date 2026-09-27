import LeanPoo.Object.MethodDictionary

/-! A layered formatter: the caller can keep an earlier method while the
runtime object acquires a later override. -/

namespace LeanPoo.Examples.MethodDictionary

open LeanPoo

inductive Key where
  | format
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Method := Object.DictionaryMethod Key Nat (fun _ => String) (fun _ => String)

def base : Object.Declaration Key Method :=
  Object.Declaration.empty.withValue .format
    (fun receiver suffix => s!"record {receiver}{suffix}")

def wrapped : Object.Declaration Key Method :=
  Object.Declaration.empty.withSlot .format
    (.computed fun _ inherited => do
      let previous ← inherited ()
      return fun receiver suffix => s!"[{previous receiver suffix}]")

def usage : Except C4.Error (String × String × String) := do
  let empty : Object.Schema Key Method :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let childPlan ← LeanPoo.extend basePlan.schema "Wrapped" "Base" wrapped
  let original := Object.MethodDictionary.fromMemoized basePlan.memoizeCompiled
  let updated := Object.MethodDictionary.fromMemoized childPlan.memoizeCompiled
  let object : Object.DictionaryObject Key Nat (fun _ => String) (fun _ => String) :=
    { receiver := 42, methods := updated }
  let fallback : Nat → String → String := fun _ _ => "missing"
  let selected := original.select .format fallback
  return (object.callDynamic .format "!" fallback,
    object.callStatic original .format "!" fallback,
    object.callSelected selected "!")

#eval usage

end LeanPoo.Examples.MethodDictionary
