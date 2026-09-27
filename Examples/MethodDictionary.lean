import LeanPoo.Object.MethodDictionary

open LeanPoo

namespace LeanPoo.Examples.MethodDictionary

inductive Key where
  | quote
  | level
  | audit
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Hashable

abbrev Args : Key → Type
  | .quote => String
  | .level => Unit
  | .audit => Bool

abbrev Result : Key → Type
  | .quote => String
  | .level => Nat
  | .audit => Bool

abbrev Method := Object.DictionaryMethod Key Nat Args Result
abbrev Dictionary := Object.MethodDictionary Key Nat Args Result

private def base : Object.Declaration Key Method :=
  Object.Declaration.empty
    |>.withValue .quote (fun receiver suffix => s!"base:{receiver}:{suffix}")
    |>.withValue .level (fun receiver _ => receiver + 1)

private def child : Object.Declaration Key Method :=
  Object.Declaration.empty |>.withSlot .quote
    (.computed fun _ inherited =>
      let parent := (inherited ()).getD (fun _ _ => "missing")
      some (fun receiver suffix => s!"child({parent receiver suffix})"))

private def late : Object.Declaration Key Method :=
  Object.Declaration.empty |>.withSlot .quote
    (.computed fun _ inherited =>
      let parent := (inherited ()).getD (fun _ _ => "missing")
      some (fun receiver suffix => s!"late({parent receiver suffix})"))

private def dictionaries : Except C4.Error (Dictionary × Dictionary × Dictionary) := do
  let empty : Object.Schema Key Method :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let basePlan ← LeanPoo.mix empty "Base" [] base
  let childPlan ← LeanPoo.extend basePlan.schema "Child" "Base" child
  let latePlan ← LeanPoo.extend childPlan.schema "Late" "Child" late
  return (Object.MethodDictionary.fromMemoized basePlan.memoizeCompiled,
    Object.MethodDictionary.fromMemoized childPlan.memoizeCompiled,
    Object.MethodDictionary.fromMemoized latePlan.memoizeCompiled)

private def quoteFallback : Nat → String → String :=
  fun _ _ => "missing quote"

private def levelFallback : Nat → Unit → Nat :=
  fun _ _ => 0

private def auditFallback : Nat → Bool → Bool :=
  fun receiver allowed => receiver > 0 && allowed

private def observed : Option Bool := do
  let (baseDict, childDict, lateDict) ← dictionaries.toOption
  let object : Object.DictionaryObject Key Nat Args Result :=
    { receiver := 7, methods := childDict }
  let revised := object.withMethods lateDict
  let selectedQuote := baseDict.select .quote quoteFallback
  let selectedAudit := baseDict.select .audit auditFallback
  let generic : Object.Generic Nat (Method .quote) String String :=
    Object.Generic.fromDictionary (.quote : Key)
    (fun receiver => if receiver >= 10 then lateDict else baseDict)
    quoteFallback
  return (
    object.callDynamic .quote "x" quoteFallback == "child(base:7:x)" &&
    object.callStatic baseDict .quote "x" quoteFallback == "base:7:x" &&
    object.callSelected selectedQuote "x" == "base:7:x" &&
    object.callStatic childDict .quote "x" quoteFallback ==
      object.callDynamic .quote "x" quoteFallback &&
    object.callDynamic .level () levelFallback == 8 &&
    object.callStatic baseDict .level () levelFallback == 8 &&
    object.callDynamic .audit true auditFallback == true &&
    object.callDynamic .audit false auditFallback == false &&
    object.callSelected selectedAudit true == true &&
    revised.callDynamic .quote "x" quoteFallback ==
      "late(child(base:7:x))" &&
    revised.callStatic baseDict .quote "x" quoteFallback == "base:7:x" &&
    revised.callSelected selectedQuote "x" == "base:7:x" &&
    object.callDynamic .quote "x" quoteFallback == "child(base:7:x)" &&
    generic.call 7 "x" == "base:7:x" &&
    generic.call 10 "x" == "late(child(base:10:x))")

example : observed = some true := by native_decide

end LeanPoo.Examples.MethodDictionary
