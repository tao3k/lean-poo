import LeanPoo.Object.Layout

open LeanPoo

namespace LeanPoo.Tests.SuffixLayout

abbrev Field (_ : String) := Nat

private def graph : C4.Graph :=
  { nodes :=
    [{ name := "Object", suffix := true },
     { name := "Named", parentOrders := [["Object"]], suffix := true },
     { name := "Special", parentOrders := [["Named"]], suffix := true },
     { name := "Foreign", suffix := true },
     { name := "Other" },
     { name := "Child", parentOrders := [["Other", "Named"]] },
     { name := "ChildSpecial", parentOrders := [["Other", "Special"]] }] }

private def declaration (name : String) : Option (Object.Declaration String Field) :=
  match name with
  | "Object" => some (Object.Declaration.empty.withDefault "base" 1)
  | "Named" => some (Object.Declaration.empty.withDefault "named" 2)
  | "Special" => some (Object.Declaration.empty.withDefault "special" 4)
  | "Foreign" => some (Object.Declaration.empty.withDefault "base" 99)
  | "Other" => some (Object.Declaration.empty.withDefault "other" 3)
  | "Child" => some (Object.Declaration.empty
      |>.withDefault "base" 10
      |>.withSlot "derived" (.self fun self =>
        some ((self "base").getD 0 + 1)))
  | "ChildSpecial" => some (Object.Declaration.empty.withDefault "base" 20)
  | _ => none

private def schema : Object.Schema String Field := { graph, declaration }

private def observed : Option Bool := do
  let childPlan ← (Object.compile schema "Child").toOption
  let specialPlan ← (Object.compile schema "ChildSpecial").toOption
  let foreignPlan ← (Object.compile schema "Foreign").toOption
  let child := childPlan.memoizeCompiled.layout
  let special := specialPlan.memoizeCompiled.layout
  let foreign := foreignPlan.memoizeCompiled.layout
  let baseField ← child.suffixField? "base"
  let namedField ← child.suffixField? "named"
  let names (layout : Object.SlotLayout String Field) :=
    layout.fields.toList.map Object.Entry.key
  let (otherValue1, otherSite1, otherHit1) :=
    (Object.SlotAccessSite.mk "other" none).read child
  let (otherValue2, otherSite2, otherHit2) := otherSite1.read child
  let (otherValue3, otherSite3, otherHit3) := otherSite2.read special
  let (otherValue4, _, otherHit4) := otherSite3.read special
  let (baseValue1, baseSite, baseHit1) :=
    (Object.SlotAccessSite.mk "base" none).read child
  let (baseValue2, _, baseHit2) := baseSite.read special
  let (staleValue, _, staleHit) :=
    (Object.SlotAccessSite.mk "other" (some 999)).read special
  return childPlan.precedence == ["Child", "Other", "Named", "Object"] &&
    specialPlan.precedence ==
      ["ChildSpecial", "Other", "Special", "Named", "Object"] &&
    names child == ["base", "named", "other", "derived"] &&
    names special == ["base", "named", "special", "other"] &&
    child.suffixSize == 2 && special.suffixSize == 3 &&
    child.suffixAncestors.toList == ["Object", "Named"] &&
    special.suffixAncestors.toList == ["Object", "Named", "Special"] &&
    child.offsets.get? "base" == some 0 &&
    special.offsets.get? "base" == some 0 &&
    child.offsets.get? "named" == some 1 &&
    special.offsets.get? "named" == some 1 &&
    child.offsets.get? "other" == some 2 &&
    special.offsets.get? "other" == some 3 &&
    (child.suffixField? "other").isNone &&
    baseField.offset == 0 && namedField.offset == 1 &&
    baseField.introducedBy == "Object" &&
    namedField.introducedBy == "Named" &&
    baseField.read child == (some 10, true) &&
    baseField.read special == (some 20, true) &&
    baseField.read foreign == (some 99, false) &&
    namedField.read special == (some 2, true) &&
    child.read "base" == some 10 &&
    child.read "derived" == some 11 &&
    special.read "base" == some 20 &&
    child.readAt 0 "other" == child.object.read "other" &&
    child.readAt 999 "base" == child.object.read "base" &&
    child.read "missing" == none &&
    otherValue1 == some 3 && !otherHit1 &&
    otherValue2 == some 3 && otherHit2 &&
    otherValue3 == some 3 && !otherHit3 &&
    otherValue4 == some 3 && otherHit4 &&
    baseValue1 == some 10 && !baseHit1 &&
    baseValue2 == some 20 && baseHit2 &&
    staleValue == some 3 && !staleHit

example : observed = some true := by native_decide

private def sharedObserved : Option Bool := do
  let childPlan ← (Object.compile schema "Child").toOption
  let specialPlan ← (Object.compile schema "ChildSpecial").toOption
  let child := childPlan.memoizeCompiled.layout
  let special := specialPlan.memoizeCompiled.layout
  let empty : Object.SharedSlotOffsets String := {}
  let first : Object.PolySlotAccessSite String := ⟨"other", []⟩
  let (one, first, shared, local1, shared1) := first.read empty child
  let collision := { special with shapeId := child.shapeId }
  let (collisionValue, _, _, collisionLocal, collisionShared) :=
    first.read shared collision
  let (two, first, shared, local2, shared2) := first.read shared special
  let (three, _, shared, local3, shared3) := first.read shared child
  let second : Object.PolySlotAccessSite String := ⟨"other", []⟩
  let (four, _, _, local4, shared4) := second.read shared special
  let missing : Object.PolySlotAccessSite String := ⟨"absent", []⟩
  let (absent, _, _, absentLocal, absentShared) := missing.read shared child
  return one == some 3 && two == some 3 && three == some 3 &&
    collisionValue == some 3 && !collisionLocal && !collisionShared &&
    four == some 3 && absent == none &&
    !local1 && !shared1 && !local2 && !shared2 &&
    local3 && !shared3 && !local4 && shared4 &&
    !absentLocal && !absentShared &&
    shared.candidates "other" == [3, 2] &&
    shared.candidates "absent" == []

example : sharedObserved = some true := by native_decide

example :
    let cache : Object.SharedSlotOffsets String := {}
    ((List.range 12).foldl (fun current offset =>
      current.remember "key" offset) cache).candidates "key" =
      [11, 10, 9, 8, 7, 6, 5, 4] := by native_decide

example :
    ((List.range 8).foldl (fun (site : Object.PolySlotAccessSite String) offset =>
      site.remember (UInt64.ofNat offset) offset) ⟨"key", []⟩).recent =
      [(7, 7), (6, 6), (5, 5), (4, 4)] := by native_decide

end LeanPoo.Tests.SuffixLayout
