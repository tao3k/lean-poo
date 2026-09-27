import LeanPoo.Object.Layout

/-! Two independently written readers share recently learned field offsets
while objects from different branches place the field at different positions. -/

namespace LeanPoo.Examples.SharedFieldAccess

private abbrev Field (_ : String) := Nat

private def schema : Object.Schema String Field :=
  { graph := { nodes :=
      [{ name := "Base", suffix := true },
       { name := "Extra" },
       { name := "Plain", parentOrders := [["Base"]] },
       { name := "Extended", parentOrders := [["Extra", "Base"]] }] }
    declaration := fun name => match name with
      | "Base" => some (Object.Declaration.empty.withDefault "base" 1)
      | "Extra" => some (Object.Declaration.empty.withDefault "extra" 2)
      | "Plain" => some (Object.Declaration.empty.withDefault "status" 10)
      | "Extended" => some (Object.Declaration.empty.withDefault "status" 20)
      | _ => none }

def run : Option (List (Option Nat × Bool × Bool)) := do
  let plain ← (Object.compile schema "Plain").toOption
  let extended ← (Object.compile schema "Extended").toOption
  let plain := plain.memoizeCompiled.layout
  let extended := extended.memoizeCompiled.layout
  let readerA : Object.PolySlotAccessSite String := ⟨"status", []⟩
  let readerB : Object.PolySlotAccessSite String := ⟨"status", []⟩
  let shared : Object.SharedSlotOffsets String := {}
  let (value1, readerA, shared, local1, shared1) := readerA.read shared plain
  let (value2, readerA, shared, local2, shared2) := readerA.read shared extended
  let (value3, _, shared, local3, shared3) := readerA.read shared plain
  let (value4, _, _, local4, shared4) := readerB.read shared extended
  return [(value1, local1, shared1), (value2, local2, shared2),
    (value3, local3, shared3), (value4, local4, shared4)]

#eval run

end LeanPoo.Examples.SharedFieldAccess
