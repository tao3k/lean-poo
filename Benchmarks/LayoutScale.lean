import LeanPoo.Object.Layout

namespace LeanPoo.Benchmarks.LayoutScale

private def object : Option (Object.Memoized String (fun _ => Nat)) := do
  let entries : List (Sigma (fun _ : String => Nat)) :=
    (List.range 64).map fun i => ⟨s!"field-{i}", i⟩
  let declaration := Object.Declaration.fromValuesIndexed entries
  let schema : Object.Schema String (fun _ => Nat) :=
    { graph := { nodes := [{ name := "Root", suffix := true }] }
      declaration := fun _ => some declaration }
  let plan ← (Object.compile schema "Root").toOption
  return plan.memoizeCompiled

private def keyedLoop (object : Object.Memoized String (fun _ => Nat))
    (count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  for i in [:count] do
    let key := if i % 2 == 0 then "field-32" else "field-33"
    checksum.modify (· + (object.read key).getD 0)
  checksum.get

private def offsetLoop (layout : Object.SlotLayout String (fun _ => Nat))
    (offset32 offset33 count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  for i in [:count] do
    let key := if i % 2 == 0 then "field-32" else "field-33"
    let offset := if i % 2 == 0 then offset32 else offset33
    checksum.modify (· + (layout.readAt offset key).getD 0)
  checksum.get

private def siteLoop (layout : Object.SlotLayout String (fun _ => Nat))
    (count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  let mut site : Object.SlotAccessSite String := ⟨"field-32", none⟩
  let mut otherSite : Object.SlotAccessSite String := ⟨"field-33", none⟩
  for i in [:count] do
    if i % 2 == 0 then
      let (value, updated, _) := site.read layout
      checksum.modify (· + value.getD 0)
      site := updated
    else
      let (value, updated, _) := otherSite.read layout
      checksum.modify (· + value.getD 0)
      otherSite := updated
  checksum.get

private def sharedSiteLoop (layout : Object.SlotLayout String (fun _ => Nat))
    (count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  let mut shared : Object.SharedSlotOffsets String := {}
  let mut site32 : Object.PolySlotAccessSite String := ⟨"field-32", []⟩
  let mut site33 : Object.PolySlotAccessSite String := ⟨"field-33", []⟩
  for i in [:count] do
    if i % 2 == 0 then
      let (value, site, cache, _, _) := site32.read shared layout
      checksum.modify (· + value.getD 0)
      site32 := site
      shared := cache
    else
      let (value, site, cache, _, _) := site33.read shared layout
      checksum.modify (· + value.getD 0)
      site33 := site
      shared := cache
  checksum.get

def main : IO Unit := do
  let count := ((← IO.getEnv "LEANPOO_BENCH_CALLS").getD "100000")
    |>.toNat?.getD 100000
  let some object := object | throw (IO.userError "layout setup failed")
  let layout := object.layout
  let some offset32 := layout.offsets.get? "field-32" |
    throw (IO.userError "field offset missing")
  let some offset33 := layout.offsets.get? "field-33" |
    throw (IO.userError "field offset missing")
  let startedKeyed ← IO.monoNanosNow
  let keyed ← keyedLoop object count
  let keyedNs := (← IO.monoNanosNow) - startedKeyed
  let startedOffset ← IO.monoNanosNow
  let offsetValue ← offsetLoop layout offset32 offset33 count
  let offsetNs := (← IO.monoNanosNow) - startedOffset
  let startedSite ← IO.monoNanosNow
  let siteValue ← siteLoop layout count
  let siteNs := (← IO.monoNanosNow) - startedSite
  let startedShared ← IO.monoNanosNow
  let sharedValue ← sharedSiteLoop layout count
  let sharedNs := (← IO.monoNanosNow) - startedShared
  if keyed != offsetValue || keyed != siteValue || keyed != sharedValue ||
      keyed != (count / 2) * 65 + (count % 2) * 32 then
    throw (IO.userError "layout read differs from keyed read")
  IO.println s!"calls={count} fields={layout.fields.size} checksum={keyed} keyed_ns={keyedNs} offset_ns={offsetNs} site_ns={siteNs} shared_site_ns={sharedNs}"

end LeanPoo.Benchmarks.LayoutScale

def main : IO Unit := LeanPoo.Benchmarks.LayoutScale.main
