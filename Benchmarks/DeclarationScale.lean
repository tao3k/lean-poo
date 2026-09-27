import LeanPoo.Object.Schema

open LeanPoo

private def values (count : Nat) : List (Sigma fun _ : Nat => Nat) :=
  (List.range count).map fun key => ⟨key, key⟩

private def benchmarkList (count : Nat) : IO Unit := do
  let started ← IO.monoMsNow
  let declaration := Object.Declaration.fromValues (values count)
  IO.println s!"slots={declaration.slots.length}"
  let elapsed := (← IO.monoMsNow) - started
  IO.println s!"elapsed_ms={elapsed}"

private def benchmarkMap (count : Nat) : IO Unit := do
  let entries : Std.DHashMap Nat (fun _ => Nat) :=
    (List.range count).foldl (fun table key => table.insert key key) {}
  IO.println s!"map_entries={entries.size}"
  let started ← IO.monoMsNow
  let declaration := Object.Declaration.fromMap entries (· <= ·)
  IO.println s!"slots={declaration.slots.length}"
  let elapsed := (← IO.monoMsNow) - started
  IO.println s!"map_elapsed_ms={elapsed}"

private def benchmarkIndexed (count : Nat) : IO Unit := do
  let started ← IO.monoMsNow
  let declaration := Object.Declaration.fromValuesIndexed (values count)
  IO.println s!"indexed_slots={declaration.slots.length}"
  let elapsed := (← IO.monoMsNow) - started
  IO.println s!"indexed_elapsed_ms={elapsed}"

def main : IO Unit := do
  benchmarkList 1000
  benchmarkList 2000
  benchmarkList 4000
  benchmarkIndexed 1000
  benchmarkIndexed 2000
  benchmarkIndexed 4000
  benchmarkMap 1000
  benchmarkMap 2000
  benchmarkMap 4000
