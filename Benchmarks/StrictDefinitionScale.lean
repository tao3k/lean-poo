import LeanPoo.Object.StrictBuilder

open LeanPoo

private def ordered (count : Nat) : Object.Declaration Nat (fun _ => Nat) :=
  Object.Declaration.build do
    for key in [:count] do
      Object.Declaration.Builder.value key key
      Object.Declaration.Builder.default key (key + 1)

private def checked (count : Nat) :
    Except (Object.Declaration.DuplicateError Nat)
      (Object.Declaration Nat (fun _ => Nat)) :=
  Object.Declaration.StrictBuilder.build do
    for key in [:count] do
      Object.Declaration.StrictBuilder.value key key
      Object.Declaration.StrictBuilder.default key (key + 1)

private def benchmarkAt (count : Nat) : IO Unit := do
  let startOrdered ← IO.monoMsNow
  let ordinary := ordered count
  IO.println s!"ordered_count={count} slots={ordinary.slots.length} defaults={ordinary.defaults.length}"
  IO.println s!"ordered_elapsed_ms={(← IO.monoMsNow) - startOrdered}"
  let startChecked ← IO.monoMsNow
  match checked count with
  | .error _ => throw <| IO.userError "unexpected duplicate in strict benchmark"
  | .ok declaration =>
    IO.println s!"strict_count={count} slots={declaration.slots.length} defaults={declaration.defaults.length}"
  IO.println s!"strict_elapsed_ms={(← IO.monoMsNow) - startChecked}"

def main : IO Unit := do
  benchmarkAt 1000
  benchmarkAt 2000
  benchmarkAt 4000
