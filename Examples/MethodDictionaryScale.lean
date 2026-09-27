import LeanPoo.Object.MethodDictionary

namespace LeanPoo.Examples.MethodDictionaryScale

private abbrev Args (_ : String) := Nat
private abbrev Result (_ : String) := Nat
private abbrev Method := Object.DictionaryMethod String Nat Args Result
private abbrev Dictionary := Object.MethodDictionary String Nat Args Result

private def dictionary (count : Nat) : Option Dictionary := do
  let declaration : Object.Declaration String Method :=
    (List.range count).foldl (fun current i =>
      current.withValue s!"method-{i}" (fun receiver arg => receiver + arg + i))
      Object.Declaration.empty
  let schema : Object.Schema String Method :=
    { graph := { nodes := [{ name := "Base" }] }
      declaration := fun _ => some declaration }
  let plan ← (Object.compile schema "Base").toOption
  return Object.MethodDictionary.fromMemoized plan.memoizeCompiled

private def fallback : Nat → Nat → Nat := fun _ _ => 0

private def dynamicLoop
    (object : Object.DictionaryObject String Nat Args Result)
    (count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  for i in [:count] do
    checksum.modify (· + object.callDynamic "method-32" i fallback)
  checksum.get

private def selectedLoop
    (object : Object.DictionaryObject String Nat Args Result)
    (selected : Nat → Nat → Nat) (count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  for i in [:count] do
    checksum.modify (· + object.callSelected (key := "method-32") selected i)
  checksum.get

def main : IO Unit := do
  let count := ((← IO.getEnv "LEANPOO_BENCH_CALLS").getD "100000")
    |>.toNat?.getD 100000
  let some methods := dictionary 64 |
    throw (IO.userError "dictionary setup failed")
  let object : Object.DictionaryObject String Nat Args Result :=
    { receiver := 7, methods }
  let selected := methods.select "method-32" fallback
  let startedDynamic ← IO.monoNanosNow
  let dynamicValue ← dynamicLoop object count
  let dynamicNs := (← IO.monoNanosNow) - startedDynamic
  let startedSelected ← IO.monoNanosNow
  let selectedValue ← selectedLoop object selected count
  let selectedNs := (← IO.monoNanosNow) - startedSelected
  if dynamicValue != selectedValue then
    throw (IO.userError "preselected method differs from dynamic dictionary")
  IO.println s!"calls={count} methods=64 checksum={dynamicValue} dynamic_ns={dynamicNs} selected_ns={selectedNs}"

end LeanPoo.Examples.MethodDictionaryScale

def main : IO Unit := LeanPoo.Examples.MethodDictionaryScale.main
