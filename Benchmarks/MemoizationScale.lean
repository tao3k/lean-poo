import LeanPoo.Object.Memo

open LeanPoo

private def plan (count : Nat) : Except C4.Error
    (Object.Plan Nat (fun _ => Nat)) := do
  let entries : Std.DHashMap Nat (fun _ => Nat) :=
    (List.range count).foldl (fun table key => table.insert key key) {}
  let declaration := Object.Declaration.fromMap entries (· <= ·)
  let schema : Object.Schema Nat (fun _ => Nat) :=
    { graph := { nodes := [{ name := "Base" }] }
      declaration := fun name =>
        if name == "Base" then some declaration else none }
  Object.compile schema "Base"

private def sample (mode : Object.ResolutionMode) (dense : Bool) (rounds count : Nat)
    (source : Object.Plan Nat (fun _ => Nat)) : IO Unit := do
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:rounds] do
    let object := source.memoizeUsing mode
    if dense then
      for key in [:count] do
        checksum := checksum + (object.read key).getD 0
    else
      checksum := checksum + (object.read (count - 1)).getD 0
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  let modeName := match mode with
    | .onDemand => "onDemand"
    | .compiled => "compiled"
    | .indexed => "indexed"
  IO.println s!"mode={modeName} dense={dense} keys={count} rounds={rounds} elapsed_us={elapsedUs} checksum={checksum}"

private def sampleReused (dense : Bool) (rounds count : Nat)
    (source : Object.Plan Nat (fun _ => Nat)) : IO Unit := do
  let compiled := source.compileMemo
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:rounds] do
    let object := compiled.instantiate
    if dense then
      for key in [:count] do
        checksum := checksum + (object.read key).getD 0
    else
      checksum := checksum + (object.read (count - 1)).getD 0
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  IO.println s!"mode=compiledReused dense={dense} keys={count} rounds={rounds} elapsed_us={elapsedUs} checksum={checksum}"

def main : IO Unit := do
  let .ok source := plan 256 | throw (IO.userError "C4 plan failed")
  for dense in [false, true] do
    for mode in [Object.ResolutionMode.onDemand,
        .compiled, .indexed] do
      sample mode dense 10 256 source
    sampleReused dense 10 256 source
