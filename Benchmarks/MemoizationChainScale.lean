import LeanPoo.Object.Memo

open LeanPoo

private def plan (count : Nat) : Except C4.Error
    (Object.Plan Nat (fun _ => Nat)) := do
  let empty : Object.Schema Nat (fun _ => Nat) :=
    { graph := { nodes := [] }, declaration := fun _ => none }
  let mut current ← LeanPoo.mix empty "Base" []
    (Object.Declaration.empty.withValue 0 0)
  for index in [1:count] do
    current ← LeanPoo.extend current.schema s!"L{index}" current.root
      (Object.Declaration.empty.withValue index index)
  return current

private def sample (mode : Object.ResolutionMode) (dense : Bool)
    (source : Object.Plan Nat (fun _ => Nat)) : IO Unit := do
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:10] do
    let object := source.memoizeUsing mode
    if dense then
      for key in [:64] do
        checksum := checksum + (object.read key).getD 0
    else
      checksum := checksum + (object.read 63).getD 0
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  let modeName := match mode with
    | .onDemand => "onDemand"
    | .compiled => "compiled"
    | .indexed => "indexed"
  IO.println s!"mode={modeName} dense={dense} layers=64 rounds=10 elapsed_us={elapsedUs} checksum={checksum}"

def main : IO Unit := do
  let .ok source := plan 64 | throw (IO.userError "C4 plan failed")
  for dense in [false, true] do
    for mode in [Object.ResolutionMode.onDemand, .compiled, .indexed] do
      sample mode dense source
