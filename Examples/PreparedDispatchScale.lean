import LeanPoo.Object.MultimethodCombination

namespace LeanPoo.Examples.PreparedDispatchScale

abbrev Args := List String × Nat
abbrev Contribution := Object.MethodCombination.Contribution Args Id Nat

def names (methodCount : Nat) : List String :=
  (List.range methodCount).map (fun i => s!"P{i}")

def precedence (args : Args) : List (List String) := [args.1]

def contribution : Contribution :=
  .primary (fun next _ => do return (← next ()) + 1)

def baseline (methodCount : Nat) : Except Object.MultimethodError
    (Object.Multimethod Args Contribution (Id Nat)) := do
  let mut generic := Object.Multimethod.standard 1 precedence
    (fun args : Args => args.2)
  for name in names methodCount do
    generic ← generic.register [.prototype name] contribution
  return generic

def prepared (methodCount : Nat) : Except Object.MultimethodError
    (Object.PreparedMultimethod Args Contribution (Args → Id Nat) (Id Nat)) := do
  let mut generic := Object.Multimethod.preparedStandard 1 precedence
    (fun args : Args => args.2)
  for name in names methodCount do
    generic ← generic.register [.prototype name] contribution
  return generic

def baselineLoop (count methodCount : Nat) : Except Object.MultimethodError
    (Nat × Object.Multimethod Args Contribution (Id Nat)) := do
  let mut generic ← baseline methodCount
  let mut checksum := 0
  for i in [:count] do
    let (value, updated) ← generic.call (names methodCount, i)
    checksum := checksum + value.run
    generic := updated
  return (checksum, generic)

def preparedLoop (count methodCount : Nat) : Except Object.MultimethodError
    (Nat × Object.PreparedMultimethod Args Contribution
      (Args → Id Nat) (Id Nat)) := do
  let mut generic ← prepared methodCount
  let mut checksum := 0
  for i in [:count] do
    let (value, updated) ← generic.call (names methodCount, i)
    checksum := checksum + value.run
    generic := updated
  return (checksum, generic)

def main : IO Unit := do
  let count := ((← IO.getEnv "LEANPOO_BENCH_CALLS").getD "100000")
    |>.toNat?.getD 100000
  let methodCount := ((← IO.getEnv "LEANPOO_BENCH_METHODS").getD "32")
    |>.toNat?.getD 32
  let baselineStart ← IO.monoNanosNow
  let (left, _) ← match baselineLoop count methodCount with
    | .ok result => pure result
    | .error _ => throw (IO.userError "baseline dispatch failed")
  let baselineElapsed := (← IO.monoNanosNow) - baselineStart
  let preparedStart ← IO.monoNanosNow
  let (right, updated) ← match preparedLoop count methodCount with
    | .ok result => pure result
    | .error _ => throw (IO.userError "prepared dispatch failed")
  let preparedElapsed := (← IO.monoNanosNow) - preparedStart
  if left != right then
    throw (IO.userError "prepared method result differs from baseline")
  IO.println s!"calls={count} methods={methodCount} checksum={left} baseline_ns={baselineElapsed} prepared_ns={preparedElapsed} effective_shapes={updated.effectiveCache.size}"

end LeanPoo.Examples.PreparedDispatchScale

def main : IO Unit := LeanPoo.Examples.PreparedDispatchScale.main
