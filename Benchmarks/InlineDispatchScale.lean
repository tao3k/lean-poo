import LeanPoo.Object.InlineDispatch

namespace LeanPoo.Benchmarks.InlineDispatchScale

private abbrev Args := List String × Nat

private def names (count : Nat) : List String :=
  (List.range count).map (fun i => s!"P{i}")

private def generic (methodCount : Nat) : Except Object.MultimethodError
    (Object.Multimethod Args Nat Nat) := do
  let mut result : Object.Multimethod Args Nat Nat :=
    { arity := 1
      precedence := fun args => [args.1]
      combine := fun methods args => methods.foldl (· + ·) args.2 }
  for i in [:methodCount] do
    result ← result.register [.prototype s!"P{i}"] (i + 1)
  result.registerWhen [.prototype "P0"]
    (fun args => args.2 == 0) 1000

private def directLoop (initial : Object.Multimethod Args Nat Nat)
    (methodCount count : Nat) : IO Nat := do
  let checksum ← IO.mkRef 0
  let order := names methodCount
  for i in [:count] do
    let args : Args := (order, i % 2)
    let .ok value := Object.InlineDispatch.direct initial args |
      throw (IO.userError "direct dispatch failed")
    checksum.modify (· + value)
  checksum.get

private def genericLoop (initial : Object.Multimethod Args Nat Nat)
    (methodCount count : Nat) : IO (Nat × Object.Multimethod Args Nat Nat) := do
  let checksum ← IO.mkRef 0
  let order := names methodCount
  let mut current := initial
  for i in [:count] do
    let args : Args := (order, i % 2)
    let .ok (value, updated) := current.call args |
      throw (IO.userError "generic dispatch failed")
    checksum.modify (· + value)
    current := updated
  return (← checksum.get, current)

private def inlineLoop (initial : Object.Multimethod Args Nat Nat)
    (methodCount count : Nat) : IO (Nat × Object.InlineDispatch Args Nat Nat) := do
  let checksum ← IO.mkRef 0
  let order := names methodCount
  let mut current := Object.InlineDispatch.create initial
  for i in [:count] do
    let args : Args := (order, i % 2)
    let .ok (value, updated) := current.call args |
      throw (IO.userError "inline dispatch failed")
    checksum.modify (· + value)
    current := updated
  return (← checksum.get, current)

def main : IO Unit := do
  let count := ((← IO.getEnv "LEANPOO_BENCH_CALLS").getD "20000")
    |>.toNat?.getD 20000
  let methodCount := ((← IO.getEnv "LEANPOO_BENCH_METHODS").getD "64")
    |>.toNat?.getD 64
  let .ok initial := generic methodCount |
    throw (IO.userError "generic setup failed")
  let startedDirect ← IO.monoNanosNow
  let direct ← directLoop initial methodCount count
  let directNs := (← IO.monoNanosNow) - startedDirect
  let startedGeneric ← IO.monoNanosNow
  let (ordinary, updatedGeneric) ← genericLoop initial methodCount count
  let genericNs := (← IO.monoNanosNow) - startedGeneric
  let startedInline ← IO.monoNanosNow
  let (inlineValue, updatedInline) ← inlineLoop initial methodCount count
  let inlineNs := (← IO.monoNanosNow) - startedInline
  if direct != ordinary || direct != inlineValue then
    throw (IO.userError "call-site dispatch differs from direct dispatch")
  IO.println s!"calls={count} methods={methodCount} checksum={direct} direct_ns={directNs} generic_ns={genericNs} inline_ns={inlineNs} generic_shapes={updatedGeneric.cache.size} inline_entries={updatedInline.entries.length}"

end LeanPoo.Benchmarks.InlineDispatchScale

def main : IO Unit := LeanPoo.Benchmarks.InlineDispatchScale.main
