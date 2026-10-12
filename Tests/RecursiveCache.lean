import LeanPoo.Object.RecursiveInstance

open LeanPoo.Prototype
open LeanPoo.Prototype.Recursive
namespace LeanPoo.Tests.RecursiveCache

private def fibonacci : Generator Nat Nat := fun input =>
  if input ≤ 1 then .value input else
    (request (input - 1)).bind fun left =>
      (request (input - 2)).map (left + ·)

private def oracle (input : Nat) : Nat :=
  ((List.range input).foldl (fun (a, b) _ => (b, a + b)) (0, 1)).1

private def slots : MutableRecord.Storage :=
  let base := MutableRecord.fromValues [("x", .integer 1), ("y", .integer 2)]
  let z := MutableRecord.write base "z" (MutableRecord.compute fun self =>
    (self "x").bind fun x => (self "y").map fun y => .list [x, y])
  let a := MutableRecord.write z "a" (MutableRecord.compute fun self => self "b")
  let b := MutableRecord.write a "b" (MutableRecord.compute fun self => self "a")
  MutableRecord.write b "broken" (fun _ _ => .error "source failure")

private def runChecks : IO Unit := do
  let (answer, cache) ← IO.ofExcept ((Cached.run fibonacci 40 200).mapError reprStr)
  unless answer.result == .value (oracle 40) && cache.entries.length == 41 &&
      cache.statistics.misses == 41 && cache.statistics.hits ≥ 38 &&
      cache.statistics.steps < 200 do
    throw (IO.userError "shared call-by-need recursion or oracle")
  let (again, hot) ← IO.ofExcept ((Cached.run fibonacci 40 1 cache).mapError reprStr)
  unless again.result == answer.result && hot.statistics.misses == cache.statistics.misses &&
      hot.statistics.steps == cache.statistics.steps && hot.statistics.hits == cache.statistics.hits + 1 do
    throw (IO.userError "a hot result recomputed its prototype")
  for input in List.range 11 do
    let (value, _) ← IO.ofExcept ((Cached.run fibonacci input 100).mapError reprStr)
    unless value.result.observation == solve fibonacci 12 input do
      throw (IO.userError "memoized/source finite observation differs")
  unless Cached.run fibonacci 40 2 matches .error .budgetExhausted do
    throw (IO.userError "budget exhaustion confused with a source error")
  let schema : LeanPoo.Object.Recursive.Schema := ⟨[("O", [])], fun _ => .identity, slots⟩
  let plan ← IO.ofExcept ((LeanPoo.Object.Recursive.compile schema "O").mapError reprStr)
  let instanceValue ← plan.instantiate
  unless (← instanceValue.cachedKeys).isEmpty do
    throw (IO.userError "instantiation forced a slot")
  let alias := instanceValue
  let first ← IO.ofExcept ((← alias.read 20 "z").mapError reprStr)
  unless first.result.observation == plan.read 3 "z" &&
      (← instanceValue.cachedKeys).length == 3 do
    throw (IO.userError "shared slot cache or final-self result")
  let failure ← IO.ofExcept ((← instanceValue.read 10 "broken").mapError reprStr)
  let failureAgain ← IO.ofExcept ((← alias.read 1 "broken").mapError reprStr)
  unless failure.result == .error "source failure" && failureAgain.result == failure.result do
    throw (IO.userError "completed source errors are not memoized")
  unless (← instanceValue.read 20 "a") matches .error (.cycle ["a", "b", "a"]) do
    throw (IO.userError "mutual initialization cycle lacks its request path")
  match ← instanceValue.readCertified 20 "a" with
  | .error (.cycle path divergent) =>
    have _kernelCycle : Diverges (MutableRecord.generator plan.storage) "a" := divergent
    unless path == ["a", "b", "a"] do throw (IO.userError "certified instance cycle path")
  | _ => throw (IO.userError "instance cycle lacks semantic evidence")
  let fresh ← plan.instantiate
  unless (← fresh.cachedKeys).isEmpty do
    throw (IO.userError "fresh instance reused another mutable cache identity")
  let mutable ← plan.mutable
  let ⟨cycleSnapshot, cycleResult⟩ ← mutable.forceCertified 20 "a"
  match cycleResult with
  | .error (.cycle path divergent) =>
    have _kernelCycle : Diverges (MutableRecord.generator cycleSnapshot.storage) "a" := divergent
    unless path == ["a", "b", "a"] do throw (IO.userError "certified snapshot cycle path")
  | _ => throw (IO.userError "mutable cycle lacks snapshot-bound semantic evidence")
  let frozen ← IO.ofExcept ((← mutable.force 20 "z").mapError reprStr)
  unless frozen.2.result == .value (.list [.integer 1, .integer 2]) &&
      (← mutable.cachedKeys).length == 3 do
    throw (IO.userError "mutable lazy cache")
  mutable.slot "x" (MutableRecord.constant (.integer 99))
  unless (← mutable.cachedKeys).isEmpty && (← mutable.generation) == 1 do
    throw (IO.userError "mutation retained stale memo entries")
  let changed ← IO.ofExcept ((← mutable.force 20 "z").mapError reprStr)
  unless changed.1.generation == 1 && changed.2.result == .value (.list [.integer 99, .integer 2]) &&
      frozen.2.result == .value (.list [.integer 1, .integer 2]) do
    throw (IO.userError "stale final-self result or escaped snapshot changed")
  let concurrent ← plan.instantiate
  let one ← IO.asTask (concurrent.read 20 "z") .dedicated
  let two ← IO.asTask (concurrent.read 20 "z") .dedicated
  let a ← IO.ofExcept one.get
  let b ← IO.ofExcept two.get
  unless a.isOk && b.isOk && (← concurrent.statistics).misses == 3 do
    throw (IO.userError "concurrent aliases computed the same cold slots twice")
  IO.println s!"RECURSIVE-CACHE-OK memoizedInputs={cache.entries.length} sourceParity=11 kernelReceipts=true cyclePath=true cachedErrors=true"

#eval runChecks
#print axioms Cached.Receipt.observed
#print axioms Cached.Receipt.agrees
#print axioms LeanPoo.Object.Recursive.Instance.read_agrees
end LeanPoo.Tests.RecursiveCache
