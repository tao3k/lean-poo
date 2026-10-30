import LeanPoo.Object.Dataflow
import Lean

/-! The fixed shape cohort matches MemoizedShapeScale: every observation includes
fresh C4 validation, preparation, all field reads, inventory and negative lookup.
This is an algorithm study; application workload and process gates stay separate. -/
namespace DataflowShapeScale
open LeanPoo LeanPoo.Object.Dataflow
private abbrev Object := Instance Nat (fun _ => Nat)
private abbrev Ready := Template Nat (fun _ => Nat)

private def declaration (width : Nat) : Declaration Nat (fun _ => Nat) :=
  Builder.build do
    for key in List.range width do
      if key == 0 then Builder.value key 1
      else Builder.derived key ((· + 1) <$> Expr.need (key - 1))

@[noinline] private def topology (width depth : Nat) : Source Nat (fun _ => Nat) × String := Id.run do
  let direct := declaration width
  let mut source : Source Nat (fun _ => Nat) := Source.empty.add {name := "Layer0"} direct
  let mut root := "Layer0"
  for layer in List.range (depth - 1) do
    let name := s!"Layer{layer + 1}"
    source := source.add {name,parentOrders := [[root]]} direct
    root := name
  return (source,root)

@[noinline] private def consume (ready : Ready) (width salt : Nat) : Except String Nat :=
  match ready.build with
  | .error error => .error s!"{repr error}"
  | .ok (object,evaluated) => do
    -- These are the actual materializer's work records, not declared counters.
    unless evaluated.length == width && evaluated.eraseDups.length == width do
      throw "resolver execution was not exactly once per declared field"
    let expectedNames := List.range width
    let mut checksum := 0
    for index in List.range width do
      let names := object.slotNames
      unless names == expectedNames do throw "changed declaration inventory/order"
      let key := (index + salt) % width
      let some value := object.read key | throw "missing declared value"
      unless value == key + 1 do throw "changed closed self/inherited value"
      checksum := checksum + value + names.length
    unless (object.read width).isNone do throw "unknown key acquired a value"
    return checksum

private def run (axis : String) (width depth instances sample : Nat) : IO Unit := do
  let allStarted ← IO.monoNanosNow
  let allocations ← IO.getNumHeartbeats
  let started ← IO.monoNanosNow
  let (source,root) := topology width depth
  let topologyNs := (← IO.monoNanosNow) - started
  let topologyAlloc := (← IO.getNumHeartbeats) - allocations
  let allocations ← IO.getNumHeartbeats
  let started ← IO.monoNanosNow
  match Template.prepare source root with
  | .error error => throw (IO.userError s!"{repr error}")
  | .ok ready => do
    let prepareNs := (← IO.monoNanosNow) - started
    let prepareAlloc := (← IO.getNumHeartbeats) - allocations
    let allocations ← IO.getNumHeartbeats
    let started ← IO.monoNanosNow
    let mut checksum := 0
    for iteration in List.range instances do
      checksum := checksum + (← IO.ofExcept (consume ready width iteration))
    let instancesNs := (← IO.monoNanosNow) - started
    let instancesAlloc := (← IO.getNumHeartbeats) - allocations
    let expected := instances * (width * (width + 1) / 2 + width * width)
    unless checksum == expected do throw (IO.userError "incomplete instance/field workload")
    let totalNs := (← IO.monoNanosNow) - allStarted
    unless topologyNs + prepareNs + instancesNs ≤ totalNs do
      throw (IO.userError "overlapping algorithm lifecycle observations")
    IO.println s!"POO-ALGORITHM-SCALE axis={axis} width={width} depth={depth} instances={instances} sample={sample} mode=materialized-dataflow topology_ns={topologyNs} prepare_ns={prepareNs} instances_ns={instancesNs} total_ns={totalNs} topology_small_alloc={topologyAlloc} prepare_small_alloc={prepareAlloc} instances_small_alloc={instancesAlloc} checksum={checksum}"

def runAll : IO Unit := do
  let points := [("width",8,8,128), ("width",32,8,128), ("width",128,8,128),
    ("depth",8,8,128), ("depth",8,32,128), ("depth",8,128,128),
    ("instances",8,8,8), ("instances",8,8,32), ("instances",8,8,128)]
  for (axis,width,depth,instances) in points do
    for sample in [1,2,3] do run axis width depth instances sample
  IO.println "POO-ALGORITHM-SCALE-OK 27 complete materialized observations; application gates unchanged"
end DataflowShapeScale

def main : IO Unit := DataflowShapeScale.runAll
