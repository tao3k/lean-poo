import LeanPoo.Object.Definition
import Lean

/-! Separate algorithm study. The existing application workloads remain unchanged.
Topology is rebuilt and validated for every variant; compilation is included in
its measured lifecycle. Reflection and effective-method reuse are separate modes. -/
namespace LegacyThunkShapeScale
open LeanPoo LeanPoo.Object

private abbrev Object := Memoized Nat (fun _ => Nat)
private abbrev Shape := CompiledPlan Nat (fun _ => Nat)

private def declaration (width : Nat) : Declaration Nat (fun _ => Nat) :=
  Declaration.build do
    for key in List.range width do
      if key == 0 then Declaration.Builder.value key 1
      else Declaration.Builder.slot key (.self fun self => (self (key - 1)).map (· + 1))

@[noinline] private def topology (width depth : Nat) : Except String (Plan Nat (fun _ => Nat)) := do
  if width == 0 || depth == 0 then throw "empty scale input"
  let direct := declaration width
  let mut schema : Schema Nat (fun _ => Nat) := {
    graph := { nodes := [{ name := "Layer0" }] }
    declaration := fun name => if name == "Layer0" then some direct else none }
  let mut root := "Layer0"
  for layer in List.range (depth - 1) do
    let name := s!"Layer{layer + 1}"
    schema ← (LeanPoo.extendSchema schema name root direct).mapError (fun error => s!"{repr error}")
    root := name
  (Object.compile schema root).mapError (fun error => s!"{repr error}")

private inductive Mode where
  | canonical | layout | shared
  deriving BEq

private def Mode.label : Mode → String
  | .canonical => "canonical-recompute"
  | .layout => "canonical-layout"
  | .shared => "compiled-layout"

/-- Opaque at callers: force every field and inventory before returning. Rotate
lookup order across objects and check both inherited self dependencies and misses. -/
@[noinline] private def consume (plan : Plan Nat (fun _ => Nat)) (shape : Option Shape)
    (mode : Mode) (width salt : Nat) : Except String Nat := do
  let object : Object := match shape with
    | none => plan.memoize
    | some ready => ready.instantiate
  let expectedNames := List.range width
  let storedNames := LeanPoo.allSlots object.plan
  let mut checksum := 0
  for index in List.range width do
    let names := if mode == .canonical then LeanPoo.allSlots object.plan else storedNames
    unless names == expectedNames do throw "changed declaration inventory/order"
    let key := (index + salt) % width
    let some value := object.read key | throw "missing declared value"
    unless value == key + 1 do throw "changed closed self/inherited value"
    checksum := checksum + value + names.length
  unless (object.read width).isNone do throw "unknown key acquired a value"
  return checksum

private def run (axis : String) (width depth instances sample : Nat) (mode : Mode) : IO Unit := do
  let allStarted ← IO.monoNanosNow
  let allocations ← IO.getNumHeartbeats
  let started ← IO.monoNanosNow
  let plan ← IO.ofExcept (topology width depth)
  let topologyNs := (← IO.monoNanosNow) - started
  let topologyAlloc := (← IO.getNumHeartbeats) - allocations
  let allocations ← IO.getNumHeartbeats
  let started ← IO.monoNanosNow
  let shape := if mode == .shared then some plan.compileMemo else none
  match shape with
  | some ready =>
    unless ready.effective.size == width do throw (IO.userError "incomplete method compilation")
  | none => pure ()
  let prepareNs := (← IO.monoNanosNow) - started
  let prepareAlloc := (← IO.getNumHeartbeats) - allocations
  let allocations ← IO.getNumHeartbeats
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for iteration in List.range instances do
    checksum := checksum + (← IO.ofExcept (consume plan shape mode width iteration))
  let instancesNs := (← IO.monoNanosNow) - started
  let instancesAlloc := (← IO.getNumHeartbeats) - allocations
  let expected := instances * (width * (width + 1) / 2 + width * width)
  unless checksum == expected do throw (IO.userError "incomplete instance/field workload")
  let totalNs := (← IO.monoNanosNow) - allStarted
  unless topologyNs + prepareNs + instancesNs ≤ totalNs do
    throw (IO.userError "overlapping algorithm lifecycle observations")
  IO.println s!"POO-ALGORITHM-SCALE axis={axis} width={width} depth={depth} instances={instances} sample={sample} mode={mode.label} topology_ns={topologyNs} prepare_ns={prepareNs} instances_ns={instancesNs} total_ns={totalNs} topology_small_alloc={topologyAlloc} prepare_small_alloc={prepareAlloc} instances_small_alloc={instancesAlloc} checksum={checksum}"

def runAll : IO Unit := do
  let points := [("width",8,8,128), ("width",32,8,128), ("width",128,8,128),
    ("depth",8,8,128), ("depth",8,32,128), ("depth",8,128,128),
    ("instances",8,8,8), ("instances",8,8,32), ("instances",8,8,128)]
  for (axis,width,depth,instances) in points do
    for sample in [1,2,3] do
      run axis width depth instances sample .shared
  IO.println "POO-ALGORITHM-SCALE-OK 27 complete compiled-thunk observations; original application gates unchanged"
end LegacyThunkShapeScale

def main : IO Unit := LegacyThunkShapeScale.runAll
