import LeanPoo.Prototype.Mutable

open LeanPoo

private def basePlan (count : Nat) : Except C4.Error
    (Object.Plan Nat (fun _ => Nat)) := do
  let entries : Std.DHashMap Nat (fun _ => Nat) :=
    (List.range count).foldl (fun table key => table.insert key key) {}
  let declaration := Object.Declaration.fromMap entries (· <= ·)
  let schema : Object.Schema Nat (fun _ => Nat) :=
    { graph := { nodes := [{ name := "Base" }] }
      declaration := fun name =>
        if name == "Base" then some declaration else none }
  Object.compile schema "Base"

private def layers (count : Nat) : Prototype.MutableProto Nat (fun _ => Nat) :=
  Prototype.MutableProto.composeAll <|
    (List.range count).reverse.map fun index =>
      Prototype.MutableProto.slot s!"Layer{index}" 0
        (.computed fun _ inherited => (inherited ()).map (· + 1))

private def sample (batched : Bool) (source : Object.Memoized Nat (fun _ => Nat))
    (prototype : Prototype.MutableProto Nat (fun _ => Nat))
    (rounds layerCount : Nat) : IO Unit := do
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:rounds] do
    let object ← if batched then
      match ← prototype.instantiate source with
      | .ok object => pure object
      | .error _ => throw (IO.userError "batched composition failed")
    else
      let object ← Object.Mutable.new source
      match ← prototype.apply object with
      | .ok () => pure object
      | .error _ => throw (IO.userError "sequential composition failed")
    checksum := checksum + (← object.read 0).getD 0
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  unless checksum == rounds * layerCount do
    throw (IO.userError "composition changed its result")
  IO.println s!"batched={batched} rounds={rounds} layers={layerCount} elapsed_us={elapsedUs} checksum={checksum}"

/-- The previous private path validated C4 after each standard layer, then
allocated only the final object. Keep that cost isolated from cell updates. -/
private def samplePerLayerC4 (source : Object.Memoized Nat (fun _ => Nat))
    (rounds layerCount : Nat) : IO Unit := do
  let started ← IO.monoNanosNow
  let mut checksum := 0
  for _ in [:rounds] do
    let mut plan := source.plan
    for index in [:layerCount] do
      let declaration := Object.Declaration.empty.withSlot 0
        (.computed fun _ inherited => (inherited ()).map (· + 1))
      match LeanPoo.extend plan.schema s!"Layer{index}" plan.root declaration with
      | .ok next => plan := next
      | .error _ => throw (IO.userError "per-layer C4 failed")
    let object ← Object.Mutable.new (source.rebuild plan)
    checksum := checksum + (← object.read 0).getD 0
  let elapsedUs := ((← IO.monoNanosNow) - started) / 1000
  unless checksum == rounds * layerCount do
    throw (IO.userError "per-layer C4 changed its result")
  IO.println s!"per_layer_c4=true rounds={rounds} layers={layerCount} elapsed_us={elapsedUs} checksum={checksum}"

def main : IO Unit := do
  let .ok plan := basePlan 128 | throw (IO.userError "C4 plan failed")
  let source := plan.memoize
  let prototype := layers 12
  sample false source prototype 5 12
  samplePerLayerC4 source 5 12
  sample true source prototype 5 12
