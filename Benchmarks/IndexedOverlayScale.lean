import LeanPoo.Functional.IndexedOverlay

open LeanPoo.Functional
private def Value (c : Nat) (_ : Nat) := {n : Nat // c ≤ n}
private def base : Provider Nat Nat Value := fun _ => some (fun c => ⟨c + 1, by omega⟩)
private def edits (count width : Nat) : List (CapabilityEdit Nat Nat Value) :=
  (List.range count).map fun step => ⟨step % width,
    if step % 7 == 0 then none else some (fun c => ⟨c + step + 2, by omega⟩)⟩
private def expected (count width key c : Nat) : Option Nat :=
  (List.range count).foldl (fun value step => if step % width == key then
    if step % 7 == 0 then none else some (c + step + 2) else value) (some (c + 1))
private def query (provider : Provider Nat Nat Value) (keys : List Nat) : IO Nat := do
  let mut checksum := 0
  for key in keys do
    for c in [0, 7] do
      match provider key with
      | none => checksum := checksum + 1
      | some factory => checksum := checksum + (factory c).val + 2
  return checksum

def main (args : List String) : IO Unit := do
  let [variant, countText, widthText] := args | throw (IO.userError "variant count width required")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  let some width := widthText.toNat? | throw (IO.userError "invalid width")
  unless count > 0 && width > 0 && (variant == "list" || variant == "indexed") do
    throw (IO.userError "invalid parameters")
  let history := edits count width
  let keys := (List.range (width + 8)) ++ (List.range (width + 8)).reverse
  let begin ← IO.monoNanosNow
  let (provider, stored) := if variant == "indexed" then
    let state := IndexedOverlay.compile base history
    (state.provider, state.overrides.size)
  else
    let state := ProviderOverlay.compile base history
    (state.provider, state.edits.length)
  let constructNs := (← IO.monoNanosNow) - begin
  let startQuery ← IO.monoNanosNow
  let checksum ← query provider keys
  let queryNs := (← IO.monoNanosNow) - startQuery
  -- Independent scalar reference is outside both timed regions.
  let mut oracle := 0
  for key in keys do
    for c in [0, 7] do
      let wanted := expected count width key c
      unless (provider key).map (fun factory => (factory c).val) == wanted do
        throw (IO.userError "per-key oracle mismatch")
      match wanted with
      | none => oracle := oracle + 1
      | some value => oracle := oracle + value + 2
  unless checksum == oracle && stored == min count width do
    throw (IO.userError "semantic or storage mismatch")
  IO.println s!"variant={variant} count={count} width={width} queries={keys.length * 2} stored={stored} checksum={checksum} construct_ns={constructNs} query_ns={queryNs} oracle_parity=true"
