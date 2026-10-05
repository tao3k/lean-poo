import LeanPoo.Functional.IndexedRegistry
open LeanPoo.Functional
private def Value (c : Nat) (_ : Nat) := {n : Nat // c ≤ n}
private def base : Provider Nat Nat Value := fun _ => some (fun c => ⟨c + 1, by omega⟩)
private def changes (count width chunk : Nat) : List (String × List (CapabilityEdit Nat Nat Value)) :=
  (List.range (count / chunk)).map fun batch => (toString (batch % 4),
    (List.range chunk).map fun offset =>
      let step := batch * chunk + offset
      ⟨step % width, if step % 7 == 0 then none else some (fun c => ⟨c + step + 2, by omega⟩)⟩)
private def expected (count width chunk name key c : Nat) : Option Nat :=
  if name == 4 then none else
  (List.range count).foldl (fun value step =>
    if step % width == key && step / chunk % 4 == name then
      if step % 7 == 0 then none else some (c + step + 2) else value) (some (c + 1))
private def query (dictionary : String → Provider Nat Nat Value) (keys : List Nat) : IO Nat := do
  let mut checksum := 0
  for name in List.range 5 do
    for key in keys do
      for c in [0, 7] do
        match dictionary (toString name) key with
        | none => checksum := checksum + 1
        | some factory => checksum := checksum + (factory c).val + 2
  return checksum

def main (args : List String) : IO Unit := do
  let [variant, countText, widthText, chunkText] := args | throw (IO.userError "variant count width chunk required")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  let some width := widthText.toNat? | throw (IO.userError "invalid width")
  let some chunk := chunkText.toNat? | throw (IO.userError "invalid chunk")
  unless count > 0 && width > 0 && chunk > 0 && count % chunk == 0 &&
      (variant == "list" || variant == "indexed") do throw (IO.userError "invalid parameters")
  let edits := changes count width chunk
  let initial := ProviderRegistry.ofNames ["0", "1", "2", "3"] id (fun _ => base)
  let keys := (List.range (width + 8)) ++ (List.range (width + 8)).reverse
  let begin ← IO.monoNanosNow
  let dictionary ← if variant == "indexed" then do
    let .ok state := edits.foldlM (fun state edit => state.patchBatch edit.1 edit.2)
      (IndexedRegistry.ofRegistry initial) | throw (IO.userError "indexed batch failed")
    pure state.dictionary
  else do
    let .ok state := edits.foldlM (fun state edit => state.patchBatch edit.1 edit.2) initial
      | throw (IO.userError "list batch failed")
    pure state.dictionary
  let constructNs := (← IO.monoNanosNow) - begin
  let startQuery ← IO.monoNanosNow
  let checksum ← query dictionary keys
  let queryNs := (← IO.monoNanosNow) - startQuery
  let mut oracle := 0
  for name in List.range 5 do
    for key in keys do
      for c in [0, 7] do
        let wanted := expected count width chunk name key c
        unless (dictionary (toString name) key).map (fun factory => (factory c).val) == wanted do
          throw (IO.userError "per-name/key oracle mismatch")
        match wanted with
        | none => oracle := oracle + 1
        | some value => oracle := oracle + value + 2
  unless checksum == oracle do throw (IO.userError "checksum mismatch")
  IO.println s!"variant={variant} count={count} width={width} chunk={chunk} batches={edits.length} queries={keys.length * 10} checksum={checksum} construct_ns={constructNs} query_ns={queryNs} oracle_parity=true"
