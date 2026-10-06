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

private def listUpdates (initial : ProviderRegistry Nat Nat Value)
    (edits : List (String × List (CapabilityEdit Nat Nat Value))) (retain : Bool) :
    Except String (ProviderRegistry Nat Nat Value × Array (ProviderRegistry Nat Nat Value)) := do
  let mut state := initial
  let mut saved := #[]
  for edit in edits do
    if retain then saved := saved.push state
    state ← state.patchBatch edit.1 edit.2
  return (state, saved)
private def indexedUpdates (initial : ProviderRegistry Nat Nat Value)
    (edits : List (String × List (CapabilityEdit Nat Nat Value))) (retain : Bool) :
    Except String (IndexedRegistry Nat Nat Value × Array (IndexedRegistry Nat Nat Value)) := do
  let mut state := IndexedRegistry.ofRegistry initial
  let mut saved := #[]
  for edit in edits do
    if retain then saved := saved.push state
    state ← state.patchBatch edit.1 edit.2
  return (state, saved)

def main (args : List String) : IO Unit := do
  let [variant, countText, widthText, chunkText, policy] := args | throw (IO.userError "variant count width chunk policy required")
  let some count := countText.toNat? | throw (IO.userError "invalid count")
  let some width := widthText.toNat? | throw (IO.userError "invalid width")
  let some chunk := chunkText.toNat? | throw (IO.userError "invalid chunk")
  unless count > 0 && width > 0 && chunk > 0 && count % chunk == 0 &&
      (variant == "list" || variant == "indexed") && (policy == "latest" || policy == "retained") do throw (IO.userError "invalid parameters")
  let edits := changes count width chunk
  let initial := ProviderRegistry.ofNames ["0", "1", "2", "3"] id (fun _ => base)
  let keys := (List.range (width + 8)) ++ (List.range (width + 8)).reverse
  let begin ← IO.monoNanosNow
  let (dictionary, saved) ← if variant == "indexed" then do
    let .ok (state, snapshots) := indexedUpdates initial edits (policy == "retained")
      | throw (IO.userError "indexed batch failed")
    pure (state.dictionary, snapshots.map IndexedRegistry.dictionary)
  else do
    let .ok (state, snapshots) := listUpdates initial edits (policy == "retained")
      | throw (IO.userError "list batch failed")
    pure (state.dictionary, snapshots.map ProviderRegistry.dictionary)
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
  unless saved.size == (if policy == "retained" then edits.length else 0) do
    throw (IO.userError "retained snapshot count mismatch")
  let mut savedChecksum := 0
  for i in [:saved.size] do
    let name := i % 4
    let key := (i * chunk) % width
    let wanted := expected (i * chunk) width chunk name key 7
    let observed := (saved[i]! (toString name) key).map (fun factory => (factory 7).val)
    unless observed == wanted do throw (IO.userError "old snapshot changed")
    savedChecksum := savedChecksum + observed.getD 0

  IO.println s!"variant={variant} policy={policy} retained={saved.size} saved_checksum={savedChecksum} count={count} width={width} chunk={chunk} batches={edits.length} queries={keys.length * 10} checksum={checksum} construct_ns={constructNs} query_ns={queryNs} oracle_parity=true"
