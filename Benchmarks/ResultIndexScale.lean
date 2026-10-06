import LeanPoo.Functional.ResultIndex
open LeanPoo.Functional.Requirements
private def Value (_ _ : Nat) := UInt64
@[noinline] private def built (seed : Nat) : (keys : List Nat) → Results Value 7 keys
  | [] => PUnit.unit
  | key :: rest => (UInt64.ofNat seed + UInt64.ofNat key + 1, built seed rest)
private def queryKey (mode : String) (count : Nat) (positive : 0 < count) (i : Nat) : Fin count :=
  if mode == "head" then ⟨0, positive⟩
  else if mode == "tail" then ⟨count-1, by omega⟩
  else ⟨i % count, Nat.mod_lt _ positive⟩
@[noinline] private def listQuery {keys : List Nat} (data : Results Value 7 keys)
    (key : Nat) (member : key ∈ keys) : UInt64 := resultAt data key member
@[noinline] private def indexedQuery [Hashable Nat] {count : Nat}
    {data : Results Value 7 (List.range count)} (index : ResultIndex data) (key : Fin count) : UInt64 :=
  index.get key.val (List.mem_range.mpr key.isLt)

def main (args : List String) : IO Unit := do
  let [variant, mode, hashing, keysText, readsText, seedText] := args |
    throw (IO.userError "variant mode hashing keys reads seed required")
  let some count := keysText.toNat? | throw (IO.userError "invalid keys")
  let some reads := readsText.toNat? | throw (IO.userError "invalid reads")
  let some seed := seedText.toNat? | throw (IO.userError "invalid seed")
  unless ["list", "indexed"].contains variant && ["head", "tail", "cycle"].contains mode &&
      ["uniform", "collision"].contains hashing && reads > 0 do throw (IO.userError "invalid parameters")
  if positive : 0 < count then do
    let _ : Hashable Nat := ⟨fun key => if hashing == "collision" then 0 else UInt64.ofNat key⟩
    let begin ← IO.monoNanosNow
    let keys := List.range count
    let data := built seed keys
    let table : Option (ResultIndex data) := if variant == "indexed" then some (ResultIndex.ofResults data) else none
    let retained ← IO.mkRef (data, table)
    let (data, table) ← retained.get
    let setupNs := (← IO.monoNanosNow)-begin
    let state ← IO.mkRef (0 : UInt64)
    let start ← IO.monoNanosNow
    for i in List.range reads do
      let key := queryKey mode count positive i
      let total ← state.get
      let value := match table with
        | none => listQuery (keys := keys) data key.val (List.mem_range.mpr key.isLt)
        | some index => indexedQuery index key
      state.set (total+value)
    let checksum ← state.get
    let queryNs := (← IO.monoNanosNow)-start
    -- Independent Nat scalar calculation and mode schedule after timing.
    let mut expected : UInt64 := 0
    for i in List.range reads do
      let key := if mode == "head" then 0 else if mode == "tail" then count-1 else i % count
      expected := expected + UInt64.ofNat (seed+key+1)
    unless checksum == expected do throw (IO.userError "independent checksum mismatch")
    IO.println s!"variant={variant} mode={mode} hashing={hashing} keys={count} reads={reads} seed={seed} checksum={checksum.toNat} setup_ns={setupNs} query_ns={queryNs} oracle_parity=true"
  else throw (IO.userError "keys must be positive")
