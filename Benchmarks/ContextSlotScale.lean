import LeanPoo.Functional.ContextSlot
open LeanPoo.Functional LeanPoo.Functional.Requirements
private def Value (_ _ : Nat) := UInt64
@[noinline] private def payload (work context key : Nat) : UInt64 := Id.run do
  let mut state := UInt64.ofNat (context+key+1)
  for _ in List.range work do
    state := state * 1664525 + 1013904223
  return state
private def scalarPayload (work context key : Nat) : UInt64 :=
  let rec loop : Nat → UInt64 → UInt64
    | 0, state => state
    | count+1, state => loop count (state * 1664525 + 1013904223)
  loop work (UInt64.ofNat (context+key+1))
private def sumValues : {keys : List Nat} → Results Value c keys → UInt64
  | [], _ => 0
  | _ :: _, (head, tail) => UInt64.add head (sumValues tail)
@[noinline] private def uncached {keys : List Nat}
    (ready : Certified (Value := Value) keys (fun _ _ => True)) (context : Nat) : UInt64 :=
  ready.consume (fun _ data _ => sumValues data) context
private def contextAt (mode : String) (i : Nat) :=
  if mode == "hit" then 7 else if mode == "miss" then i%2 else i/8

def main (args : List String) : IO Unit := do
  let [variant, mode, workText, keysText, readsText] := args |
    throw (IO.userError "variant mode work keys reads required")
  let some work := workText.toNat? | throw (IO.userError "invalid work")
  let some count := keysText.toNat? | throw (IO.userError "invalid keys")
  let some reads := readsText.toNat? | throw (IO.userError "invalid reads")
  unless ["uncached", "cached"].contains variant && ["hit", "miss", "blocks"].contains mode &&
      count > 0 && reads > 0 do throw (IO.userError "invalid parameters")
  let keys := List.range count
  let provider : Provider Nat Nat Value := fun key => some (fun c => payload work c key)
  let begin ← IO.monoNanosNow
  let .ok ready := prepareCertified provider keys (fun _ _ => True) (fun _ _ _ => True.intro) |
    throw (IO.userError "preparation failed")
  let (_, warm, _) := (ContextSlot.empty ready).read 7
  let retained ← IO.mkRef (ready, warm)
  let (ready, warm) ← retained.get
  let setupNs := (← IO.monoNanosNow)-begin
  let state ← IO.mkRef (warm, (0 : UInt64), (0 : Nat))
  let start ← IO.monoNanosNow
  for i in List.range reads do
    let (slot, total, hits) ← state.get
    let c := contextAt mode i
    if variant == "cached" then
      let (output, next, hit) := slot.consume (fun _ data _ => sumValues data) c
      state.set (next, total+output, hits+(if hit then 1 else 0))
    else
      state.set (slot, total + uncached ready c, hits)
  let (_, checksum, reused) ← state.get
  let queryNs := (← IO.monoNanosNow)-start
  -- Separate scalar recurrence and key iteration, outside the timed query.
  let mut expected : UInt64 := 0
  let mut previous := 7
  let mut expectedHits := 0
  for i in List.range reads do
    let c := contextAt mode i
    for key in List.range count do expected := expected + scalarPayload work c key
    if previous == c then expectedHits := expectedHits+1
    previous := c
  unless checksum == expected && reused == (if variant == "cached" then expectedHits else 0) do
    throw (IO.userError "scalar checksum/cache policy mismatch")
  IO.println s!"variant={variant} mode={mode} work={work} keys={count} reads={reads} checksum={checksum.toNat} expected_hits={expectedHits} reused={reused} setup_ns={setupNs} query_ns={queryNs} oracle_parity=true"
