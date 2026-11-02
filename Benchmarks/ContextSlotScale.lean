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

private def scalarMain (args : List String) : IO Unit := do
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

-- Structural contexts exercise retained identity, equal independent values and
-- true replacement without changing the original scalar workload/CLI.
private def StructuralValue (_ : List Nat) (_ : Unit) := UInt64
@[noinline] private def structuralPayload (context : List Nat) : UInt64 :=
  context.foldl (fun total n => total + UInt64.ofNat n) 0
@[noinline] private def copyContext (context : List Nat) : List Nat :=
  (context.foldl (fun reversed n => n :: reversed) []).reverse

@[noinline] private def structuralReads
    (ready : Certified (Value := StructuralValue) [()] (fun _ _ => True))
    (base equal changed : List Nat) (mode : String) (reads : Nat) : IO (UInt64 × Nat) := do
  let (_, warm, _) := (ContextSlot.empty ready).read base
  let state ← IO.mkRef (warm, (0 : UInt64), (0 : Nat))
  for i in List.range reads do
    let (slot, total, hits) ← state.get
    let context := if mode == "same" then base else if mode == "equal" then equal
      else if i % 2 == 0 then changed else base
    let (value, next, hit) := slot.consume (fun _ data _ => data.1) context
    state.set (next, UInt64.add total value, hits + if hit then 1 else 0)
  let (_, total, hits) ← state.get
  return (total, hits)

private def structuralMain (args : List String) : IO Unit := do
  let [mode, sizeText, readsText] := args | throw (IO.userError "structural mode size reads required")
  let some size := sizeText.toNat? | throw (IO.userError "invalid size")
  let some reads := readsText.toNat? | throw (IO.userError "invalid reads")
  unless ["same", "equal", "miss"].contains mode && size > 0 && reads > 0 do
    throw (IO.userError "invalid structural parameters")
  let base := List.range size
  let equal := copyContext base
  let changed := size :: base
  unless base == equal && !(base == changed) do throw (IO.userError "structural controls invalid")
  let ready : Certified (Value := StructuralValue) [()] (fun _ _ => True) :=
    ⟨(structuralPayload, PUnit.unit), fun _ => True.intro⟩
  let baseSum := UInt64.ofNat (size * (size - 1) / 2)
  let expected := baseSum * UInt64.ofNat reads +
    if mode == "miss" then UInt64.ofNat (size * ((reads + 1) / 2)) else 0
  let expectedHits := if mode == "miss" then 0 else reads
  let warm ← structuralReads ready base equal changed mode reads
  unless warm == (expected, expectedHits) do throw (IO.userError "structural warmup mismatch")
  let mut elapsed := #[]
  for _ in List.range 3 do
    let start ← IO.monoNanosNow
    let result ← structuralReads ready base equal changed mode reads
    let duration := (← IO.monoNanosNow) - start
    unless result == (expected, expectedHits) do throw (IO.userError "structural scalar/reuse mismatch")
    elapsed := elapsed.push duration
  for sample in List.range elapsed.size do
    IO.println s!"measurement: poo.context.structural.{mode}.sample{sample+1} {elapsed[sample]!} ns"
  IO.println s!"CONTEXT-STRUCTURAL-OK mode={mode} size={size} reads={reads} warmup=1 samples=3 checksum={expected.toNat} hits={expectedHits}"

-- Independent uncached floor for the same alternating structural factory work.
-- Existing structural reads, parameters and recorded samples remain unchanged.
@[noinline] private def referenceStructuralReads
    (ready : Certified (Value := StructuralValue) [()] (fun _ _ => True))
    (base changed : List Nat) (reads : Nat) : IO (UInt64 × UInt64) := do
  let warm := ready.consume (fun _ data _ => data.1) base
  let state ← IO.mkRef (warm, (0 : UInt64))
  for i in List.range reads do
    let (warm, total) ← state.get
    let context := if i % 2 == 0 then changed else base
    let output := ready.consume (fun _ data _ => data.1) context
    state.set (warm, UInt64.add total output)
  state.get

private def structuralReferenceMain (args : List String) : IO Unit := do
  let [sizeText, readsText] := args | throw (IO.userError "reference size reads required")
  let some size := sizeText.toNat? | throw (IO.userError "invalid size")
  let some reads := readsText.toNat? | throw (IO.userError "invalid reads")
  unless size > 0 && reads > 0 do throw (IO.userError "invalid reference parameters")
  let base := List.range size
  let changed := size :: base
  let ready : Certified (Value := StructuralValue) [()] (fun _ _ => True) :=
    ⟨(structuralPayload, PUnit.unit), fun _ => True.intro⟩
  let baseSum := UInt64.ofNat (size * (size - 1) / 2)
  let expected := baseSum * UInt64.ofNat reads + UInt64.ofNat (size * ((reads + 1) / 2))
  let check := fun result => result == (baseSum, expected)
  unless check (← referenceStructuralReads ready base changed reads) do
    throw (IO.userError "uncached structural warmup mismatch")
  let mut elapsed := #[]
  for _ in List.range 3 do
    let start ← IO.monoNanosNow
    let result ← referenceStructuralReads ready base changed reads
    let duration := (← IO.monoNanosNow) - start
    unless check result do throw (IO.userError "uncached structural scalar mismatch")
    elapsed := elapsed.push duration
  for sample in List.range elapsed.size do
    IO.println s!"measurement: poo.context.structural-reference.miss.sample{sample+1} {elapsed[sample]!} ns"
  IO.println s!"CONTEXT-STRUCTURAL-REFERENCE-OK size={size} reads={reads} warmup=1 samples=3 checksum={expected.toNat} hits=0"

def main (args : List String) : IO Unit :=
  match args with
  | "structural" :: rest => structuralMain rest
  | "structural-reference" :: rest => structuralReferenceMain rest
  | _ => scalarMain args
