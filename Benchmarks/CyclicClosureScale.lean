import LeanPoo.Functional.IncrementalClosure
import LeanPoo.Functional.StrongComponents
open LeanPoo LeanPoo.Functional LeanPoo.Functional.PositiveEquations

/-- Parameterized families all have the independent oracle 'every fact is true'. -/
def workload (family : String) (n : Nat) : Equations n := fun index =>
  if family == "reverse" then
    if last : index.val+1 = n then .literal true else .read ⟨index.val+1,by omega⟩
  else if family == "fanout" then
    if index.val = 0 then .literal true else .read ⟨0,by have := index.isLt; omega⟩
  else if zero : index.val = 0 then
    if family == "ring" then .either (.literal true) (.read ⟨n-1,by have := index.isLt; omega⟩) else .literal true
  else
    let previous : Fin n := ⟨index.val-1,by omega⟩
    if family == "shared" then .both (.read previous) (.read previous)
    else if family == "quorum" then
      Expr.twoOfThree (.read previous) (.read previous) (.read ⟨0,by have := index.isLt; omega⟩)
    else .read previous

/-- Force the complete reachability matrix for two disjoint cycles. Cross-group
negatives exercise the expensive shared-search case; every cell has an independent
partition oracle. Both controls include matrix allocation in the query timer. -/
def measurePaths (variant family : String) (n : Nat) : IO Unit := do
  unless n ≥ 2 && n%2 == 0 && ["ring","shared"].contains family do
    throw (IO.userError "path controls require an even size and ring/shared family")
  let width := n/2
  let edge : Fin n → Fin n → Bool := fun a b =>
    decide (a.val/width = b.val/width) &&
      (decide ((a.val+1)%width = b.val%width) ||
        (family == "shared" && decide ((a.val+2)%width = b.val%width)))
  let begin ← IO.monoNanosNow
  let table := if variant == "paths-unshared" then
      Vector.ofFn (fun a => Vector.ofFn (fun b => StrongComponents.reachable edge n a b))
    else if variant == "paths-layered" then StrongComponents.reachableLayers edge n
    else StrongComponents.reachableTable edge n
  let forced ← IO.mkRef table
  let facts ← forced.get
  let queryNs := (← IO.monoNanosNow)-begin
  for a in List.finRange n do
    for b in List.finRange n do
      unless facts[a.val][b.val] == decide (a.val/width = b.val/width) do
        throw (IO.userError "independent path partition oracle")
  IO.println s!"variant={variant} family={family} n={n} query_ns={queryNs} oracle_parity=true"

/-- Force every result before stopping the query timer and check a scalar oracle.
The unshared control is for measurement, not a supported compatibility path. -/
def main (args : List String) : IO Unit := do
  let [variant,family,size] := args | throw (IO.userError "variant family size")
  let some n := size.toNat? | throw (IO.userError "size")
  unless n > 0 && ["reference","unshared","paths","paths-unshared","paths-layered","paths-paired","worklist","retained-index"].contains variant &&
      ["chain","reverse","fanout","shared","ring","quorum"].contains family do throw (IO.userError "parameters")
  if variant == "paths-paired" then
    -- Share process startup, not computed matrices. Reverse order balances the
    -- selector against both lightweight and layered controls under natural GC.
    for round in List.range 3 do
      for selected in ["paths-unshared","paths","paths-layered","paths-layered","paths","paths-unshared"] do
        IO.print s!"round={round} "
        measurePaths selected family n
    return
  if ["paths","paths-unshared","paths-layered"].contains variant then
    return ← measurePaths variant family n
  let setupBegin ← IO.monoNanosNow
  let prepared ← if variant == "retained-index" then
      IO.mkRef (some (IncrementalClosure.compile (workload family n)))
    else IO.mkRef none
  let retained ← prepared.get
  let setupNs := (← IO.monoNanosNow)-setupBegin
  let begin ← IO.monoNanosNow
  let (facts,counts) ← if variant == "reference" || variant == "unshared" then do
      let values := if variant == "unshared" then
          Vector.ofFn (Prototype.FiniteClosure.close (system (workload family n))).value
        else Vector.ofFn (PositiveEquations.close (workload family n)).value
      let forced ← IO.mkRef (values, (none : Option IncrementalClosure.Stats))
      forced.get
    else do
      let plan := match retained with | some plan => plan | none => IncrementalClosure.compile (workload family n)
      let result := IncrementalClosure.fastClose plan
      let forced ← IO.mkRef (result.store,some result.stats)
      forced.get
  let queryNs := (← IO.monoNanosNow)-begin
  let checksum := facts.toArray.foldl (fun sum bit => sum+if bit then 1 else 0) 0
  unless checksum == n do throw (IO.userError "independent scalar oracle")
  let stats := counts.getD {}
  IO.println s!"variant={variant} family={family} n={n} setup_ns={setupNs} query_ns={queryNs} checksum={checksum} pops={stats.pops} evals={stats.evaluations} nodes={stats.nodes} writes={stats.writes} pushes={stats.pushes} oracle_parity=true"
