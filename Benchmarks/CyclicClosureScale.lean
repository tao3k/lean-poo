import LeanPoo.Functional.IncrementalClosure
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

def main (args : List String) : IO Unit := do
  let [variant,family,size] := args | throw (IO.userError "variant family size")
  let some n := size.toNat? | throw (IO.userError "size")
  unless n > 0 && ["reference","worklist","retained-index"].contains variant &&
      ["chain","reverse","fanout","shared","ring","quorum"].contains family do throw (IO.userError "parameters")
  let setupBegin ← IO.monoNanosNow
  let prepared ← if variant == "retained-index" then
      IO.mkRef (some (IncrementalClosure.compile (workload family n)))
    else IO.mkRef none
  let retained ← prepared.get
  let setupNs := (← IO.monoNanosNow)-setupBegin
  let begin ← IO.monoNanosNow
  let (facts,counts) ← if variant == "reference" then do
      let result := PositiveEquations.close (workload family n)
      let forced ← IO.mkRef (Vector.ofFn result.value, (none : Option IncrementalClosure.Stats))
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
