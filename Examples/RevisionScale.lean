import LeanPoo.Object.Resolve

open LeanPoo

private def name (index : Nat) : String := s!"N{index}"

private def schema (count : Nat) : Object.Schema Nat (fun _ => Nat) :=
  { graph := { nodes := (List.range count).map fun index =>
      { name := name index
        parentOrders := if index == 0 then [] else [[name (index - 1)]] } }
    declaration := fun _ => some Object.Declaration.empty }

private def update (declaration : Object.Declaration Nat (fun _ => Nat)) :
    Object.Declaration Nat (fun _ => Nat) :=
  declaration.withValue 0 1

private def benchmark (count rounds : Nat) : IO Unit := do
  let source := schema count
  let root := name (count - 1)
  let .ok plan := Object.compile source root
    | throw (IO.userError "initial C4 plan failed")
  let .ok revisedSchema := source.reviseDeclaration (name 0) update
    | throw (IO.userError "source revision failed")
  let startedCompile ← IO.monoNanosNow
  for _ in [:rounds] do
    let .ok compiled := Object.compile revisedSchema root
      | throw (IO.userError "recompiled C4 plan failed")
    if compiled.precedence.length != count then
      throw (IO.userError "recompiled precedence changed")
  let compileUs := ((← IO.monoNanosNow) - startedCompile) / 1000
  let startedReuse ← IO.monoNanosNow
  for _ in [:rounds] do
    let .ok revised := plan.reviseDeclaration (name 0) update
      | throw (IO.userError "validated plan revision failed")
    if revised.precedence.length != count then
      throw (IO.userError "reused precedence changed")
  let reuseUs := ((← IO.monoNanosNow) - startedReuse) / 1000
  IO.println s!"nodes={count} rounds={rounds} compile_us={compileUs} reuse_us={reuseUs}"

def main : IO Unit := benchmark 64 20
