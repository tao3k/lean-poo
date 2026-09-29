import LeanPoo.Object.Schema

open LeanPoo

private def name (index : Nat) : String := s!"Family{index}"

private def family (index : Nat) : Object.Schema Nat (fun _ => Nat) :=
  { graph := { nodes := [{ name := name index }] }
    declaration := fun query =>
      if query == name index then
        some (Object.Declaration.empty.withDefault 0 index)
      else none }

private def repeated (first : Object.Schema Nat (fun _ => Nat))
    (others : List (Object.Schema Nat (fun _ => Nat))) :
    Except Object.SchemaMergeError (Object.Schema Nat (fun _ => Nat)) :=
  others.foldlM Object.Schema.mergeDisjoint first

private def checksum (count : Nat)
    (schema : Object.Schema Nat (fun _ => Nat)) : Nat :=
  (List.range count).foldl (fun total index =>
    total + ((schema.declaration (name index)).bind (·.default 0)).getD 0) 0

private def benchmark (count : Nat) : IO Unit := do
  let first := family 0
  let others := (List.range (count - 1)).map (fun index => family (index + 1))
  let startedRepeated ← IO.monoNanosNow
  let .ok old := repeated first others
    | throw (IO.userError "repeated merge failed")
  let oldCount := old.graph.nodes.length
  let oldSum := checksum count old
  let repeatedUs := ((← IO.monoNanosNow) - startedRepeated) / 1000
  let startedOnePass ← IO.monoNanosNow
  let .ok merged := first.mergeDisjointMany others
    | throw (IO.userError "one-pass merge failed")
  let mergedCount := merged.graph.nodes.length
  let mergedSum := checksum count merged
  let onePassUs := ((← IO.monoNanosNow) - startedOnePass) / 1000
  if oldCount != count || mergedCount != count ||
      oldSum != mergedSum || mergedSum != count * (count - 1) / 2 then
    throw (IO.userError "schema merge results differ")
  IO.println s!"families={count} checksum={mergedSum} repeated_us={repeatedUs} one_pass_us={onePassUs}"

def main : IO Unit := do
  benchmark 100
  benchmark 300
  benchmark 600
