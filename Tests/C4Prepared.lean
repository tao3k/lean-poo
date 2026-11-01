import LeanPoo.C4.Prepared
import LeanPoo.Object.Resolve

open LeanPoo.C4

example (schema : LeanPoo.Object.Schema String (fun _ => Nat)) (root : String) :
    (LeanPoo.Object.compile schema root).map (·.precedence) = linearize schema.graph root :=
  LeanPoo.Object.compile_precedence schema root

example (graph : Graph) (prepared : Prepared graph) (root : String) :
    prepared.at root = linearize graph root := prepared.at_eq root

example (schema : LeanPoo.Object.Schema String (fun _ => Nat))
    (prepared : Prepared schema.graph) (root : String) :
    LeanPoo.Object.compilePrepared schema prepared root = LeanPoo.Object.compile schema root :=
  LeanPoo.Object.compilePrepared_eq schema prepared root

private def graphs : List Graph := [
  { nodes := [{ name := "A" }, { name := "A" }, { name := "Root" }] },
  { nodes := [{ name := "A" }, { name := "A" },
      { name := "Root", parentOrders := [["A"]] }] },
  { nodes := [{ name := "Root", parentOrders := [["Missing"]] }] },
  { nodes := [{ name := "A", parentOrders := [["Root"]] },
      { name := "Root", parentOrders := [["A"]] }] },
  { nodes := [{ name := "O" }, { name := "A", parentOrders := [["O"]] },
      { name := "B", parentOrders := [["O"]] },
      { name := "Root", parentOrders := [["A", "B"]] }] },
  { nodes := [{ name := "A" }, { name := "B" },
      { name := "X", parentOrders := [["A", "B"]] },
      { name := "Y", parentOrders := [["B", "A"]] },
      { name := "Root", parentOrders := [["X", "Y"]] }] },
  { nodes := [{ name := "A", suffix := true }, { name := "B", suffix := true },
      { name := "Root", parentOrders := [["A", "B"]] }] }]

#eval show IO Unit from do
  for graph in graphs do
    let prepared := prepare graph
    let schema : LeanPoo.Object.Schema String (fun _ => Nat) :=
      { graph, declaration := fun _ => none }
    -- Interleave roots and revisit both successes and errors. Unreachable
    -- duplicate declarations must not reject an otherwise valid root.
    for root in ["Root", "Missing", "A", "Root", "B", "Missing"] do
      unless reprStr (prepared.at root) == reprStr (linearize graph root) do
        throw (IO.userError s!"prepared C4 changed complete result at {root}")
      let planned := (LeanPoo.Object.compilePrepared schema prepared root).map (·.precedence)
      unless reprStr planned == reprStr (linearize graph root) do
        throw (IO.userError s!"prepared object plan changed complete result at {root}")
      let built := (LeanPoo.Object.compile schema root).map (·.precedence)
      unless reprStr built == reprStr (linearize graph root) do
        throw (IO.userError s!"original object owner changed complete result at {root}")
  IO.println "C4-PREPARED-OK 42 complete success/error replays"

-- Ordinary C4 accepts this crossing suffix, while the canonical audit rejects
-- it. Shared preparation must keep the exact ordinary success, not narrow it.
private def crossing : Graph := { nodes := [
  { name := "A" }, { name := "B" },
  { name := "P", parentOrders := [["A", "B"]] },
  { name := "S", parentOrders := [["A"]], suffix := true },
  { name := "Root", parentOrders := [["P", "S"]] }] }
#guard reprStr ((prepare crossing).at "Root") == reprStr (Except.ok ["Root", "P", "B", "S", "A"] : Except Error (List String))
#guard (linearizeAudited crossing "Root").toOption.isNone

example (prepared : Prepared graph) (root : String)
    (result : Except Error (List String)) (bound : result = linearize graph root) :
    (prepared.retain root result bound).at root = result :=
  (prepared.retain root result bound).at_eq root |>.trans bound.symm

-- Reverse declarations and begin with the deepest root: shared ancestors must
-- not depend on topological source order or successful previous root requests.
#eval show IO Unit from do
  for graph in graphs ++ [crossing] do
    for candidate in [graph, { nodes := graph.nodes.reverse }] do
      let prepared := prepare candidate
      for root in ["Root", "A", "B", "Missing", "Root"] do
        unless reprStr (prepared.at root) == reprStr (linearize candidate root) do
          throw (IO.userError s!"shared ancestor result/order changed at {root}")
  IO.println "C4-ANCESTOR-OK 80 reordered/fallback/complete-result replays"

#print axioms Prepared.at_eq
#print axioms LeanPoo.Object.compilePrepared_eq
#print axioms LeanPoo.Object.compile_precedence
#print axioms LeanPoo.Object.Schema.reviseDeclaration_preserves_preparation

-- The hash-scan certificate is independent of any graph/root preparation.
example (success : scanNames nodes seen = .ok complete) :
    (nodes.map Node.name).Nodup := (scanNames_sound success).1

#print axioms scanNames_sound
