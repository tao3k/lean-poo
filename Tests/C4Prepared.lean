import LeanPoo.C4.Prepared

open LeanPoo.C4

example (graph : Graph) (prepared : Prepared graph) (root : String) :
    prepared.at root = linearize graph root := prepared.at_eq root

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
    -- Interleave roots and revisit both successes and errors. Unreachable
    -- duplicate declarations must not reject an otherwise valid root.
    for root in ["Root", "Missing", "A", "Root", "B", "Missing"] do
      unless reprStr (prepared.at root) == reprStr (linearize graph root) do
        throw (IO.userError s!"prepared C4 changed complete result at {root}")
  IO.println "C4-PREPARED-OK 42 complete success/error replays"

#print axioms Prepared.at_eq
