import LeanPoo.Prototype.C3
open LeanPoo.Prototype

private def graph : C3.Graph :=
  [("O",[]),("A",["O"]),("B",["O"]),("C",["O"]),("D",["O"]),("E",["O"]),
   ("K1",["A","B","C"]),("K2",["D","B","E"]),("K3",["D","A"]),("Z",["K1","K2","K3"])]

-- paper:1895
#guard ([Sum.inl [], Sum.inl ["1"], Sum.inl ["a","b","c"], Sum.inr "nil"].map C3.notNull) == [false,true,true,true]
-- paper:1896
#guard C3.removeNulls [["a","b","c"],[],["d","e"],[],["f"],[],[]] == [["a","b","c"],["d","e"],["f"]]
#guard C3.removeNext "a" [["a","b"],["b","a"],[],["a"]] == [["b"],["b","a"]]
-- paper:1897 (the following four assertions)
#guard (C3.linearize graph "O").toOption == some ["O"]
#guard (C3.linearize graph "A").toOption == some ["A","O"]
#guard (C3.linearize graph "K1").toOption == some ["K1","A","B","C","O"]
#guard (C3.linearize graph "Z").toOption == some ["Z","K1","K2","K3","D","A","B","C","E","O"]
#guard (C3.linearize [("A",["B"]),("B",["A"])] "A") matches .error (.cycle _)
#guard (C3.linearize [("A",["missing"])] "A") matches .error (.unknownNode "missing")
#guard (C3.linearize [("A",[]),("A",[])] "A") matches .error (.duplicateNode "A")
#guard (C3.linearize [("A",[]),("B",["A","A"])] "B") matches .error .inconsistentOrder
#guard (C3.linearize [("O",[]),("A",["O"]),("B",["O"]),
  ("X",["A","B"]),("Y",["B","A"]),("Z",["X","Y"])] "Z") matches .error .inconsistentOrder

-- Independent slow C3 merge oracle with scalar head/tail membership.
private def merge : Nat → List (List String) → Option (List String)
  | 0, lists => if lists.all List.isEmpty then some [] else none
  | fuel+1, lists =>
    let nonempty := lists.filter (!·.isEmpty)
    if nonempty.isEmpty then some []
    else do
      let head ← nonempty.findSome? fun row => do
        let head ← row.head?
        if nonempty.any (fun other => other.tail.contains head) then none else some head
      let tail ← merge fuel (nonempty.map (fun row => if row.head? == some head then row.tail else row))
      return head :: tail

private def oracle (graph : C3.Graph) : Nat → String → Option (List String)
  | 0, _ => none
  | fuel+1, root => do
    let row ← graph.find? (fun row => row.1 == root)
    let parents ← row.2.mapM (oracle graph fuel)
    return root :: (← merge (graph.length*graph.length+1) (parents ++ [row.2]))

private def parentOrders : Nat → List String → List (List String)
  | 0, _ => [[]]
  | fuel+1, names => [[]] ++ names.flatMap (fun name =>
      (parentOrders fuel (names.filter (· != name))).map (name :: ·))

private def run : IO Unit := do
  let mut cases := 0
  let mut graphs := 0
  -- All ordered-parent DAGs on four vertices in a fixed topological labeling.
  for one in parentOrders 1 ["0"] do
    for two in parentOrders 2 ["0","1"] do
      for three in parentOrders 3 ["0","1","2"] do
        let nodes : C3.Graph := [("0",[]),("1",one),("2",two),("3",three)]
        graphs := graphs+1
        for root in ["0","1","2","3"] do
          unless (C3.linearize nodes root).toOption == oracle nodes 5 root do
            throw (IO.userError "C3 differs from independent recursive merge")
          cases := cases+1
  unless graphs == 160 && cases == 640 do throw (IO.userError "C3 coverage drift")
  IO.println s!"POOF-C3-OK paperOrders=4 rejectionCases=5 graphs={graphs} oracleComparisons={cases}"
#eval run
