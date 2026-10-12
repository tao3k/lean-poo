import LeanPoo.Prototype.C3CacheCoherence

namespace LeanPoo.Tests.C3CacheCoherence
open LeanPoo.Prototype
open LeanPoo.C4

-- Generic clients need neither a DAG witness nor a successful-result premise.
example (graph : C3.Graph) (roots : List String) :
    C3.linearizeMany graph roots = C3.linearizeUncachedMany graph roots :=
  C3.linearizeMany_eq_uncached graph roots
example (graph : C3.Graph) (root : String) :
    C3.linearize graph root = C3.linearizeUncached graph root :=
  C3.linearize_eq_uncached graph root
example (graph : C3.Graph) (root : String) (cache : C3.Cache)
    (valid : C3.CacheDerivations graph cache) :
    (C3.visit graph root [] cache (graph.length + 1)).map Prod.fst =
      C3.referenceVisit graph root [] (graph.length + 1) :=
  C3.visit_reference_root graph root cache valid
example (derived : C3.GraphDerivation graph root output)
    (cycle : C3.Reaches graph root root) : False := derived.no_cycle cycle
example (graph : C3.Graph) (roots : List String) (orders : List (List String))
    (success : C3.linearizeMany graph roots = .ok orders) : C3.GraphCertificate graph roots :=
  C3.GraphCertificate.of_cached graph roots orders success

private def same [DecidableEq α] (left right : Except Error α) : Bool :=
  match left, right with
  | .ok first, .ok second => decide (first = second)
  | .error first, .error second => decide (first = second)
  | _, _ => false

-- Independent scalar graph validation and cache-free head/tail merge oracle.
private def validate : List String → C3.Graph → Except Error Unit
  | _, [] => .ok ()
  | seen, (name, parents) :: rest =>
    if seen.contains name then .error (.duplicateNode name)
    else if parents.length != parents.eraseDups.length then .error .inconsistentOrder
    else validate (name :: seen) rest

private def merge : Nat → List (List String) → Except Error (List String)
  | 0, lists => if lists.all List.isEmpty then .ok [] else .error .inconsistentOrder
  | fuel + 1, lists => do
    let nonempty := lists.filter (!·.isEmpty)
    if nonempty.isEmpty then return []
    let some chosen := nonempty.findSome? (fun row => do
      let first ← row.head?
      if nonempty.any (fun other => other.tail.contains first) then none else some first) |
        throw .inconsistentOrder
    let rest ← merge fuel (nonempty.map (fun row =>
      if row.head? == some chosen then row.tail else row))
    return chosen :: rest

private def visit (graph : C3.Graph) : Nat → String → List String → Except Error (List String)
  | 0, root, _ => .error (.cycle root)
  | fuel + 1, root, path => do
    if path.contains root then throw (.cycle root)
    let some row := graph.find? (fun row => row.1 == root) | throw (.unknownNode root)
    let orders ← row.2.mapM (fun parent => visit graph fuel parent (root :: path))
    let candidates := orders ++ [row.2]
    return root :: (← merge (candidates.flatten.length + 1) candidates)

private def oracle (graph : C3.Graph) (roots : List String) : Except Error (List (List String)) := do
  validate [] graph
  roots.mapM (fun root => visit graph (graph.length + 1) root [])

private def parentOrders : Nat → List String → List (List String)
  | 0, _ => [[]]
  | fuel + 1, names => [[]] ++ names.flatMap (fun name =>
      (parentOrders fuel (names.filter (· != name))).map (name :: ·))

private def cycle : C3.Graph :=
  [("Leaf", []), ("A", ["Leaf", "B"]), ("B", ["C"]), ("C", ["A"])]
#guard (C3.linearizeMany cycle ["Leaf", "Leaf", "A", "Missing"]) matches .error (.cycle "A")
#guard (C3.linearizeMany cycle ["Leaf", "B"]) matches .error (.cycle "B")
#guard (C3.linearizeMany cycle ["Leaf", "Missing", "A"]) matches .error (.unknownNode "Missing")
#guard (C3.linearizeMany cycle ["Leaf", "Leaf"]) matches .ok [["Leaf"], ["Leaf"]]
#guard (C3.linearizeMany [("A", ["A", "A"])] []) matches .error .inconsistentOrder
#guard (C3.linearizeMany [("A", []), ("A", [])] []) matches .error (.duplicateNode "A")

private def inconsistent : C3.Graph :=
  [("Leaf", []), ("X", []), ("Y", []), ("A", ["X", "Y"]),
    ("B", ["Y", "X"]), ("Z", ["A", "B"]), ("Cycle", ["Cycle"])]
#guard (C3.linearizeMany inconsistent ["Leaf", "A", "B", "Z", "Cycle"]) matches .error .inconsistentOrder
#guard (C3.linearizeMany inconsistent ["Leaf", "Cycle", "Z"]) matches .error (.cycle "Cycle")

-- Forged memo entries cannot satisfy the theorem's derivation invariant.
private def forged : C3.Cache := ({} : C3.Cache).insert "A" ["A"]
example : ¬ C3.CacheDerivations [("A", ["A"])] forged := by
  intro valid
  have derived := valid "A" ["A"] (by simp [forged])
  exact derived.no_cycle (.edge ⟨("A", ["A"]), rfl, by simp⟩)
#guard (C3.visit [("A", ["A"])] "A" [] forged 2).map Prod.fst matches .ok ["A"]
#guard C3.referenceVisit [("A", ["A"])] "A" [] 2 matches .error (.cycle "A")

private def run : IO Unit := do
  IO.println "POOF-C3-CACHE-COHERENCE-START"
  let mut graphs := 0
  let mut batches := 0
  let mut warmReads := 0
  let mut hotReads := 0
  let mut successes := 0
  let mut cycles := 0
  let mut missing := 0
  let mut inconsistentMerges := 0
  -- Every ordered parent list of width <= 2 on all four names; self edges
  -- and mutual cycles remain in the family rather than being filtered out.
  let choices := parentOrders 2 ["Leaf", "A", "B", "C"]
  for a in choices do
    for b in choices do
      for c in choices do
        let graph : C3.Graph := [("Leaf", []), ("A", a), ("B", b), ("C", c)]
        graphs := graphs + 1
        let .ok (_, warm) := C3.visit graph "Leaf" [] {} (graph.length + 1) |
          throw (IO.userError "leaf warmup")
        for root in ["A", "B", "C"] do
          let actual := C3.visit graph root [] warm (graph.length + 1)
          let expected := visit graph (graph.length + 1) root []
          unless same (actual.map Prod.fst) expected &&
              same (C3.referenceVisit graph root [] (graph.length + 1)) expected do
            throw (IO.userError s!"warm cycle/error mismatch: {graph}, {root}")
          warmReads := warmReads + 1
          if let .ok (order, updated) := actual then
            let .ok (again, after) := C3.visit graph root [] updated (graph.length + 1) |
              throw (IO.userError "sound computed root failed on hit")
            unless again == order do throw (IO.userError "cached root changed order")
            for name in ["Leaf", "A", "B", "C"] do
              unless after.get? name == updated.get? name do throw (IO.userError "hot read changed memo table")
            hotReads := hotReads + 1
        for roots in [[], ["Leaf"], ["A"], ["B"], ["C"],
            ["Leaf", "A", "B", "Leaf", "C", "A"], ["Leaf", "A", "Missing", "B"]] do
          let expected := oracle graph roots
          unless same (C3.linearizeMany graph roots) expected && same (C3.linearizeUncachedMany graph roots) expected do
            throw (IO.userError s!"batch cycle/error mismatch: {graph}, {roots}")
          match expected with
          | .ok _ => successes := successes + 1
          | .error (.cycle _) => cycles := cycles + 1
          | .error (.unknownNode _) => missing := missing + 1
          | .error .inconsistentOrder => inconsistentMerges := inconsistentMerges + 1
          | .error _ => throw (IO.userError "validated family produced unrelated error")
          batches := batches + 1
  -- Validation and first-error priorities on inputs beyond the enumerated family.
  for graph in [[], [("A", [])], [("A", ["Missing"])], [("A", []), ("A", [])],
      [("A", ["A", "A"])], cycle, inconsistent] do
    for roots in [[], ["A"], ["Missing", "A"], ["Leaf", "A", "Missing"],
        ["Leaf", "A", "B", "Z", "Cycle"], ["Leaf", "Cycle", "Z"]] do
      let expected := oracle graph roots
      unless same (C3.linearizeMany graph roots) expected && same (C3.linearizeUncachedMany graph roots) expected do
        throw (IO.userError "validation/first-error oracle mismatch")
      batches := batches + 1
  -- Genuine warm values at insufficient fuel or on a fabricated path show why
  -- the internal theorem keeps both its budget and actual-path hypotheses.
  let dag : C3.Graph := [("Root", ["Leaf"]), ("Leaf", [])]
  let .ok (_, warm) := C3.visit dag "Root" [] {} 3 | throw (IO.userError "DAG warmup")
  unless same ((C3.visit dag "Root" [] warm 1).map Prod.fst) (.ok ["Root", "Leaf"]) &&
      same (C3.referenceVisit dag "Root" [] 1) (.error (.cycle "Leaf")) do
    throw (IO.userError "insufficient-budget control lost distinction")
  unless same ((C3.visit dag "Root" ["Leaf"] warm 3).map Prod.fst) (.ok ["Root", "Leaf"]) &&
      same (C3.referenceVisit dag "Root" ["Leaf"] 3) (.error (.cycle "Leaf")) do
    throw (IO.userError "fabricated-path control lost distinction")
  unless graphs == 4913 && batches == 34433 && warmReads == 14739 && hotReads == 2364 &&
      successes == 12417 && cycles == 20795 && missing == 788 && inconsistentMerges == 391 do
    throw (IO.userError "C3 finite family coverage drift")
  IO.println s!"POOF-C3-CACHE-COHERENCE-OK graphs={graphs} batches={batches} warm={warmReads} hot={hotReads} success={successes} cycles={cycles} missing={missing} merge-errors={inconsistentMerges} boundary-controls=3"

#eval run
#print axioms C3.GraphDerivation.no_cycle
#print axioms C3.referenceVisit_complete_active
#print axioms C3.visit_reference_active
#print axioms C3.visit_reference_root
#print axioms C3.linearizeMany_eq_uncached
#print axioms C3.linearize_eq_uncached
#print axioms C3.GraphCertificate.of_cached
end LeanPoo.Tests.C3CacheCoherence
