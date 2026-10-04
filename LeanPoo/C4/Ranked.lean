import LeanPoo.C4.Types

/-! A checked finite rank for the entire inheritance graph. This certificate
concerns parent edges, independently of C4's method-precedence constraints. -/

namespace LeanPoo.C4

/-- Every parent has a smaller rank; graph nodes fit the propagation bound. -/
structure Ranked (graph : Graph) where
  rank : String → Nat
  bounded : ∀ node ∈ graph.nodes, rank node.name < graph.nodes.length
  parentLower : ∀ node ∈ graph.nodes, ∀ parent ∈ node.parentOrders.flatten,
    rank parent < rank node.name

inductive RankError where
  | graph (error : Error)
  | blocked (remaining : List String)
  | invalidRank
  deriving Repr, BEq

/-- Check a proposed rank at every node and parent edge. No assumption about
the scheduler or a successful C4 linearization enters the certificate. -/
def Graph.checkRank (graph : Graph) (rank : String → Nat) :
    Except RankError (Ranked graph) := do
  graph.validate.mapError .graph
  if checked : graph.nodes.all (fun node =>
      decide (rank node.name < graph.nodes.length) &&
      node.parentOrders.flatten.all (fun parent =>
        decide (rank parent < rank node.name))) = true then
    return {
      rank
      bounded := by
        intro node member
        have localCheck := List.all_eq_true.mp checked node member
        exact of_decide_eq_true (Bool.and_eq_true_iff.mp localCheck).1
      parentLower := by
        intro node member parent edge
        have localCheck := List.all_eq_true.mp checked node member
        have edgeChecks := (Bool.and_eq_true_iff.mp localCheck).2
        exact of_decide_eq_true (List.all_eq_true.mp edgeChecks parent edge) }
  else
    throw .invalidRank

/-- A parent-first schedule of all nodes. A blocked remainder contains a
cycle once name/reference validation has succeeded. -/
private def schedule (nodes : List Node) : Except RankError (List String) :=
  go nodes [] {} nodes.length
where
  go (remaining : List Node) (done : List String) (seen : Std.HashSet String) :
      Nat → Except RankError (List String)
    | 0 =>
      if remaining.isEmpty then .ok done.reverse
      else .error (.blocked (remaining.map Node.name))
    | fuel + 1 =>
      if remaining.isEmpty then .ok done.reverse
      else
        match remaining.find? (fun node =>
            node.parentOrders.flatten.all seen.contains) with
        | none => .error (.blocked (remaining.map Node.name))
        | some node => go (remaining.filter (fun other => other.name != node.name))
            (node.name :: done) (seen.insert node.name) fuel

/-- Infer a finite topological rank, then independently check its proof
obligations. This validates the whole schema, including unreachable nodes. -/
def Graph.inferRanked (graph : Graph) : Except RankError (Ranked graph) := do
  graph.validate.mapError .graph
  let order ← schedule graph.nodes
  graph.checkRank order.idxOf

end LeanPoo.C4
