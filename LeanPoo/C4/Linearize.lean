import Std
import LeanPoo.C4.Merge

/-!
C4 metadata algorithm translated from François-René Rideau's C4-Mixins,
include/c4/linearize.hpp.
Upstream offers Apache-2.0 or No Problem Bugroff; this translation uses Apache-2.0.
-/

namespace LeanPoo.C4

private abbrev Table := Std.HashMap String Linearization

private def lookup (table : Table) (name : String) : Option Linearization :=
  table.get? name

private def parents (node : Node) : List String :=
  unique node.parentOrders.flatten

private def withoutTail (items tail : List String) : List String :=
  items.filter (fun item => !tail.contains item)

/-- Local suffix members must form an ordered subsequence of the inherited
tail, with no non-suffix member between them. -/
private def respectsSuffixTail (order tail : List String) : Bool :=
  let suffix := order.dropWhile (fun item => !tail.contains item)
  suffix.all tail.contains &&
    tail.filter (fun item => suffix.contains item) == suffix

/-- Walk the already computed inherited-suffix chain. -/
private def suffixReaches (table : Table) (source target : String) : Bool :=
  let (_, found) := (List.range (table.size + 1)).foldl
    (fun (current, found) _ =>
      if found then (current, true)
      else match current with
        | none => (none, false)
        | some name =>
          if name == target then (current, true)
          else ((lookup table name).bind Linearization.inheritedSuffix, false))
    (some source, false)
  found

/-- Compute one node after all its parents have been computed. -/
private def computeNode (table : Table) (node : Node) :
    Except Error Linearization := do
  let orders := node.parentOrders.filter (fun order => !order.isEmpty)
  let mut parentResultsRev : List Linearization := []
  for parent in parents node do
    let some result := lookup table parent | throw (.unknownNode parent)
    parentResultsRev := result :: parentResultsRev
  let parentResults := parentResultsRev.reverse

  let mut inheritedSuffix : Option String := none
  for result in parentResults do
    match inheritedSuffix, result.mostSpecificSuffix with
    | none, next => inheritedSuffix := next
    | _, none => pure ()
    | some current, some next =>
      if suffixReaches table current next then
        pure ()
      else if suffixReaches table next current then
        inheritedSuffix := some next
      else
        throw .incompatibleSuffixes

  let inheritedTail ← match inheritedSuffix with
    | none => pure []
    | some suffix =>
      let some result := lookup table suffix | throw (.unknownNode suffix)
      pure result.precedence
  if !orders.all (fun order => respectsSuffixTail order inheritedTail) then
    throw .suffixOrderViolation

  let candidates :=
    (parentResults.map (fun result => withoutTail result.precedence inheritedTail)) ++
    (orders.map (fun order => withoutTail order inheritedTail))
  let mergedPrefix ← merge candidates
  return {
    precedence := [node.name] ++ mergedPrefix ++ inheritedTail
    inheritedSuffix := inheritedSuffix
    mostSpecificSuffix := if node.suffix then some node.name else inheritedSuffix
  }

/-- Resolve a node only after its parents, retaining each completed C4 result.
The remaining node count bounds recursion, including cyclic graphs. -/
private def resolveNode (index : Std.HashMap String Node) (root name : String)
    (table : Table) : Nat → Except Error Table
  | 0 =>
      if (lookup table name).isSome then .ok table else .error (.cycle root)
  | fuel + 1 => do
      if (lookup table name).isSome then
        return table
      let some node := index.get? name | throw (.unknownNode name)
      let mut ready := table
      for parent in parents node do
        ready ← resolveNode index root parent ready fuel
      let result ← computeNode ready node
      return ready.insert name result

/-- First declarations own name lookup until duplicate validation reports an
error; indexing avoids repeated linear searches while discovering reachability. -/
private def nodeIndex (graph : Graph) : Std.HashMap String Node :=
  graph.nodes.foldl (fun table node =>
    if table.contains node.name then table else table.insert node.name node) {}

/-- Discover each reachable name once in breadth-first order. Every queued
name comes from the root or one parent edge, so the finite edge count bounds
the loop even when an edge points to an unknown node. -/
private def reachable (graph : Graph) (index : Std.HashMap String Node)
    (root : String) : List String := Id.run do
  let fuel := graph.nodes.foldl (fun total node =>
    total + node.parentOrders.flatten.length) 1
  let mut pending := [root]
  let mut seen : Std.HashSet String := {}
  let mut reversed := []
  for _ in [:fuel] do
    match pending with
    | [] => break
    | name :: rest =>
        pending := rest
        if !seen.contains name then
          seen := seen.insert name
          reversed := name :: reversed
          if let some node := index.get? name then
            pending := pending ++ parents node
  return reversed.reverse

/-- Total finite-graph C4 translation. All iterations have bounds from graph size. -/
def linearize (graph : Graph) (root : String) : Except Error (List String) := do
  let index := nodeIndex graph
  if (index.get? root).isNone then
    throw (.unknownNode root)
  let names := reachable graph index root
  let namesSet := names.foldl (fun seen name => seen.insert name)
    ({} : Std.HashSet String)
  let nodes := graph.nodes.filter (fun node => namesSet.contains node.name)
  ({ nodes } : Graph).validate
  let table ← resolveNode index root root {} nodes.length
  let some result := lookup table root | throw (.cycle root)
  return result.precedence

end LeanPoo.C4
