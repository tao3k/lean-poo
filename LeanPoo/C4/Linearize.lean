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
  let mut parentResults : List Linearization := []
  for parent in parents node do
    let some result := lookup table parent | throw (.unknownNode parent)
    parentResults := parentResults ++ [result]

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

/-- Add nodes whose parents are already in the table; preserve declaration order. -/
private def pass (nodes : List Node) (table : Table) : Except Error Table :=
  nodes.foldl (fun state node => do
    let ready ← state
    if (lookup ready node.name).isSome then
      return ready
    if !(parents node).all (fun parent => (lookup ready parent).isSome) then
      return ready
    let result ← computeNode ready node
    return ready.insert node.name result) (.ok table)

/-- Names reachable from the requested root; other nodes cannot affect it. -/
private def reachable (graph : Graph) (root : String) : List String :=
  (List.range graph.nodes.length).foldl (fun names _ =>
    unique (names ++ (names.flatMap fun name =>
      match graph.findNode? name with
      | none => []
      | some node => parents node))) [root]

/-- Total finite-graph C4 translation. All iterations have bounds from graph size. -/
def linearize (graph : Graph) (root : String) : Except Error (List String) := do
  if (graph.findNode? root).isNone then
    throw (.unknownNode root)
  let names := reachable graph root
  let nodes := graph.nodes.filter (fun node => names.contains node.name)
  ({ nodes } : Graph).validate
  let table ← (List.range nodes.length).foldl
    (fun state _ => state.bind (pass nodes)) (.ok {} : Except Error Table)
  let some result := lookup table root | throw (.cycle root)
  return result.precedence

end LeanPoo.C4
