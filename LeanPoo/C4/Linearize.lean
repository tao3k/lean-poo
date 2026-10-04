import Std
import LeanPoo.C4.NodeCertificate

/-!
C4 metadata algorithm translated from François-René Rideau's C4-Mixins,
include/c4/linearize.hpp.
Upstream offers Apache-2.0 or No Problem Bugroff; this translation uses Apache-2.0.
-/

namespace LeanPoo.C4

/- Named runtime operations supply proof seams for graph indexing and traversal. -/
namespace LinearizeState

abbrev Table := Std.HashMap String Linearization

def lookup (table : Table) (name : String) : Option Linearization :=
  table.get? name

def parents (node : Node) : List String :=
  unique node.parentOrders.flatten

/-- One step through the already computed inherited-suffix chain. -/
@[inline] def suffixStep (table : Table) (target : String)
    (state : Option String × Bool) (_ : Nat) : Option String × Bool :=
  let (current, found) := state
  if found then (current, true)
  else match current with
    | none => (none, false)
    | some name =>
      if name == target then (current, true)
      else ((lookup table name).bind Linearization.inheritedSuffix, false)

def suffixReachesWithFuel (table : Table) (source target : String) (fuel : Nat) : Bool :=
  ((List.range fuel).foldl (suffixStep table target) (some source, false)).2

/-- Walk the inherited-suffix chain with the actual table-size budget. -/
def suffixReaches (table : Table) (source target : String) : Bool :=
  suffixReachesWithFuel table source target (table.size + 1)

/-- Compare two inherited suffix names using the actual bounded cache walk. -/
def selectSuffixStep (table : Table) (current next : Option String) :
    Except Error (Option String) :=
  match current, next with
  | none, next => .ok next
  | current, none => .ok current
  | some current, some next =>
    if suffixReaches table current next then .ok (some current)
    else if suffixReaches table next current then .ok (some next)
    else .error .incompatibleSuffixes

/-- Fold parent suffix metadata in its original declaration order. -/
def selectSuffix (table : Table) : List (Option String) → Option String →
    Except Error (Option String)
  | [], current => .ok current
  | next :: rest, current => do
    let selected ← selectSuffixStep table current next
    selectSuffix table rest selected

/-- Collect cached parents in declaration order, accumulating in reverse. -/
def collectParentsRev (table : Table) : List String → List Linearization →
    Except Error (List Linearization)
  | [], reversed => .ok reversed
  | name :: rest, reversed => do
    let some entry := lookup table name | throw (.unknownNode name)
    collectParentsRev table rest (entry :: reversed)

def collectParents (table : Table) (names : List String) : Except Error (List Linearization) := do
  let reversed ← collectParentsRev table names []
  return reversed.reverse

/-- Compute one node after all its parents have been computed. -/
def computeNode (table : Table) (node : Node) (checked : Bool) :
    Except Error Linearization := do
  let orders := node.parentOrders.filter (fun order => !order.isEmpty)
  let parentResults ← collectParents table (parents node)

  let inheritedSuffix ← selectSuffix table (parentResults.map (·.mostSpecificSuffix)) none

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
  let mergedAncestry ← if checked then
    do
      let mut tailsRev : List (List String) := []
      for result in parentResults do
        if let some suffix := result.mostSpecificSuffix then
          let some cached := lookup table suffix | throw (.unknownNode suffix)
          tailsRev := cached.precedence :: tailsRev
      let certificate ← certifyNode node.name
        (parentResults.map (·.precedence) ++ orders) tailsRev.reverse inheritedTail
      pure certificate.ancestry.output
  else do
    let mergedPrefix ← merge candidates
    pure (mergedPrefix ++ inheritedTail)
  return {
    precedence := node.name :: mergedAncestry
    inheritedSuffix := inheritedSuffix
    mostSpecificSuffix := if node.suffix then some node.name else inheritedSuffix
  }

/-- Resolve a node only after its parents, retaining each completed C4 result.
The remaining node count bounds recursion, including cyclic graphs. -/
def resolveNode (index : Std.HashMap String Node) (root name : String)
    (table : Table) (checked : Bool) : Nat → Except Error Table
  | 0 =>
      if (lookup table name).isSome then .ok table else .error (.cycle root)
  | fuel + 1 => do
      if (lookup table name).isSome then
        return table
      let some node := index.get? name | throw (.unknownNode name)
      let mut ready := table
      for parent in parents node do
        ready ← resolveNode index root parent ready checked fuel
      let result ← computeNode ready node checked
      return ready.insert name result

/-- First declarations own name lookup until duplicate validation reports an
error; indexing avoids repeated linear searches while discovering reachability. -/
@[inline] def indexStep (table : Std.HashMap String Node) (node : Node) : Std.HashMap String Node :=
  if table.contains node.name then table else table.insert node.name node

def nodeIndex (graph : Graph) : Std.HashMap String Node :=
  graph.nodes.foldl indexStep {}

/-- Discover each reachable name once in breadth-first order. Every queued
name comes from the root or one parent edge, so the finite edge count bounds
the loop even when an edge points to an unknown node. -/
def reachable (graph : Graph) (index : Std.HashMap String Node)
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
def linearizeWith (graph : Graph) (root : String) (checked : Bool) : Except Error (List String) := do
  let index := nodeIndex graph
  if (index.get? root).isNone then
    throw (.unknownNode root)
  let names := reachable graph index root
  let namesSet := names.foldl (fun seen name => seen.insert name)
    ({} : Std.HashSet String)
  let nodes := graph.nodes.filter (fun node => namesSet.contains node.name)
  ({ nodes } : Graph).validate
  let table ← resolveNode index root root {} checked nodes.length
  let some result := lookup table root | throw (.cycle root)
  return result.precedence

end LinearizeState

/-- The ordinary tail-count implementation. -/
def linearize (graph : Graph) (root : String) : Except Error (List String) :=
  LinearizeState.linearizeWith graph root false

/-- Opt-in independent replay and suffix reconstruction for every reachable
node. Each accepted merge certifies order preservation for all complete parent
and local inputs, and retention of the inherited tail as an actual suffix.
The selected tail is independently checked against all cached parent tails,
and the prepended node name is checked for freshness. This does not prove
the graph traversal or cached metadata correct for every graph. -/
def linearizeChecked (graph : Graph) (root : String) : Except Error (List String) :=
  LinearizeState.linearizeWith graph root true

end LeanPoo.C4
