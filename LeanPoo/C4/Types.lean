import Std

namespace LeanPoo.C4

/-- A node's local parent orders are listed in declaration order. -/
structure Node where
  name : String
  parentOrders : List (List String) := []
  suffix : Bool := false
  deriving Repr, BEq, Inhabited

structure Graph where
  nodes : List Node
  deriving Repr, Inhabited

inductive Error where
  | duplicateNode (name : String)
  | unknownNode (name : String)
  | cycle (name : String)
  | inconsistentOrder
  | incompatibleSuffixes
  | suffixOrderViolation
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The metadata C4 needs while walking an inheritance graph. -/
structure Linearization where
  precedence : List String
  inheritedSuffix : Option String
  mostSpecificSuffix : Option String
  deriving Repr, BEq, Inhabited

def Graph.findNode? (graph : Graph) (name : String) : Option Node :=
  graph.nodes.find? (fun node => node.name == name)

def unique (items : List String) : List String :=
  let (_, reversed) := items.foldl (fun (seen, reversed) item =>
    if seen.contains item then (seen, reversed)
    else (seen.insert item, item :: reversed))
    (({} : Std.HashSet String), [])
  reversed.reverse

/-- Validate names before following edges, so missing references have one error path. -/
def Graph.validate (graph : Graph) : Except Error Unit := do
  let mut seen : Std.HashSet String := {}
  for node in graph.nodes do
    if seen.contains node.name then
      throw (.duplicateNode node.name)
    seen := seen.insert node.name
  for node in graph.nodes do
    for order in node.parentOrders do
      for parent in order do
        if !seen.contains parent then
          throw (.unknownNode parent)

end LeanPoo.C4
