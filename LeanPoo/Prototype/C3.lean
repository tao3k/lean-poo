import LeanPoo.C4.Precedence

/-! The paper's ordinary C3 policy, separate from the C4 object policy. -/
namespace LeanPoo.Prototype.C3

abbrev Graph := List (String × List String)
abbrev Cache := Std.HashMap String (List String)

/-- Typed source not-null?: the empty list differs from every atomic value. -/
def notNull (value : Sum (List α) β) : Bool :=
  match value with
  | .inl values => !values.isEmpty
  | .inr _ => true

def removeNulls (lists : List (List α)) : List (List α) :=
  lists.filter (!·.isEmpty)

def removeNext [BEq α] (next : α) (lists : List (List α)) : List (List α) :=
  removeNulls (lists.map (fun row => if row.head? == some next then row.tail else row))

/-- Internal production traversal; exposed so graph-level soundness can state
an invariant over its incoming and outgoing memo tables. -/
def visit (graph : Graph) (name : String) (path : List String) (cache : Cache) :
    Nat → Except LeanPoo.C4.Error (List String × Cache)
  | 0 => .error (.cycle name)
  | fuel+1 => do
    if path.contains name then throw (.cycle name)
    if let some result := cache.get? name then return (result,cache)
    let some entry := graph.find? (fun entry => entry.1 == name) | throw (.unknownNode name)
    let mut current := cache
    let mut orders := []
    for parent in entry.2 do
      let (order, updated) ← visit graph parent (name :: path) current fuel
      current := updated
      orders := order :: orders
    -- Standard C3: merge parent linearizations, followed by direct-parent order.
    let tail ← LeanPoo.C4.Precedence.mergeCertified (orders.reverse ++ [entry.2])
    let result := name :: tail.output
    return (result,current.insert name result)

/-- Internal validation used by the scalar and batched production paths. -/
def validateGraph (graph : Graph) : Except LeanPoo.C4.Error Unit := do
  let mut seen : Std.HashSet String := {}
  for (name,parents) in graph do
    if seen.contains name then throw (.duplicateNode name)
    seen := seen.insert name
    if parents.length != (LeanPoo.C4.unique parents).length then throw .inconsistentOrder

/-- Validate one finite graph and share ancestor computations across roots. -/
def linearizeMany (graph : Graph) (roots : List String) :
    Except LeanPoo.C4.Error (List (List String)) := do
  validateGraph graph
  let mut cache : Cache := {}
  let mut orders := []
  for root in roots do
    let (order, updated) ← visit graph root [] cache (graph.length+1)
    cache := updated
    orders := order :: orders
  return orders.reverse

/-- Ordinary C3 over a finite graph. Duplicate names/parents are refused. -/
def linearize (graph : Graph) (root : String) : Except LeanPoo.C4.Error (List String) := do
  validateGraph graph
  return (← visit graph root [] {} (graph.length+1)).1

/-- A one-root batch has the same result and error as the scalar entry point,
for every graph and root. Both start with an empty cache. -/
theorem linearizeMany_singleton (graph : Graph) (root : String) :
    linearizeMany graph [root] = (linearize graph root).map (fun order => [order]) := by
  cases valid : validateGraph graph with
  | error err => simp [linearizeMany, linearize, valid, bind, Except.bind, Except.map]
  | ok _ =>
    cases result : visit graph root [] {} (graph.length+1) with
    | error err => simp [linearizeMany, linearize, valid, result, bind, Except.bind, Except.map]
    | ok value =>
      simp [linearizeMany, linearize, valid, result, bind, Except.bind, Except.map]
      rfl

end LeanPoo.Prototype.C3
