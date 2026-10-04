import LeanPoo.Object.Memo

/-! Chapter 7's two-level inheritance exercise: linearize specification sorts,
then impose their cross-sort priorities in each selected ancestry and wrap the result.
-/
namespace LeanPoo.Object.SortedInheritance
universe u v

/-- Most-specific sort first. Classifications cover the selected source ancestry. -/
structure Policy where
  sorts : C4.Graph
  root : String
  classification : List (String × String)

def precedes (order : List String) (first second : String) : Bool :=
  order.contains first && order.contains second && decide (order.idxOf first < order.idxOf second)

def higher (priority : List String) (classification : List (String × String))
    (first second : String) : Bool :=
  match classification.find? (·.1 == first), classification.find? (·.1 == second) with
  | some (_, firstSort), some (_, secondSort) => precedes priority firstSort secondSort
  | _, _ => false

/-- Every ordered pair from distinct priority levels; same-sort order stays with C4. -/
def requirements (source priority : List String) (classification : List (String × String)) :
    List (String × String) :=
  source.flatMap fun first => source.filterMap fun second =>
    if higher priority classification first second then some (first, second) else none

theorem requirements_complete (source priority : List String)
    (classification : List (String × String)) (first second : String)
    (firstIn : first ∈ source) (secondIn : second ∈ source)
    (priorityBefore : higher priority classification first second = true) :
    (first, second) ∈ requirements source priority classification := by
  apply List.mem_flatMap.mpr
  refine ⟨first, firstIn, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨second, secondIn, by simp [priorityBefore]⟩

/-- A checked result binds the complete cross-sort requirements to the actual
executable object's C4 precedence. The wrapper contributes no direct slots. -/
structure Certified (Key : Type u) (Value : Key → Type v)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  object : Memoized Key Value
  source : List String
  priority : List String
  classification : List (String × String)
  respects : (requirements source priority classification).all
    (fun pair => precedes object.plan.precedence pair.1 pair.2) = true

theorem Certified.higher_precedes {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (result : Certified Key Value) (first second : String)
    (firstIn : first ∈ result.source) (secondIn : second ∈ result.source)
    (priorityBefore : higher result.priority result.classification first second = true) :
    precedes result.object.plan.precedence first second = true :=
  (List.all_eq_true.mp result.respects) (first, second)
    (requirements_complete _ _ _ first second firstIn secondIn priorityBefore)

inductive Error where
  | sorts (error : C4.Error)
  | repeatedClassification (name : String)
  | unknownSpecification (name : String)
  | unavailableSort (specification sort : String)
  | unclassified (name : String)
  | inheritance (error : C4.Error) (requirements : List (String × String))
  | priorityNotRespected (requirements : List (String × String))
  deriving Repr

private def validate (policy : Policy) (source : List String) :
    Except Error (List String) := do
  let priority ← (C4.linearize policy.sorts policy.root).mapError .sorts
  let mut seen : Std.HashSet String := {}
  for (specification, sort) in policy.classification do
    if seen.contains specification then throw (.repeatedClassification specification)
    unless source.contains specification do throw (.unknownSpecification specification)
    unless priority.contains sort do throw (.unavailableSort specification sort)
    seen := seen.insert specification
  for specification in source do
    unless seen.contains specification do throw (.unclassified specification)
  return priority

/-- Each selected node receives constraints among its own proper ancestors.
This lets C4 derive parent precedence under the sort policy before descendants
inherit it. Original declarations and unrelated graph nodes are retained. -/
private def constrainGraph (graph : C4.Graph) (source : List String)
    (required : List (String × String)) : Except Error C4.Graph := do
  let nodes ← graph.nodes.mapM fun node => do
    if !source.contains node.name then return node
    let ancestry ← (C4.linearize graph node.name).mapError (fun e => .inheritance e required)
    let parents := ancestry.filter (· != node.name)
    let applicable := required.filter fun pair => parents.contains pair.1 && parents.contains pair.2
    return { node with parentOrders := node.parentOrders ++ applicable.map (fun (first, second) => [first, second]) }
  return { nodes }

/-- Validate all metadata before constructing the new object. The sort hierarchy
has its own selected C4 root; unrelated sorts cannot classify this source. -/
def apply {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (policy : Policy) (source : Memoized Key Value) (name : String) :
    Except Error (Certified Key Value) :=
  match validate policy source.plan.precedence with
  | .error error => .error error
  | .ok priority =>
    let required := requirements source.plan.precedence priority policy.classification
    match constrainGraph source.plan.schema.graph source.plan.precedence required with
    | .error error => .error error
    | .ok graph =>
      let schema := { source.plan.schema with graph := graph }
      match LeanPoo.mixC4 schema
          { name, parentOrders := [source.plan.root] :: required.map (fun (first, second) => [first, second]) }
          Declaration.empty with
      | .error error => .error (.inheritance error required)
      | .ok plan =>
        let object := source.rebuild plan
        if checked : required.all (fun pair => precedes object.plan.precedence pair.1 pair.2) = true then
          .ok { object := object
                source := source.plan.precedence
                priority := priority
                classification := policy.classification
                respects := checked }
        else
          .error (.priorityNotRespected
            (required.filter fun pair => !precedes object.plan.precedence pair.1 pair.2))

end LeanPoo.Object.SortedInheritance
