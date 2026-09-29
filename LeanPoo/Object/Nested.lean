import LeanPoo.Object.Memo

/-!
A nested object is an ordinary typed slot value. These method fragments
extend its inherited object when the outer C4 resolver reaches the slot.
They use the same inner C4 composition operations as a top-level object.
-/

namespace LeanPoo.Object.Nested

universe u v w x

/-- Give every outer node a distinct identity inside one inner family. -/
def liftedName (namePrefix outerName : String) : String :=
  namePrefix ++ "/" ++ outerName

/-- One direct inner specification at an outer node. Its additional parent
orders can name prototypes in the supplied inner base family. -/
structure Layer (Key : Type w) (Value : Key → Type x) where
  declaration : Declaration Key Value := Declaration.empty
  parentOrders : List (List String) := []
  suffix : Option Bool := none

inductive ContributionError where
  | unknownOuterNode (name : String)
  | duplicateLayer (name : String)
  deriving Repr, BEq

/-- A finite, checked declaration of the outer nodes that contribute to one
inner focus. Only nodes reachable from the selected outer root may contribute.
The list order is authoring order; C4, not that order, resolves inheritance. -/
structure Contributions (Key : Type w) (Value : Key → Type x) where
  layers : Std.HashMap String (Layer Key Value)

def Contributions.ofEntries {OuterKey : Type u}
    {OuterValue : OuterKey → Type v} {Key : Type w}
    {Value : Key → Type x} (outer : Plan OuterKey OuterValue)
    (entries : List (String × Layer Key Value)) :
    Except ContributionError (Contributions Key Value) := do
  let reachable := outer.precedence.foldl
    (fun names name => names.insert name) ({} : Std.HashSet String)
  let layers ← entries.foldlM (fun layers (name, layer) => do
    unless reachable.contains name do
      throw (.unknownOuterNode name)
    if layers.contains name then
      throw (.duplicateLayer name)
    return layers.insert name layer) ({} : Std.HashMap String (Layer Key Value))
  return ⟨layers⟩

def Contributions.lookup (contributions : Contributions Key Value)
    (name : String) : Option (Layer Key Value) :=
  contributions.layers.get? name

private structure Focus (Key : Type w) (Value : Key → Type x) where
  nodes : Std.HashMap String C4.Node
  relevant : Std.HashSet String
  layers : Std.HashMap String (Layer Key Value)

/-- A node remains at the inner focus when it contributes directly or an
ancestor contributes. The reverse outer C4 order visits every parent before
its child. Direct declarations are evaluated once and retained by name. -/
private def prepareFocus {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    (outer : Plan OuterKey OuterValue) (namePrefix : String)
    (contribution : String → Option (Layer Key Value)) :
    Focus Key Value :=
  let outerNodes : Std.HashMap String C4.Node :=
    outer.schema.graph.nodes.foldl
      (fun table node => table.insert node.name node) {}
  let (relevant, layers) :=
    outer.precedence.reverse.foldl (fun (relevant, layers) name =>
    let direct := contribution name
    let inherited := (outerNodes.get? name).elim false fun node =>
      node.parentOrders.flatten.any relevant.contains
    let nextRelevant :=
      if direct.isSome || inherited then relevant.insert name else relevant
    let nextLayers := match direct with
      | some layer => layers.insert (liftedName namePrefix name) layer
      | none => layers
    (nextRelevant, nextLayers)) ({}, {})
  ⟨outerNodes, relevant, layers⟩

/-- Keep the transitive ancestor closure of direct inner contributions.
Intermediate identity nodes retain C4 constraints. A separate inner base
becomes a shared ancestor of every retained leaf. -/
private def liftedSchema {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    (outer : Plan OuterKey OuterValue) (namePrefix : String)
    (focus : Focus Key Value) (relevant : Std.HashSet String)
    (baseRoots : List String) : Schema Key Value :=
  let rename := liftedName namePrefix
  let names := outer.precedence.filter relevant.contains
  let nodes := names.filterMap fun name =>
    (focus.nodes.get? name).map fun node =>
      let keptOrders := node.parentOrders.map fun order =>
        (order.filter relevant.contains).map rename
      let layer := focus.layers.get? (rename name)
      let extraOrders := (layer.map (·.parentOrders)).getD []
      let baseOrders := if keptOrders.flatten.isEmpty then
        baseRoots.map (fun root => [root]) else []
      { node with
        name := rename name
        parentOrders := keptOrders ++ extraOrders ++ baseOrders
        suffix := (layer.bind (·.suffix)).getD node.suffix }
  { graph := { nodes }
    declaration := fun name => (focus.layers.get? name).map (·.declaration) }

private def fullAncestry {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    (outer : Plan OuterKey OuterValue) : Std.HashSet String :=
  outer.precedence.foldl (fun names name => names.insert name) {}

/-- Check that pruning has not changed the order of contributed ancestors. -/
private def preservesOrder {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    (outer : Plan OuterKey OuterValue) (inner : Plan Key Value)
    (namePrefix : String) (relevant : Std.HashSet String) : Bool :=
  let expected := (outer.precedence.filter relevant.contains).map
    (liftedName namePrefix)
  let selected : Std.HashSet String :=
    expected.foldl (fun names name => names.insert name) {}
  inner.precedence.filter selected.contains == expected

inductive LiftError where
  | schema (error : SchemaMergeError)
  | c4 (error : C4.Error)
  | orderingDrift
  | missingFocus
  deriving Repr

/-- One checked compiler for both standalone and base-backed inner graphs.
If pruning changes C4 precedence, retry with the complete outer ancestry. -/
private def compileFocus {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    (outer : Plan OuterKey OuterValue) (bases : List (Plan Key Value))
    (namePrefix : String)
    (contribution : String → Option (Layer Key Value)) :
    Except LiftError (Option (Plan Key Value)) := do
  let focus := prepareFocus outer namePrefix contribution
  if !focus.relevant.contains outer.root then return none
  let compileWith (kept : Std.HashSet String) :
      Except LiftError (Plan Key Value) := do
    let lifted := liftedSchema outer namePrefix focus kept
      (bases.map (·.root))
    let schema ← (lifted.mergeDisjointMany
      (bases.map (·.schema))).mapError .schema
    (compile schema (liftedName namePrefix outer.root)).mapError .c4
  match compileWith focus.relevant with
  | .error (.schema error) => throw (.schema error)
  | .error _ => pure ⟨⟩
  | .ok compact =>
      if preservesOrder outer compact namePrefix focus.relevant then
        return some compact
  let full := fullAncestry outer
  let plan ← compileWith full
  if preservesOrder outer plan namePrefix full then
    return some plan
  throw .orderingDrift

/-- Lift explicitly supplied inner layers through the relevant
outer ancestry. A missing focus yields `none`; nodes with contributing
ancestors but no direct method remain as identity ordering layers. -/
def liftLayers {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (outer : Plan OuterKey OuterValue) (namePrefix : String)
    (contribution : String → Option (Layer Key Value)) :
    Except LiftError (Option (Memoized Key Value)) :=
  (compileFocus outer [] namePrefix contribution).map
    (Option.map Plan.memoize)

/-- Lift an outer DAG over a separate inner base family. The base is shared
by every relevant leaf, so it appears once below all contributions.
The base's resolution mode is retained in the derived object. -/
def liftLayersOn {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (outer : Plan OuterKey OuterValue) (base : Memoized Key Value)
    (namePrefix : String)
    (contribution : String → Option (Layer Key Value)) :
    Except LiftError (Memoized Key Value) := do
  let plan? ← compileFocus outer [base.plan] namePrefix contribution
  return (plan?.map base.rebuild).getD base

/-- Lift a focus over several independent inner families. Each base root is
an independent parent of the retained outer leaves. Identity collisions are
reported by the same disjoint-schema check used by first-class object mixing;
the first base selects the resulting resolution mode. -/
def liftLayersOnMany {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (outer : Plan OuterKey OuterValue) (first : Memoized Key Value)
    (others : List (Memoized Key Value)) (namePrefix : String)
    (contribution : String → Option (Layer Key Value)) :
    Except LiftError (Memoized Key Value) := do
  let bases := first :: others
  let plan? ← compileFocus outer (bases.map (·.plan)) namePrefix contribution
  match plan? with
  | some plan => return first.rebuild plan
  | none => throw .missingFocus

/-- Direct declarations are layers without additional inner parents. -/
def lift {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (outer : Plan OuterKey OuterValue) (namePrefix : String)
    (contribution : String → Option (Declaration Key Value)) :
    Except LiftError (Option (Memoized Key Value)) :=
  liftLayers outer namePrefix (fun name =>
    (contribution name).map fun declaration => { declaration })

/-- Add a common inner base to direct declarations with no additional
inner parent orders. -/
def liftOn {OuterKey : Type u} {OuterValue : OuterKey → Type v}
    {Key : Type w} {Value : Key → Type x}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (outer : Plan OuterKey OuterValue) (base : Memoized Key Value)
    (namePrefix : String)
    (contribution : String → Option (Declaration Key Value)) :
    Except LiftError (Memoized Key Value) :=
  liftLayersOn outer base namePrefix (fun name =>
    (contribution name).map fun declaration => { declaration })

/-- Lift one fallible change of an inner value into a delayed outer slot
method. Absence and prior errors propagate without invoking the change. -/
def mapInherited {Outer : Type u} {Error : Type v} {Inner : Type w}
    (change : Inner → Except Error Inner) :
    Prototype.SlotSpec Outer (Option (Except Error Inner)) :=
  .computed fun _ inherited =>
    (inherited ()).map (·.bind change)

theorem mapInherited_eval {Outer : Type u} {Error : Type v}
    {Inner : Type w} (change : Inner → Except Error Inner)
    (self : Outer)
    (inherited : Prototype.Next (Option (Except Error Inner))) :
    (mapInherited change).eval self inherited =
      (inherited ()).map (·.bind change) := rfl

/-- Extend an inherited inner object with an independently defined override.
The outer slot retains both absence and inner composition errors. -/
def plusWith {Outer : Type u} {Key : Type v} {Value : Key → Type w}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (override : Memoized Key Value) (name : String) :
    Prototype.SlotSpec Outer
      (Option (Except PlusWithError (Memoized Key Value))) :=
  mapInherited fun base => base.plusWith override name

/-- Extend an inherited inner object with an override already present in its
own C4 family. The outer slot retains inner composition errors. -/
def plus {Outer : Type u} {Key : Type v} {Value : Key → Type w}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (name overrideName : String) :
    Prototype.SlotSpec Outer
      (Option (Except LeanPoo.CompositionError (Memoized Key Value))) :=
  mapInherited fun base => base.plus name overrideName

end LeanPoo.Object.Nested
