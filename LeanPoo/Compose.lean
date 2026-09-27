import LeanPoo.Object.Resolve

/-!
Static graph constructors corresponding to Gerbil-POO object.ss .mix,
.extend, and .+. C4 remains the sole authority for precedence.
-/

namespace LeanPoo

universe u v

private def addNode (schema : Object.Schema Key Value) (node : C4.Node)
    (declaration : Object.Declaration Key Value) :
    Object.Schema Key Value :=
  { graph := { nodes := schema.graph.nodes ++ [node] }
    declaration := fun query =>
      if query == node.name then some declaration else schema.declaration query }

/-- Stage a single-parent layer without resolving C4 yet. This is safe for
private construction: a fresh child of an existing parent cannot change the
parent's precedence. The final root is still validated by `Object.compile`. -/
def extendSchema (schema : Object.Schema Key Value) (name parent : String)
    (declaration : Object.Declaration Key Value) :
    Except C4.Error (Object.Schema Key Value) := do
  if (schema.graph.findNode? name).isSome then
    throw (.duplicateNode name)
  if (schema.graph.findNode? parent).isNone then
    throw (.unknownNode parent)
  return addNode schema { name, parentOrders := [[parent]] } declaration

/-- Build an object from the complete C4 node metadata. -/
def mixC4 (schema : Object.Schema Key Value) (node : C4.Node)
    (declaration : Object.Declaration Key Value) :
    Except C4.Error (Object.Plan Key Value) :=
  Object.compile (addNode schema node declaration) node.name

/-- Add one object with Gerbil's flat, ordered supers and compile its C4 plan. -/
def mix (schema : Object.Schema Key Value) (name : String)
    (supers : List String) (declaration : Object.Declaration Key Value) :
    Except C4.Error (Object.Plan Key Value) :=
  mixC4 schema
    { name, parentOrders := if supers.isEmpty then [] else [supers] }
    declaration

/-- Extend one parent with a new declaration. -/
def extend (schema : Object.Schema Key Value) (name parent : String)
    (declaration : Object.Declaration Key Value) :
    Except C4.Error (Object.Plan Key Value) :=
  mix schema name [parent] declaration

inductive CompositionError where
  | c4 (error : C4.Error)
  | nonFlatOverride (name : String)
  deriving Repr

/-- Gerbil's .+ takes the override's own declaration, places its supers
before the base, and creates a new object. The override must use the flat
Gerbil parent surface, rather than C++'s multiple local parent orders. -/
def plus {Key : Type u} {Value : Key → Type v}
    (schema : Object.Schema Key Value) (name base overrideName : String) :
    Except CompositionError (Object.Plan Key Value) :=
  match schema.graph.findNode? overrideName with
  | none => .error (.c4 (.unknownNode overrideName))
  | some overrideNode =>
      let build (supers : List String) :=
        let declaration := (schema.declaration overrideName).getD Object.Declaration.empty
        match mix schema name (supers ++ [base]) declaration with
        | .ok plan => .ok plan
        | .error error => .error (.c4 error)
      match overrideNode.parentOrders with
      | [] => build []
      | [order] => build order
      | _ => .error (.nonFlatOverride overrideName)

inductive CloneError (Key : Type u) where
  | c4 (error : C4.Error)
  | duplicateOverride (key : Key)
  deriving Repr

/-- Clone the direct declaration and topology, replacing each listed direct
slot once. The new node is validated by the same C4 compiler as mix. -/
def clone {Key : Type u} {Value : Key → Type v}
    [DecidableEq Key] [BEq Key] [LawfulBEq Key] [Hashable Key]
    (schema : Object.Schema Key Value) (name source : String)
    (overrides : List (Sigma Value)) :
    Except (CloneError Key) (Object.Plan Key Value) := do
  let some sourceNode := schema.graph.findNode? source |
    throw (.c4 (.unknownNode source))
  let mut seen : Std.HashSet Key := {}
  let mut declaration :=
    (schema.declaration source).getD Object.Declaration.empty
  for override in overrides do
    if seen.contains override.1 then
      throw (.duplicateOverride override.1)
    seen := seen.insert override.1
    declaration := declaration.withValue override.1 override.2
  let copied : Object.Schema Key Value :=
    { graph := { nodes := schema.graph.nodes ++
        [{ sourceNode with name }] }
      declaration := fun query =>
        if query == name then some declaration else schema.declaration query }
  match Object.compile copied name with
  | .ok plan => pure plan
  | .error error => throw (.c4 error)

end LeanPoo
