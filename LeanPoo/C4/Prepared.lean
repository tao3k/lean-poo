import LeanPoo.C4.AuditedResolver

namespace LeanPoo.C4

/-- A complete observable result, including the original error, indexed by
the actual immutable graph and requested root. -/
abbrev PreparedResult (graph : Graph) (root : String) :=
  Thunk { result : Except Error (List String) // result = linearize graph root }

/-- Finite graph-owned preparation. Root results stay lazy; the first valid
root demand prepares a canonical ancestor table for the finite declared graph.
Successful ancestor entries are shared across roots, including cached suffixes. -/
structure Prepared (graph : Graph) where
  roots : Std.DHashMap String (PreparedResult graph)
  missing : (root : String) → PreparedResult graph root

private abbrev SharedTable (graph : Graph) :=
  { table : LinearizeState.Table // LinearizeState.MetadataInvariant graph table }

/-- Populate one graph-owned ancestor table. A failed branch never publishes
partial metadata. Its requesting root keeps the original compiler/error path. -/
private def prepareAncestors (graph : Graph)
    (index : Std.HashMap String Node) (same : index = LinearizeState.nodeIndex graph) : SharedTable graph :=
  graph.nodes.foldl (fun before node =>
    match done : LinearizeState.resolveAuditedNode index node.name node.name
        before.val graph.nodes.length with
    | .error _ => before
    | .ok table => ⟨table,
        (LinearizeState.resolveAuditedNode_acceptance before.property (same ▸ done)).2.2⟩)
    ⟨{}, LinearizeState.MetadataInvariant.empty graph⟩

/-- Preserve the original reachable-only validation before consulting shared
ancestors. Failed audits use the original compiler, never an audit diagnostic. -/
private def preparedRoot (graph : Graph) (index : Std.HashMap String Node)
    (same : index = LinearizeState.nodeIndex graph) (shared : Thunk (SharedTable graph))
    (root : String) : { result : Except Error (List String) // result = linearize graph root } :=
  if (index.get? root).isNone then ⟨linearize graph root, rfl⟩ else
  let names := LinearizeState.reachable graph index root
  let namesSet := names.foldl (fun seen name => seen.insert name) ({} : Std.HashSet String)
  let nodes := graph.nodes.filter (fun node => namesSet.contains node.name)
  match validated : (Graph.mk nodes).validate with
  | .error _ => ⟨linearize graph root, rfl⟩
  | .ok _ =>
    let ready := shared.get
    match found : LinearizeState.lookup ready.val root with
    | none => ⟨linearize graph root, rfl⟩
    | some entry => ⟨.ok entry.precedence, by
        have trace := ready.property.tail root entry found
        apply (linearize_complete trace _).symm
        simpa only [nodes, namesSet, names, same, LinearizeState.reachableNodes] using validated⟩

def prepare (graph : Graph) : Prepared graph :=
  let index := LinearizeState.nodeIndex graph
  let shared := Thunk.mk fun _ => prepareAncestors graph index rfl
  let make : (root : String) → PreparedResult graph root := fun root =>
    Thunk.mk fun _ => preparedRoot graph index rfl shared root
  let roots := graph.nodes.foldl (fun roots node =>
    if roots.contains node.name then roots else roots.insert node.name (make node.name))
      ({} : Std.DHashMap String (PreparedResult graph))
  ⟨roots, make⟩

/-- Retain an already proved exact result, such as an existing Object Plan.
The certificate binds both the graph and root; names alone cannot seed a table. -/
def Prepared.retain (prepared : Prepared graph) (root : String)
    (result : Except Error (List String)) (valid : result = linearize graph root) : Prepared graph :=
  { prepared with roots := prepared.roots.insert root (Thunk.pure ⟨result, valid⟩) }

def Prepared.at (prepared : Prepared graph) (root : String) : Except Error (List String) :=
  match prepared.roots.get? root with
  | some result => result.get.val
  | none => (prepared.missing root).get.val

/-- Universal complete result/error equality, also for absent roots and invalid
graphs. A key alone cannot admit an unbound result. -/
theorem Prepared.at_eq (prepared : Prepared graph) (root : String) :
    prepared.at root = linearize graph root := by
  unfold Prepared.at
  split
  · rename_i result _
    exact result.get.property
  · exact (prepared.missing root).get.property

end LeanPoo.C4
