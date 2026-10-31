import LeanPoo.C4.Linearize

namespace LeanPoo.C4

/-- A complete observable result, including the original error, indexed by
the actual immutable graph and requested root. -/
abbrev PreparedResult (graph : Graph) (root : String) :=
  Thunk { result : Except Error (List String) // result = linearize graph root }

/-- Finite graph-owned preparation. Only requested roots are evaluated.
The resolver's temporary ancestor table is not retained per root. -/
structure Prepared (graph : Graph) where
  roots : Std.DHashMap String (PreparedResult graph)
  missing : (root : String) → PreparedResult graph root

def prepare (graph : Graph) : Prepared graph :=
  let index := LinearizeState.nodeIndex graph
  let make : (root : String) → PreparedResult graph root := fun root =>
    Thunk.mk fun _ => ⟨LinearizeState.linearizeIndexed graph index root false, rfl⟩
  let roots := graph.nodes.foldl (fun roots node =>
    if roots.contains node.name then roots else roots.insert node.name (make node.name))
      ({} : Std.DHashMap String (PreparedResult graph))
  ⟨roots, make⟩

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
