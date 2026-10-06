import LeanPoo.C4.Renaming
import LeanPoo.C4.Presentation

/-! Explicit label-and-storage migration witnesses. A witness preserves exact
parent rows and suffix flags while allowing injective labels and declaration
permutation. It is not inferred from graph similarity. -/
namespace LeanPoo.C4
variable {graph middle other : Graph}

/-- Package one injective label map and the exact target declaration permutation.
Provider alignment and name uniqueness are separate application obligations. -/
structure Graph.Relabeling (graph other : Graph) where
  rename : String → String
  injective : Function.Injective rename
  declarations : (graph.rename rename).nodes.Perm other.nodes

private theorem node_rename_comp (node : Node) (first second : String → String) :
    (node.rename first).rename second = node.rename (second ∘ first) := by
  cases node
  simp [Node.rename, List.map_map, Function.comp_def]

namespace Graph.Relabeling

/-- Compose migration descriptions before moving any retained output. -/
def trans (first : graph.Relabeling middle) (second : middle.Relabeling other) :
    graph.Relabeling other where
  rename := second.rename ∘ first.rename
  injective := second.injective.comp first.injective
  declarations := by
    have combined := (first.declarations.map (Node.rename second.rename)).trans second.declarations
    have same : (graph.rename (second.rename ∘ first.rename)).nodes =
        (graph.rename first.rename).nodes.map (Node.rename second.rename) := by
      simp only [Graph.rename, List.map_map]
      congr 1
      funext node
      exact (node_rename_comp node first.rename second.rename).symm
    rw [same]
    exact combined

/-- Target uniqueness follows from the explicit witness and source uniqueness. -/
theorem unique (change : graph.Relabeling other)
    (source : (graph.nodes.map Node.name).Nodup) : (other.nodes.map Node.name).Nodup := by
  apply (change.declarations.map Node.name).nodup_iff.mp
  have renamed : ((graph.nodes.map Node.name).map change.rename).Nodup := source.map change.rename (fun a b different same => different (change.injective same))
  simpa only [Graph.rename, List.map_map, Node.rename, Function.comp_def] using renamed

end Graph.Relabeling

/-- Map the retained output once and supply erased evidence for the exact target.
No resolver or graph-lookup validation executes in this migration operation. -/
def VerifiedOrder.relabel (order : VerifiedOrder graph root) (change : graph.Relabeling other)
    (unique : (graph.nodes.map Node.name).Nodup) : VerifiedOrder other (change.rename root) :=
  (order.rename change.rename change.injective unique).permute change.declarations (by
    have renamed : ((graph.nodes.map Node.name).map change.rename).Nodup := unique.map change.rename (fun a b different same => different (change.injective same))
    simpa only [Graph.rename, List.map_map, Node.rename, Function.comp_def] using renamed)

@[simp] theorem VerifiedOrder.relabel_output (order : VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map Node.name).Nodup) :
    (order.relabel change unique).output = order.output.map change.rename := rfl

/-- Any independently verified target order has exactly the mapped source output. -/
theorem VerifiedOrder.relabel_unique (order : VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map Node.name).Nodup)
    (fresh : VerifiedOrder other (change.rename root)) :
    fresh.output = order.output.map change.rename := fresh.unique (order.relabel change unique)

/-- Compose descriptions and migrate once, or migrate sequentially: equal output.
The direct path maps one list; the sequential path maps an intermediate list too. -/
theorem VerifiedOrder.relabel_trans_output (order : VerifiedOrder graph root)
    (first : graph.Relabeling middle) (second : middle.Relabeling other)
    (unique : (graph.nodes.map Node.name).Nodup) :
    ((order.relabel first unique).relabel second (first.unique unique)).output =
      (order.relabel (first.trans second) unique).output := by
  simp only [relabel_output, List.map_map, Graph.Relabeling.trans]

/-- Pair queries preserve injectively mapped identities, including absent names. -/
theorem VerifiedOrder.relabel_precedes (order : VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map Node.name).Nodup) :
    (order.relabel change unique).precedes (change.rename left) (change.rename right) =
      order.precedes left right := by
  change (order.rename change.rename change.injective unique).precedes
    (change.rename left) (change.rename right) = _
  exact order.rename_precedes change.rename change.injective unique

end LeanPoo.C4
