import LeanPoo.C4.Presentation
import LeanPoo.Functional.Requirements

/-! Preserve named capability consumers when declaration storage is reordered.
Provider dictionaries and capability/result families are unchanged. -/
namespace LeanPoo.Functional

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {graph other : C4.Graph}

/-- Reuse the same dictionary after declaration reordering. No factory lookup,
provider reconstruction or factory invocation is added by the proof. -/
theorem assemble_permute (order : C4.VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) :
    assemble (order.permute same unique) providers = assemble order providers := rfl

/-- A whole consumer checklist retains exact functions and first missing-key
errors. Result and proof consumers can use equality without handwritten require. -/
theorem Requirements.prepare_permute (order : C4.VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key) :
    prepare (assemble (order.permute same unique) providers) keys =
      prepare (assemble order providers) keys := rfl

end LeanPoo.Functional
