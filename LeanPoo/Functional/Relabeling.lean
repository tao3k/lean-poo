import LeanPoo.C4.Relabeling
import LeanPoo.Functional.Requirements

/-! Capability consumers across explicit label-and-declaration migrations. Only
requested keys on original ancestors need aligned provider entries. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {graph other : C4.Graph}

/-- Combine name and declaration changes without changing the selected factory.
Provider alignment is scoped to original ancestors for this capability. -/
theorem assemble_relabel (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers mapped : String → Provider Context Key Value) (key : Key)
    (aligned : ∀ name, C4.Ancestor graph name root →
      mapped (change.rename name) key = providers name key) :
    assemble (order.relabel change unique) mapped key = assemble order providers key := by
  exact assemble_rename order change.rename change.injective unique mapped aligned

/-- Preserve one caller-owned checklist, exact functions and first missing key.
No alignment obligation is introduced for unrequested capabilities. -/
theorem Requirements.prepare_relabel (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers mapped : String → Provider Context Key Value) (keys : List Key)
    (aligned : ∀ name, C4.Ancestor graph name root → ∀ key ∈ keys,
      mapped (change.rename name) key = providers name key) :
    prepare (assemble (order.relabel change unique) mapped) keys =
      prepare (assemble order providers) keys := by
  apply prepare_congr
  intro key requested
  exact assemble_relabel order change unique providers mapped key
    (fun name ancestor => aligned name ancestor key requested)

end LeanPoo.Functional
