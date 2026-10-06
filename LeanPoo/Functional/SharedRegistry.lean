import LeanPoo.Functional.Registry

/-! One declaration-scoped provider registry shared by any verified roots of
one graph. Stored entries do not add ancestors to a root's selection order. -/
namespace LeanPoo.Functional
universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable {graph other : C4.Graph}

private theorem ancestor_declared (order : C4.VerifiedOrder graph root)
    (ancestor : C4.Ancestor graph name root) : name ∈ graph.nodes.map C4.Node.name := by
  obtain ⟨_, _, trace, _⟩ := order.ancestor_order ancestor
  obtain ⟨node, member, same⟩ := trace.declared
  exact List.mem_map.mpr ⟨node, member, same⟩

/-- Construct once from declarations, without compiling any root or invoking
factories. This index alone does not validate the graph or establish precedence. -/
def ProviderRegistry.ofGraph (graph : C4.Graph)
    (providers : String → Provider Context Key Value) : ProviderRegistry Context Key Value :=
  ofNames (graph.nodes.map C4.Node.name) id providers

/-- Every declared name retains its whole provider, including unrelated nodes. -/
theorem ProviderRegistry.ofGraph_lookup (providers : String → Provider Context Key Value)
    (member : name ∈ graph.nodes.map C4.Node.name) :
    (ofGraph graph providers).dictionary name = providers name := by
  have found : (ofNames (graph.nodes.map C4.Node.name) id providers).entries[name]? =
      some (providers name) := ofNames_lookup _ id Function.injective_id providers member
  simp only [ofGraph, dictionary, found]

/-- Undeclared application providers are outside the shared graph registry. -/
theorem ProviderRegistry.ofGraph_missing (providers : String → Provider Context Key Value)
    (missing : name ∉ graph.nodes.map C4.Node.name) :
    (ofGraph graph providers).dictionary name key = none := by
  exact ofNames_missing _ id providers (fun source member same => missing (same ▸ member))

/-- Any verified root selects the exact original factory from this shared table. -/
theorem assemble_ofGraph_registry (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (key : Key) :
    assemble order (ProviderRegistry.ofGraph graph providers).dictionary key = assemble order providers key := by
  unfold assemble
  simpa using select_rename (providers := providers) (names := order.output) (key := key)
    id (ProviderRegistry.ofGraph graph providers).dictionary
    (fun name member => congrFun (ProviderRegistry.ofGraph_lookup providers
      (ancestor_declared order (order.covers.mp member))) key)

theorem Requirements.prepare_ofGraph_registry (order : C4.VerifiedOrder graph root)
    (providers : String → Provider Context Key Value) (keys : List Key) :
    prepare (assemble order (ProviderRegistry.ofGraph graph providers).dictionary) keys =
      prepare (assemble order providers) keys := by
  apply prepare_congr
  intro key _
  exact assemble_ofGraph_registry order providers key

/-- Build one mapped declaration registry and retain it across all migrated roots.
Only names are changed; the original provider functions are stored intact. -/
def ProviderRegistry.relabelGraph (change : graph.Relabeling other)
    (providers : String → Provider Context Key Value) : ProviderRegistry Context Key Value :=
  ofNames (graph.nodes.map C4.Node.name) change.rename providers

theorem ProviderRegistry.relabelGraph_lookup (change : graph.Relabeling other)
    (providers : String → Provider Context Key Value) (member : name ∈ graph.nodes.map C4.Node.name) :
    (relabelGraph change providers).dictionary (change.rename name) = providers name := by
  simp [relabelGraph, dictionary, ofNames_lookup _ change.rename change.injective providers member]

theorem ProviderRegistry.relabelGraph_missing (change : graph.Relabeling other)
    (providers : String → Provider Context Key Value)
    (missing : name ∉ graph.nodes.map C4.Node.name) :
    (relabelGraph change providers).dictionary (change.rename name) key = none := by
  exact ofNames_missing _ change.rename providers
    (fun source member same => missing (change.injective same ▸ member))

/-- Shared and root-cut registries agree on every mapped ancestor; they can differ
on direct dictionary queries outside that root's cut. -/
theorem ProviderRegistry.relabelGraph_relabel (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (providers : String → Provider Context Key Value)
    (ancestor : C4.Ancestor graph name root) :
    (relabelGraph change providers).dictionary (change.rename name) =
      (relabel order change providers).dictionary (change.rename name) := by
  rw [relabelGraph_lookup change providers (ancestor_declared order ancestor),
      relabel_aligned order change providers ancestor]

theorem assemble_relabelGraph_registry (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) (key : Key) :
    assemble (order.relabel change unique) (ProviderRegistry.relabelGraph change providers).dictionary key =
      assemble order providers key := by
  apply assemble_relabel
  intro name ancestor
  exact congrFun (ProviderRegistry.relabelGraph_lookup change providers (ancestor_declared order ancestor)) key

theorem Requirements.prepare_relabelGraph_registry (order : C4.VerifiedOrder graph root)
    (change : graph.Relabeling other) (unique : (graph.nodes.map C4.Node.name).Nodup)
    (providers : String → Provider Context Key Value) (keys : List Key) :
    prepare (assemble (order.relabel change unique)
      (ProviderRegistry.relabelGraph change providers).dictionary) keys =
      prepare (assemble order providers) keys := by
  apply prepare_congr
  intro key _
  exact assemble_relabelGraph_registry order change unique providers key

end LeanPoo.Functional
