import LeanPoo.C4.GraphComputeInvariant

namespace LeanPoo.Tests.GraphComputeInvariant
open C4 LinearizeState

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) :
    ∃ certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders)
      (suffixTails table (entries.map (·.mostSpecificSuffix))),
      certificate.output = output ∧
        tail = (if node.suffix then certificate.output else certificate.selection.output) ∧
        ∀ target declaration, graph.findNode? target = some declaration → declaration.suffix = true →
          Ancestor graph target node.name → target ≠ node.name → target ∈ certificate.selection.output :=
  graph_node_certificate valid trace found collected

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool) :
    ∃ chosen, computeNode table node checked = .ok {
      precedence := output
      inheritedSuffix := chosen
      mostSpecificSuffix := if node.suffix then some node.name else chosen } ∧
      tail = (if node.suffix then output else selectedTail table chosen) :=
  computeNode_graph_complete valid trace found collected checked

example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool) :
    ∃ result, computeNode table node checked = .ok result ∧ result.precedence = output ∧
      MetadataInvariant graph (table.insert node.name result) :=
  computeNode_metadata_insert valid trace found fresh collected checked

/- The newly computed entry supports semantic ancestry queries immediately;
the stronger invariant is usable by the next traversal layer. -/
example (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph node.name output tail) (found : graph.findNode? node.name = some node)
    (fresh : lookup table node.name = none)
    (collected : collectParents table (parents node) = .ok entries) (checked : Bool)
    (declared : graph.findNode? target = some declaration) (marked : declaration.suffix = true) :
    ∃ result, computeNode table node checked = .ok result ∧ result.precedence = output ∧
      (suffixReaches (table.insert node.name result) node.name target = true ↔
        Ancestor graph target node.name) := by
  obtain ⟨result, computed, same, inserted⟩ :=
    computeNode_metadata_insert valid trace found fresh collected checked
  have cached : lookup (table.insert node.name result) node.name = some result := by
    simp [lookup_insert]
  exact ⟨result, computed, same, suffixReaches_flagged_iff inserted cached declared marked⟩

#print axioms collected_parent_tail_map
#print axioms graph_node_certificate
#print axioms computeNode_graph_complete
#print axioms computeNode_graph_insert
#print axioms fresh_insert_retains
#print axioms selectedTail_fresh_insert
#print axioms MetadataInvariant.insert
#print axioms computeNode_metadata_insert

end LeanPoo.Tests.GraphComputeInvariant
