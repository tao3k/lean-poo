import LeanPoo.C4.VerifiedOrder

/-! Retain verified results when graph declarations are reordered. Local parent
orders and suffix flags remain part of the exact declaration identity. -/
namespace LeanPoo.C4

variable {graph other : Graph}

/-- Exact name lookup agreement, including absent names. This is stronger than
agreement only on the ancestors of one root. -/
def Graph.SameLookup (graph other : Graph) : Prop :=
  ∀ name, graph.findNode? name = other.findNode? name

private theorem lookup_perm {before after : List Node} (same : before.Perm after)
    (unique : (before.map Node.name).Nodup) (name : String) :
    before.find? (fun node => node.name == name) =
      after.find? (fun node => node.name == name) := by
  induction same with
  | nil => rfl
  | cons node perm ih =>
    simp only [List.map_cons, List.nodup_cons] at unique
    simp only [List.find?_cons]
    rw [ih unique.2]
  | swap a b tail =>
    simp only [List.map_cons, List.nodup_cons, List.mem_cons] at unique
    by_cases first : a.name == name
    · by_cases second : b.name == name
      · have identical : a.name = b.name := (beq_iff_eq.mp first).trans (beq_iff_eq.mp second).symm
        exact False.elim (unique.1 (Or.inl identical.symm))
      · simp [first, second]
    · simp [List.find?_cons, first]
  | trans first second ih₁ ih₂ =>
    exact (ih₁ unique).trans (ih₂ ((first.map Node.name).nodup_iff.mp unique))

/-- Permuting uniquely named declarations preserves all graph lookups. -/
theorem Graph.sameLookup_of_perm (same : graph.nodes.Perm other.nodes)
    (unique : (graph.nodes.map Node.name).Nodup) : graph.SameLookup other :=
  fun name => lookup_perm same unique name

/-- The complete graph derivation depends on exact lookups, not storage order. -/
theorem GraphTrace.represent (trace : GraphTrace graph root output tail)
    (same : graph.SameLookup other) : GraphTrace other root output tail := by
  induction trace with
  | node found rows names parents certificate ih =>
    exact .node ((same _).symm.trans found) rows names ih certificate

/-- Retain the original output list and supply erased evidence for another
lookup-equivalent graph. Neither resolver executes in this operation. -/
def VerifiedOrder.represent (order : VerifiedOrder graph root)
    (same : graph.SameLookup other) (unique : (other.nodes.map Node.name).Nodup) :
    VerifiedOrder other root where
  output := order.output
  derivation := by
    obtain ⟨tail, trace⟩ := order.derivation
    exact ⟨tail, trace.represent same⟩
  accepted := by
    obtain ⟨tail, trace⟩ := order.derivation
    exact linearizeChecked_unique_complete (trace.represent same)
      (LinearizeState.reachableUnique_of_global unique)

/-- A public declaration-reordering operation; output is retained unchanged. -/
def VerifiedOrder.permute (order : VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map Node.name).Nodup) :
    VerifiedOrder other root :=
  order.represent (Graph.sameLookup_of_perm same unique) ((same.map Node.name).nodup_iff.mp unique)

@[simp] theorem VerifiedOrder.permute_output (order : VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map Node.name).Nodup) :
    (order.permute same unique).output = order.output := rfl

/-- Every independent verified result agrees with the retained presentation. -/
theorem VerifiedOrder.permute_unique (order : VerifiedOrder graph root)
    (same : graph.nodes.Perm other.nodes) (unique : (graph.nodes.map Node.name).Nodup)
    (fresh : VerifiedOrder other root) : fresh.output = order.output :=
  fresh.unique (order.permute same unique)

/-- Successful checked outputs are invariant. Rejection payloads may differ
because validation still reports the first malformed declaration. -/
theorem linearizeChecked_permute_ok (same : graph.nodes.Perm other.nodes)
    (unique : (graph.nodes.map Node.name).Nodup) :
    linearizeChecked graph root = .ok output ↔ linearizeChecked other root = .ok output := by
  constructor
  · intro accepted
    obtain ⟨tail, trace⟩ := linearizeChecked_graph_sound accepted
    exact linearizeChecked_unique_complete (trace.represent (Graph.sameLookup_of_perm same unique))
      (LinearizeState.reachableUnique_of_global ((same.map Node.name).nodup_iff.mp unique))
  · intro accepted
    obtain ⟨tail, trace⟩ := linearizeChecked_graph_sound accepted
    exact linearizeChecked_unique_complete
      (trace.represent (Graph.sameLookup_of_perm same.symm ((same.map Node.name).nodup_iff.mp unique)))
      (LinearizeState.reachableUnique_of_global unique)

end LeanPoo.C4
