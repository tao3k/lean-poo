import LeanPoo.C4.OrderRelation

namespace LeanPoo.C4

/-- Rename identities while retaining declaration, local-row, and suffix order. -/
def Node.rename (rename : String → String) (node : Node) : Node :=
  {name := rename node.name, parentOrders := node.parentOrders.map (List.map rename), suffix := node.suffix}

def Graph.rename (graph : Graph) (rename : String → String) : Graph :=
  {nodes := graph.nodes.map (Node.rename rename)}

namespace Renaming
variable (rename : String → String) (injective : Function.Injective rename)

include injective in
private theorem equal (a b : String) : (rename a == rename b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact ⟨fun h => injective h, congrArg rename⟩

include injective in
private theorem contains (items : List String) (name : String) :
    (items.map rename).contains (rename name) = items.contains name := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨a, member, same⟩ => by simpa [injective same] using member,
    fun member => ⟨name, member, rfl⟩⟩

private theorem empty (items : List String) : (items.map rename).isEmpty = items.isEmpty := by
  cases items <;> rfl

private theorem all_empty (lists : List (List String)) :
    (lists.map (List.map rename)).all List.isEmpty = lists.all List.isEmpty := by
  induction lists with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.all_cons, empty, ih]

private theorem heads (lists : List (List String)) :
    Precedence.heads (lists.map (List.map rename)) = (Precedence.heads lists).map rename := by
  induction lists with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp only [Precedence.heads, List.map_cons, List.filterMap_cons,
      List.head?_nil, List.head?_cons, List.map_nil, List.map_cons]
    · exact ih
    · exact congrArg (_ :: ·) ih

include injective in
private theorem eligible (lists : List (List String)) (name : String) :
    Precedence.eligible (lists.map (List.map rename)) (rename name) = Precedence.eligible lists name := by
  induction lists with
  | nil => rfl
  | cons first rest ih =>
    cases first <;> simp only [Precedence.eligible, List.map_cons, List.map_nil, List.all_cons,
      List.drop_succ_cons, List.drop_zero, List.drop_nil, List.contains_nil,
      contains rename injective] at * <;> rw [ih]

private theorem find (items : List String) (predicate : String → Bool)
    (renamedPredicate : String → Bool) (same : ∀ name, renamedPredicate (rename name) = predicate name) :
    (items.map rename).find? renamedPredicate = (items.find? predicate).map rename := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [List.map_cons, List.find?_cons, same]; split <;> simp_all

include injective in
/-- The leftmost eligible choice depends on equality and input order, not labels. -/
theorem choose (lists : List (List String)) :
    Precedence.choose (lists.map (List.map rename)) = (Precedence.choose lists).map rename := by
  unfold Precedence.choose
  rw [all_empty, heads]
  split
  · rfl
  · exact find rename _ _ _ (eligible rename injective lists)

include injective in
private theorem advance_order (items : List String) (name : String) :
    Precedence.advanceOrder (rename name) (items.map rename) =
      (Precedence.advanceOrder name items).map rename := by
  cases items with
  | nil => rfl
  | cons first rest => simp only [List.map_cons, Precedence.advanceOrder, equal rename injective]; split <;> rfl

include injective in
private theorem advance (lists : List (List String)) (name : String) :
    Precedence.advance (lists.map (List.map rename)) (rename name) =
      (Precedence.advance lists name).map (List.map rename) := by
  simp only [Precedence.advance, List.map_map]
  congr 1
  funext items
  exact advance_order rename injective items name

include injective in
/-- Transport an original merge derivation without replaying its algorithm. -/
theorem trace (original : Precedence.Trace lists output) :
    Precedence.Trace (lists.map (List.map rename)) (output.map rename) := by
  induction original with
  | done finished => exact .done (by rw [all_empty]; exact finished)
  | @step lists name output selected rest ih =>
    apply Precedence.Trace.step
    · rw [choose rename injective, selected]; rfl
    · rw [advance rename injective]; exact ih

include injective in
private theorem without_tail (items tail : List String) :
    withoutTail (items.map rename) (tail.map rename) = (withoutTail items tail).map rename := by
  induction items with
  | nil => rfl
  | cons first rest ih => simp only [withoutTail, List.map_cons, List.filter_cons, contains rename injective] at *; split <;> simp_all

include injective in
private theorem compatible (original : SuffixCompatible items tail) :
    SuffixCompatible (items.map rename) (tail.map rename) := by
  obtain ⟨front, suffix, same, absent, kept⟩ := original
  refine ⟨front.map rename, suffix.map rename, by simp [same], ?_, kept.map rename⟩
  intro name present member
  obtain ⟨first, inFront, rfl⟩ := List.mem_map.mp present
  obtain ⟨second, inTail, eq⟩ := List.mem_map.mp member
  exact absent first inFront (by simpa [injective eq] using inTail)

/-- Rename an inherited-tail certificate; its proof data erase at runtime. -/
def tail (original : TailCertified tails) : TailCertified (tails.map (List.map rename)) where
  output := original.output.map rename
  chosen := by
    rcases original.chosen with ⟨none, nil⟩ | present
    · exact .inl ⟨by simp [none], by simp [nil]⟩
    · exact .inr (List.mem_map.mpr ⟨_, present, rfl⟩)
  containsTail := by
    intro items present
    obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
    exact (original.containsTail before member).map rename

/-- Rename the complete prefix/suffix certificate, preserving literal tails. -/
def suffix (original : SuffixCertified orders inherited) :
    SuffixCertified (orders.map (List.map rename)) (inherited.map rename) where
  front := original.front.map rename
  trace := by
    have transported := trace rename injective original.trace
    have mapped : (orders.map (fun items => withoutTail items inherited)).map (List.map rename) =
        (orders.map (List.map rename)).map (fun items => withoutTail items (inherited.map rename)) := by
      simp only [List.map_map]
      congr 1
      funext items
      exact (without_tail rename injective items inherited).symm
    rw [mapped] at transported
    exact transported
  compatible := by
    intro items present
    obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
    exact compatible rename injective (original.compatible before member)

/-- Transport complete node evidence, including freshness and duplicate freedom. -/
def node (original : NodeCertified name orders tails) :
    NodeCertified (rename name) (orders.map (List.map rename)) (tails.map (List.map rename)) where
  selection := tail rename original.selection
  ancestry := suffix rename injective original.ancestry
  tailUnique := original.tailUnique.map rename (fun a b different same => different (injective same))
  fresh := by
    change rename name ∉ original.ancestry.front.map rename ++ original.selection.output.map rename
    rw [← List.map_append]
    intro present
    obtain ⟨before, member, same⟩ := List.mem_map.mp present
    exact original.fresh (by simpa only [injective same, SuffixCertified.output] using member)

include injective in
private theorem lookup (nodes : List Node) (name : String) :
    (nodes.map (Node.rename rename)).find? (fun n => n.name == rename name) =
      (nodes.find? (fun n => n.name == name)).map (Node.rename rename) := by
  induction nodes with
  | nil => rfl
  | cons first rest ih =>
    simp only [List.map_cons, List.find?_cons, Node.rename, equal rename injective]
    split <;> simp_all [Node.rename]

include injective in
theorem find_node (graph : Graph) (name : String) :
    (graph.rename rename).findNode? (rename name) =
      (graph.findNode? name).map (Node.rename rename) :=
  lookup rename injective graph.nodes name

end Renaming

/-- Original graph evidence is preserved by injective relabeling of identities. -/
theorem GraphTrace.rename (original : GraphTrace graph name output inherited)
    (rename : String → String) (injective : Function.Injective rename) :
    GraphTrace (graph.rename rename) (rename name) (output.map rename) (inherited.map rename) := by
  induction original with
  | @node name declaration found rows names parents certificate ih =>
    let renamedRows := rows.map (fun row => (rename row.1, (row.2.1.map rename, row.2.2.map rename)))
    have found' : (graph.rename rename).findNode? (rename name) = some (declaration.rename rename) := by
      rw [Renaming.find_node rename injective, found]; rfl
    have names' : renamedRows.map Prod.fst = (declaration.rename rename).parentOrders.flatten := by
      simp only [renamedRows, List.map_map, Node.rename]
      rw [← List.map_flatten, ← names, List.map_map]
      rfl
    have parents' : ∀ row ∈ renamedRows,
        GraphTrace (graph.rename rename) row.1 row.2.1 row.2.2 := by
      intro row present
      obtain ⟨before, member, rfl⟩ := List.mem_map.mp present
      exact ih before member
    have orderEq : renamedRows.map (fun row => row.2.1) ++ (declaration.rename rename).parentOrders =
        (rows.map (fun row => row.2.1) ++ declaration.parentOrders).map (List.map rename) := by
      simp [renamedRows, Node.rename, List.map_append, List.map_map]
    have tailsEq : renamedRows.map (fun row => row.2.2) =
        (rows.map (fun row => row.2.2)).map (List.map rename) := by simp [renamedRows, List.map_map]
    have transported : ∃ cert : NodeCertified (rename name)
        ((rows.map (fun row => row.2.1) ++ declaration.parentOrders).map (List.map rename))
        ((rows.map (fun row => row.2.2)).map (List.map rename)),
        cert.output = certificate.output.map rename ∧
        cert.selection.output = certificate.selection.output.map rename := by
      refine ⟨Renaming.node rename injective certificate, ?_, rfl⟩
      simp only [Renaming.node, Renaming.suffix, Renaming.tail,
        NodeCertified.output, SuffixCertified.output, List.map_cons, List.map_append]
    rw [← orderEq, ← tailsEq] at transported
    obtain ⟨cert, outputEq, selectedEq⟩ := transported
    have result := GraphTrace.node found' renamedRows names' parents' cert
    rw [outputEq, selectedEq] at result
    by_cases flag : declaration.suffix = true <;> simpa [Node.rename, flag] using result

/-- Migrate a retained result by mapping its names once. Neither compiler is
executed; global declaration uniqueness is an explicit sufficient premise. -/
def VerifiedOrder.rename (order : VerifiedOrder graph root)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map Node.name).Nodup) :
    VerifiedOrder (graph.rename rename) (rename root) where
  output := order.output.map rename
  derivation := by
    obtain ⟨inherited, original⟩ := order.derivation
    exact ⟨inherited.map rename, original.rename rename injective⟩
  accepted := by
    obtain ⟨inherited, original⟩ := order.derivation
    apply linearizeChecked_unique_complete (original.rename rename injective)
    apply LinearizeState.reachableUnique_of_global
    simpa only [Graph.rename, List.map_map, Node.rename, Function.comp_def, List.Nodup] using
      unique.map rename (fun a b different same => different (injective same))

@[simp] theorem VerifiedOrder.rename_output (order : VerifiedOrder graph root)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map Node.name).Nodup) :
    (order.rename rename injective unique).output = order.output.map rename := rfl

/-- Every independent verified compilation of the renamed graph agrees with
transported evidence, irrespective of its execution strategy. -/
theorem VerifiedOrder.rename_unique (order : VerifiedOrder graph root)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map Node.name).Nodup)
    (other : VerifiedOrder (graph.rename rename) (rename root)) :
    other.output = order.output.map rename :=
  other.unique (order.rename rename injective unique)

/-- Pair queries commute with injective renaming, including absent/self queries. -/
theorem VerifiedOrder.rename_precedes (order : VerifiedOrder graph root)
    (rename : String → String) (injective : Function.Injective rename)
    (unique : (graph.nodes.map Node.name).Nodup) :
    (order.rename rename injective unique).precedes (rename left) (rename right) =
      order.precedes left right := by
  apply Bool.eq_iff_iff.mpr
  rw [VerifiedOrder.precedes_iff, VerifiedOrder.precedes_iff]
  change ([left, right].map rename).Sublist (order.output.map rename) ↔
    [left, right].Sublist order.output
  constructor
  · intro kept
    obtain ⟨before, included, same⟩ := List.sublist_map_iff.mp kept
    have identical := (List.map_inj_right (fun a b h => injective h)).mp same
    simpa [← identical] using included
  · exact fun kept => kept.map rename

end LeanPoo.C4
