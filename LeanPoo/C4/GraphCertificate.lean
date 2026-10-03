import LeanPoo.C4.Linearize

namespace LeanPoo.C4

/-- A finite derivation tied to exact graph lookups and all declared parent
edges. The third index records the node's most-specific suffix precedence. -/
inductive GraphTrace (graph : Graph) : String → List String → List String → Prop where
  | node (found : graph.findNode? name = some node)
      (rows : List (String × (List String × List String)))
      (names : rows.map Prod.fst = node.parentOrders.flatten)
      (parents : ∀ row ∈ rows, GraphTrace graph row.1 row.2.1 row.2.2)
      (certificate : NodeCertified name
        (rows.map (fun row => row.2.1) ++ node.parentOrders)
        (rows.map (fun row => row.2.2))) :
      GraphTrace graph name certificate.output
        (if node.suffix then certificate.output else certificate.selection.output)

structure GraphResult (graph : Graph) (root : String) where
  output : List String
  mostSpecificTail : List String
  trace : GraphTrace graph root output mostSpecificTail

theorem GraphTrace.nodup (trace : GraphTrace graph root output tail) : output.Nodup := by
  cases trace with
  | node _ _ _ _ certificate => exact certificate.nodup

theorem GraphTrace.head (trace : GraphTrace graph root output tail) :
    output.head? = some root := by
  cases trace with
  | node _ _ _ _ certificate => exact certificate.head

theorem GraphTrace.suffix (trace : GraphTrace graph root output tail) : tail.IsSuffix output := by
  cases trace with
  | node found rows names parents certificate =>
    split
    · exact ⟨[], rfl⟩
    · exact certificate.inherited_suffix

/-- Every declared direct parent has a derivation whose complete precedence
is an ordered sublist of the child's returned precedence. -/
theorem GraphTrace.parent {node : Node} {parent : String} (trace : GraphTrace graph root output tail)
    (found : graph.findNode? root = some node) (member : parent ∈ node.parentOrders.flatten) :
    ∃ parentOutput parentTail, GraphTrace graph parent parentOutput parentTail ∧
      parentOutput.Sublist output := by
  cases trace with
  | node actual rows names parents certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    rw [← names] at member
    obtain ⟨row, present, name⟩ := List.mem_map.mp member
    refine ⟨row.2.1, row.2.2, ?_, ?_⟩
    · simpa [name] using parents row present
    · exact certificate.preserves (List.mem_append_left _ (List.mem_map.mpr ⟨row, present, rfl⟩))

theorem GraphTrace.local_order {node : Node} (trace : GraphTrace graph root output tail)
    (found : graph.findNode? root = some node) (member : order ∈ node.parentOrders) :
    order.Sublist output := by
  cases trace with
  | node actual rows names parents certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    exact certificate.preserves (List.mem_append_right _ member)

theorem GraphTrace.parent_tail {node : Node} {parent : String}
    (trace : GraphTrace graph root output tail)
    (found : graph.findNode? root = some node) (member : parent ∈ node.parentOrders.flatten) :
    ∃ parentOutput parentTail, GraphTrace graph parent parentOutput parentTail ∧
      parentTail.IsSuffix tail := by
  cases trace with
  | node actual rows names parents certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    rw [← names] at member
    obtain ⟨row, present, name⟩ := List.mem_map.mp member
    refine ⟨row.2.1, row.2.2, ?_, ?_⟩
    · simpa [name] using parents row present
    · have input : row.2.2 ∈ rows.map (fun row => row.2.2) := List.mem_map.mpr ⟨row, present, rfl⟩
      split
      · exact certificate.parent_suffix input
      · exact certificate.selection.containsTail _ input

theorem GraphTrace.flagged {node : Node} (trace : GraphTrace graph root output tail)
    (found : graph.findNode? root = some node) (flag : node.suffix = true) : tail = output := by
  cases trace with
  | node actual rows names parents certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    simp [flag]

/-- Reachability follows the first graph declaration, exactly as graph lookup
does. Every edge is one name in that declaration's local parent orders. -/
inductive Ancestor (graph : Graph) : String → String → Prop where
  | self : Ancestor graph name name
  | parent (found : graph.findNode? child = some node)
      (member : parent ∈ node.parentOrders.flatten)
      (earlier : Ancestor graph ancestor parent) : Ancestor graph ancestor child

/-- A finite root derivation includes every graph ancestor, preserving its
derived precedence as an ordered sublist of the root precedence. -/
theorem GraphTrace.ancestor {ancestor : String} (path : Ancestor graph ancestor root) :
    ∀ {output tail}, GraphTrace graph root output tail →
      ∃ ancestorOutput ancestorTail, GraphTrace graph ancestor ancestorOutput ancestorTail ∧
        ancestorOutput.Sublist output := by
  induction path with
  | self =>
    intro output tail trace
    exact ⟨output, tail, trace, List.Sublist.refl _⟩
  | parent found member earlier ih =>
    intro output tail trace
    obtain ⟨parentOutput, parentTail, parentTrace, kept⟩ := trace.parent found member
    obtain ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited⟩ := ih parentTrace
    exact ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited.trans kept⟩

theorem GraphTrace.ancestor_tail {ancestor : String} (path : Ancestor graph ancestor root) :
    ∀ {output tail}, GraphTrace graph root output tail →
      ∃ ancestorOutput ancestorTail, GraphTrace graph ancestor ancestorOutput ancestorTail ∧
        ancestorTail.IsSuffix tail := by
  induction path with
  | self =>
    intro output tail trace
    exact ⟨output, tail, trace, List.suffix_refl _⟩
  | parent found member earlier ih =>
    intro output tail trace
    obtain ⟨parentOutput, parentTail, parentTrace, kept⟩ := trace.parent_tail found member
    obtain ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited⟩ := ih parentTrace
    exact ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited.trans kept⟩

theorem GraphTrace.root_mem (trace : GraphTrace graph root output tail) : root ∈ output := by
  cases trace with
  | node _ _ _ _ certificate => simp [NodeCertified.output]

theorem GraphTrace.covers (trace : GraphTrace graph root output tail) :
    item ∈ output ↔ Ancestor graph item root := by
  constructor
  · intro member
    induction trace with
    | node found rows names parents certificate ih =>
      have edge (row) (present : row ∈ rows) : row.1 ∈ rows.map Prod.fst :=
        List.mem_map.mpr ⟨row, present, rfl⟩
      rcases certificate.covers.mp member with own | ⟨order, present, contains⟩ | tailMember
      · subst item
        exact .self
      · rcases List.mem_append.mp present with parentOrder | localOrder
        · obtain ⟨row, rowPresent, same⟩ := List.mem_map.mp parentOrder
          subst order
          exact .parent found (by simpa only [names] using edge row rowPresent) (ih row rowPresent contains)
        · exact .parent found (List.mem_flatten.mpr ⟨order, localOrder, contains⟩) .self
      · rcases certificate.selection.chosen with ⟨_, empty⟩ | selected
        · simp [empty] at tailMember
        · obtain ⟨row, present, same⟩ := List.mem_map.mp selected
          rw [← same] at tailMember
          have inherited := (parents row present).suffix.sublist.subset tailMember
          exact .parent found (by simpa only [names] using edge row present) (ih row present inherited)
  · intro path
    obtain ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited⟩ := trace.ancestor path
    exact inherited.subset ancestorTrace.root_mem

private def longestTail (tails : List (List String)) : List String :=
  tails.foldl (fun current next => if current.length < next.length then next else current) []

/-- Independent bounded reconstruction from graph declarations. Parent rows
carry their derivations rather than relying on cached linearization metadata. -/
private def derive (graph : Graph) (root name : String) : Nat → Except Error (GraphResult graph name)
  | 0 => .error (.cycle root)
  | fuel + 1 => do
    match found : graph.findNode? name with
    | none => throw (.unknownNode name)
    | some node =>
      let children ← node.parentOrders.flatten.mapM fun parent => do
        let child ← derive graph root parent fuel
        return (⟨parent, child⟩ : Sigma (GraphResult graph))
      let rows := children.map fun child =>
        (child.1, (child.2.output, child.2.mostSpecificTail))
      if names : rows.map Prod.fst = node.parentOrders.flatten then
        let orders := rows.map (fun row => row.2.1) ++ node.parentOrders
        let tails := rows.map (fun row => row.2.2)
        let certificate ← certifyNode name orders tails (longestTail tails)
        have parents : ∀ row ∈ rows, GraphTrace graph row.1 row.2.1 row.2.2 := by
          intro row present
          obtain ⟨child, _, same⟩ := List.mem_map.mp present
          subst row
          exact child.2.trace
        return ⟨certificate.output,
          if node.suffix then certificate.output else certificate.selection.output,
          .node found rows names parents certificate⟩
      else throw .inconsistentOrder

/-- The returned graph derivation is bound to the ordinary compiler's exact
successful result, not a caller-supplied candidate list or cache snapshot. -/
structure GraphCertified (graph : Graph) (root : String) where
  result : GraphResult graph root
  compiled : linearize graph root = .ok result.output

def GraphCertified.output (certificate : GraphCertified graph root) : List String :=
  certificate.result.output

theorem GraphCertified.nodup (certificate : GraphCertified graph root) :
    certificate.output.Nodup := certificate.result.trace.nodup

theorem GraphCertified.head (certificate : GraphCertified graph root) :
    certificate.output.head? = some root := certificate.result.trace.head

theorem GraphCertified.ancestor {ancestor : String} (certificate : GraphCertified graph root)
    (path : Ancestor graph ancestor root) :
    ∃ ancestorOutput ancestorTail, GraphTrace graph ancestor ancestorOutput ancestorTail ∧
      ancestorOutput.Sublist certificate.output := certificate.result.trace.ancestor path

theorem GraphCertified.unique (first second : GraphCertified graph root) :
    first.output = second.output := Except.ok.inj (first.compiled.symm.trans second.compiled)

theorem GraphCertified.covers (certificate : GraphCertified graph root) :
    item ∈ certificate.output ↔ Ancestor graph item root := certificate.result.trace.covers

theorem GraphCertified.local_order {node : Node} (certificate : GraphCertified graph root)
    (found : graph.findNode? root = some node) (member : order ∈ node.parentOrders) :
    order.Sublist certificate.output := certificate.result.trace.local_order found member

theorem GraphCertified.ancestor_suffix {ancestor : String} {node : Node}
    (certificate : GraphCertified graph root) (path : Ancestor graph ancestor root)
    (found : graph.findNode? ancestor = some node) (flag : node.suffix = true) :
    ∃ ancestorOutput ancestorTail, GraphTrace graph ancestor ancestorOutput ancestorTail ∧
      ancestorOutput.IsSuffix certificate.output := by
  obtain ⟨ancestorOutput, ancestorTail, ancestorTrace, inherited⟩ :=
    certificate.result.trace.ancestor_tail path
  have same := ancestorTrace.flagged found flag
  exact ⟨ancestorOutput, ancestorTail, ancestorTrace,
    by rw [← same]; exact inherited.trans certificate.result.trace.suffix⟩

/-- Produce an independently reconstructed graph certificate for the ordinary
compiler's result. Verification is opt-in and may repeat shared parent work. -/
def linearizeCertified (graph : Graph) (root : String) : Except Error (GraphCertified graph root) :=
  match compiled : linearize graph root with
  | .error error => .error error
  | .ok output => do
    let result ← derive graph root root graph.nodes.length
    if same : result.output = output then
      return ⟨result, by rw [same]; exact compiled⟩
    else throw .inconsistentOrder

end LeanPoo.C4
