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

theorem GraphTrace.parent_budget {node : Node} {parent : String}
    (trace : GraphTrace graph root output tail)
    (found : graph.findNode? root = some node) (member : parent ∈ node.parentOrders.flatten) :
    ∃ parentOutput parentTail, GraphTrace graph parent parentOutput parentTail ∧
      parentOutput.length < output.length := by
  cases trace with
  | node actual rows names parents certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    rw [← names] at member
    obtain ⟨row, present, name⟩ := List.mem_map.mp member
    refine ⟨row.2.1, row.2.2, ?_, ?_⟩
    · simpa [name] using parents row present
    · have kept := certificate.ancestry.preserves
        (List.mem_append_left _ (List.mem_map.mpr ⟨row, present, rfl⟩))
      exact Nat.lt_of_le_of_lt kept.length_le (Nat.lt_succ_self _)

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

/-- Every reachable ancestor's original local order is retained in the root
output, including unflagged ancestors and repeated declarations. -/
theorem GraphTrace.ancestor_local_order {ancestor : String} {node : Node} {order : List String}
    (trace : GraphTrace graph root output tail)
    (path : Ancestor graph ancestor root) (found : graph.findNode? ancestor = some node)
    (member : order ∈ node.parentOrders) : order.Sublist output := by
  obtain ⟨_, _, ancestorTrace, kept⟩ := trace.ancestor path
  exact (ancestorTrace.local_order found member).trans kept

theorem GraphTrace.root_mem (trace : GraphTrace graph root output tail) : root ∈ output := by
  cases trace with
  | node _ _ _ _ certificate => simp [NodeCertified.output]

theorem GraphTrace.declared (trace : GraphTrace graph root output tail) :
    ∃ declaration ∈ graph.nodes, declaration.name = root := by
  cases trace with
  | node found rows names parents certificate =>
    have selected := List.find?_some (p := fun declaration : Node => declaration.name == root) found
    exact ⟨_, List.mem_of_find?_eq_some found, beq_iff_eq.mp selected⟩

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

/-- Graph-derived output size is bounded by the number of original declarations. -/
theorem GraphTrace.length_bound (trace : GraphTrace graph root output tail) :
    output.length ≤ graph.nodes.length := by
  have bound : output.length ≤ (graph.nodes.map Node.name).length :=
    trace.nodup.length_le_of_subset (by
      intro item member
      obtain ⟨ancestorOutput, ancestorTail, ancestorTrace, _⟩ := trace.ancestor (trace.covers.mp member)
      obtain ⟨declaration, present, same⟩ := ancestorTrace.declared
      exact List.mem_map.mpr ⟨declaration, present, same⟩)
  simpa using bound

private def longestTail (tails : List (List String)) : List String :=
  tails.foldl (fun current next => if current.length < next.length then next else current) []

private theorem longestTail_fold (target : List String) (tails : List (List String))
    (current : List String) (initial : current.IsSuffix target)
    (contained : ∀ tail ∈ tails, tail.IsSuffix target)
    (chosen : current = target ∨ target ∈ tails) :
    tails.foldl (fun current next => if current.length < next.length then next else current) current = target := by
  induction tails generalizing current with
  | nil => simpa using chosen
  | cons next rest ih =>
    have nextSuffix := contained next (by simp)
    have restSuffix : ∀ tail ∈ rest, tail.IsSuffix target :=
      fun tail member => contained tail (by simp [member])
    simp only [List.foldl_cons]
    split
    · rename_i longer
      apply ih next nextSuffix restSuffix
      rcases chosen with same | member
      · subst current
        have bound := nextSuffix.length_le
        omega
      · rcases List.mem_cons.mp member with same | member
        · exact .inl same.symm
        · exact .inr member
    · rename_i shorter
      apply ih current initial restSuffix
      rcases chosen with same | member
      · exact .inl same
      · rcases List.mem_cons.mp member with same | member
        · subst next
          exact .inl (initial.eq_of_length_le (by omega))
        · exact .inr member

private theorem longestTail_complete (certificate : TailCertified tails) :
    longestTail tails = certificate.output := by
  rcases certificate.chosen with ⟨empty, same⟩ | member
  · simp [longestTail, empty, same]
  · exact longestTail_fold certificate.output tails [] List.nil_suffix
      certificate.containsTail (.inr member)

private def resultRow (child : Sigma (GraphResult graph)) :
    String × (List String × List String) :=
  (child.1, (child.2.output, child.2.mostSpecificTail))

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
      let rows := children.map resultRow
      if names : rows.map Prod.fst = node.parentOrders.flatten then
        let orders := rows.map (fun row => row.2.1) ++ node.parentOrders
        let tails := rows.map (fun row => row.2.2)
        let certificate ← certifyNodeReference name orders tails (longestTail tails)
        have parents : ∀ row ∈ rows, GraphTrace graph row.1 row.2.1 row.2.2 := by
          intro row present
          obtain ⟨child, _, same⟩ := List.mem_map.mp present
          subst row
          exact child.2.trace
        return ⟨certificate.output,
          if node.suffix then certificate.output else certificate.selection.output,
          .node found rows names parents certificate⟩
      else throw .inconsistentOrder

private theorem derive_rows (rows : List (String × (List String × List String)))
    (ready : ∀ row ∈ rows, ∃ child : GraphResult graph row.1,
      derive graph root row.1 fuel = .ok child ∧
      child.output = row.2.1 ∧ child.mostSpecificTail = row.2.2) :
    ∃ children : List (Sigma (GraphResult graph)),
      (rows.map Prod.fst).mapM (fun parent => do
        let child ← derive graph root parent fuel
        return (⟨parent, child⟩ : Sigma (GraphResult graph))) = .ok children ∧
      children.map resultRow = rows := by
  induction rows with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons row rows ih =>
    obtain ⟨child, success, output, tail⟩ := ready row (by simp)
    obtain ⟨children, successes, same⟩ := ih (fun other member => ready other (by simp [member]))
    refine ⟨⟨row.1, child⟩ :: children, ?_, ?_⟩
    · rw [List.map_cons, List.mapM_cons, successes, success]
      rfl
    · simp [resultRow, same, output, tail]

private theorem derive_complete (trace : GraphTrace graph name output tail)
    (enough : output.length ≤ fuel) :
    ∃ result, derive graph root name fuel = .ok result ∧
      result.output = output ∧ result.mostSpecificTail = tail := by
  induction trace generalizing fuel with
  | node found rows names parents certificate ih =>
    cases fuel with
    | zero => simp [NodeCertified.output] at enough
    | succ fuel =>
      have ready : ∀ row ∈ rows, ∃ child : GraphResult graph row.1,
          derive graph root row.1 fuel = .ok child ∧
          child.output = row.2.1 ∧ child.mostSpecificTail = row.2.2 := by
        intro row member
        have kept := certificate.ancestry.preserves
          (List.mem_append_left _ (List.mem_map.mpr ⟨row, member, rfl⟩))
        apply ih row member
        have bound : certificate.ancestry.output.length ≤ fuel := Nat.le_of_succ_le_succ enough
        exact Nat.le_trans kept.length_le bound
      obtain ⟨children, successes, same⟩ := derive_rows rows ready
      rw [names] at successes
      subst rows
      obtain ⟨result, success, outputEq, tailEq⟩ := certifyNodeReference_complete certificate
      refine ⟨⟨result.output, if _ then result.output else result.selection.output,
        .node found (children.map resultRow) names parents result⟩, ?_, outputEq, ?_⟩
      · simp only [derive]
        split
        · rename_i missing
          rw [missing] at found
          cases found
        · rename_i actual selected
          have identical := Option.some.inj (selected.symm.trans found)
          subst actual
          rw [successes]
          simp only [bind, Except.bind, pure, Except.pure,
            dite_eq_left names, longestTail_complete certificate.selection]
          simp only [success]
      · simp [outputEq, tailEq]

/-- Complete independent reconstruction with the original declaration count
as its budget. It does not call the ordinary compiler. -/
def reconstruct (graph : Graph) (root : String) : Except Error (GraphResult graph root) :=
  derive graph root root graph.nodes.length

theorem reconstruct_complete (trace : GraphTrace graph root output tail) :
    ∃ result, reconstruct graph root = .ok result ∧
      result.output = output ∧ result.mostSpecificTail = tail :=
  derive_complete trace trace.length_bound

/-- Reconstruction succeeds exactly for roots admitting a finite derivation. -/
theorem reconstruct_success_iff :
    (reconstruct graph root).toOption.isSome = true ↔
      ∃ output tail, GraphTrace graph root output tail := by
  constructor
  · intro success
    cases result : reconstruct graph root with
    | error error => simp [result, Except.toOption] at success
    | ok certificate => exact ⟨certificate.output, certificate.mostSpecificTail, certificate.trace⟩
  · rintro ⟨output, tail, trace⟩
    obtain ⟨result, success, _, _⟩ := reconstruct_complete trace
    simp [success, Except.toOption]

/-- Both complete precedence and most-specific tail are determined by the
original graph, independently of the ordinary compiler's result. -/
theorem GraphTrace.unique (first : GraphTrace graph root output₁ tail₁)
    (second : GraphTrace graph root output₂ tail₂) : output₁ = output₂ ∧ tail₁ = tail₂ := by
  obtain ⟨one, success₁, output₁Eq, tail₁Eq⟩ := reconstruct_complete first
  obtain ⟨two, success₂, output₂Eq, tail₂Eq⟩ := reconstruct_complete second
  have same := Except.ok.inj (success₁.symm.trans success₂)
  subst two
  exact ⟨output₁Eq.symm.trans output₂Eq, tail₁Eq.symm.trans tail₂Eq⟩

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

theorem GraphCertified.length_bound (certificate : GraphCertified graph root) :
    certificate.output.length ≤ graph.nodes.length := certificate.result.trace.length_bound

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
    let result ← reconstruct graph root
    if same : result.output = output then
      return ⟨result, by rw [same]; exact compiled⟩
    else throw .inconsistentOrder

/-- Once the ordinary compiler returns a derivable result, the public
certificate path cannot fail during reconstruction or output comparison. -/
theorem linearizeCertified_complete (compiled : linearize graph root = .ok output)
    (trace : GraphTrace graph root output tail) :
    ∃ certificate, linearizeCertified graph root = .ok certificate ∧
      certificate.output = output := by
  obtain ⟨result, success, same, _⟩ := reconstruct_complete trace
  refine ⟨⟨result, by rw [same]; exact compiled⟩, ?_, same⟩
  simp only [linearizeCertified]
  split
  · rename_i failed
    rw [failed] at compiled
    cases compiled
  · rename_i actual returned
    have identical := Except.ok.inj (returned.symm.trans compiled)
    subst actual
    rw [success]
    simp [bind, Except.bind, same, pure, Except.pure]

end LeanPoo.C4
