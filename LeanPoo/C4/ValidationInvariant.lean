import LeanPoo.C4.ReachabilityInvariant

namespace LeanPoo.C4

/-- Successful name scan for the exact first validation loop. -/
def scanNames (nodes : List Node) (seen : Std.HashSet String) : Except Error (Std.HashSet String) :=
  forIn nodes seen fun node seen => do
    if seen.contains node.name then do
      throw (Error.duplicateNode node.name)
      pure (ForInStep.yield (seen.insert node.name))
    else pure (ForInStep.yield (seen.insert node.name))

private theorem scanNames_complete (unique : (nodes.map Node.name).Nodup)
    (fresh : ∀ node ∈ nodes, seen.contains node.name = false) :
    ∃ complete, scanNames nodes seen = .ok complete ∧
      ∀ name, complete.contains name = true ↔ name ∈ nodes.map Node.name ∨ seen.contains name = true := by
  induction nodes generalizing seen with
  | nil => exact ⟨seen, rfl, by simp⟩
  | cons node rest ih =>
    have distinct := List.nodup_cons.mp unique
    have absent := fresh node (by simp)
    have restFresh : ∀ next ∈ rest, (seen.insert node.name).contains next.name = false := by
      intro next member
      have different : node.name ≠ next.name := by
        intro same; exact distinct.1 (List.mem_map.mpr ⟨next, member, same.symm⟩)
      simp [Std.HashSet.contains_insert, different, fresh next (by simp [member])]
    obtain ⟨complete, scanned, membership⟩ := ih distinct.2 restFresh
    refine ⟨complete, ?_, ?_⟩
    · simpa only [scanNames, List.forIn_cons, absent, Bool.false_eq_true, ↓reduceIte,
        bind, Except.bind, pure, Except.pure] using scanned
    · intro name
      rw [membership]
      simp only [List.map_cons, List.mem_cons, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
      simp only [eq_comm (a := node.name) (b := name), or_assoc, or_left_comm]

private theorem forIn_unit_complete (items : List α) (action : α → Except Error (ForInStep PUnit))
    (success : ∀ item ∈ items, action item = .ok (.yield PUnit.unit)) :
    forIn items PUnit.unit (fun item _ => action item) = (Except.ok PUnit.unit : Except Error PUnit) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    have first := success item (by simp)
    have remaining := ih (fun next member => success next (by simp [member]))
    simpa only [List.forIn_cons, first, bind, Except.bind, pure, Except.pure] using remaining

/-- Actual validation succeeds for unique declaration names and complete
parent-name membership, without assuming either runtime loop succeeds. -/
theorem Graph.validate_complete {graph : Graph} (unique : (graph.nodes.map Node.name).Nodup)
    (closed : ∀ node ∈ graph.nodes, ∀ parent ∈ node.parentOrders.flatten,
      parent ∈ graph.nodes.map Node.name) : graph.validate = .ok () := by
  obtain ⟨seen, scanned, membership⟩ := scanNames_complete (seen := {}) unique (by simp)
  have names : ∀ name, seen.contains name = true ↔ name ∈ graph.nodes.map Node.name := by
    intro name; simpa using membership name
  have checked : (forIn graph.nodes PUnit.unit fun (node : Node) _ => do
      forIn node.parentOrders PUnit.unit fun order _ => do
        forIn order PUnit.unit fun parent _ => do
          if !seen.contains parent then do
            throw (Error.unknownNode parent)
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)
      pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Except Error PUnit) := by
    apply forIn_unit_complete
    intro node present
    have orders : (forIn node.parentOrders PUnit.unit fun order _ => do
        forIn order PUnit.unit fun parent _ => do
          if !seen.contains parent then do
            throw (Error.unknownNode parent)
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Except Error PUnit) := by
      apply forIn_unit_complete
      intro order localMember
      have inner : (forIn order PUnit.unit fun parent _ => do
          if !seen.contains parent then do
            throw (Error.unknownNode parent)
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)) = (Except.ok PUnit.unit : Except Error PUnit) := by
        apply forIn_unit_complete
        intro parent member
        have found := (names parent).mpr (closed node present parent
          (List.mem_flatten.mpr ⟨order, localMember, member⟩))
        simp [found, pure, Except.pure]
      rw [inner]
      rfl
    rw [orders]
    rfl
  unfold Graph.validate
  change (do
    let complete ← scanNames graph.nodes {}
    forIn graph.nodes PUnit.unit fun (node : Node) _ => do
      forIn node.parentOrders PUnit.unit fun order _ => do
        forIn order PUnit.unit fun parent _ => do
          if !complete.contains parent then do
            throw (Error.unknownNode parent)
            pure (ForInStep.yield PUnit.unit)
          else pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)
      pure (ForInStep.yield PUnit.unit)
    pure ()) = .ok ()
  rw [scanned]
  simp only [bind, Except.bind]
  simp only [bind, Except.bind] at checked
  rw [checked]
  rfl

end LeanPoo.C4

namespace LeanPoo.C4

private theorem unique_named_member {nodes : List Node} {first second : Node} (unique : (nodes.map Node.name).Nodup)
    (left : first ∈ nodes) (right : second ∈ nodes) (same : first.name = second.name) : first = second := by
  induction nodes with
  | nil => simp at left
  | cons node rest ih =>
    have distinct := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with own | later
    · subst first
      rcases List.mem_cons.mp right with own | later
      · exact own.symm
      · exact False.elim (distinct.1 (List.mem_map.mpr ⟨second, later, same.symm⟩))
    · rcases List.mem_cons.mp right with own | other
      · subst second
        exact False.elim (distinct.1 (List.mem_map.mpr ⟨first, later, same⟩))
      · exact ih distinct.2 later other

namespace LinearizeState

/-- Only reachable declarations must have unique names. Disconnected duplicate
or missing-parent declarations remain outside the runtime validation policy. -/
def ReachableUnique (graph : Graph) (root : String) : Prop :=
  ((reachableNodes graph root).map Node.name).Nodup

/-- A finite root derivation and reachable uniqueness identify every included
declaration with the first declaration used by the graph relation. -/
theorem reachable_declaration_lookup (unique : ReachableUnique graph root)
    (present : node ∈ reachableNodes graph root) : graph.findNode? node.name = some node := by
  obtain ⟨original, ancestor⟩ := reachableNodes_mem.mp present
  cases found : graph.findNode? node.name with
  | none =>
    have absent := List.find?_eq_none.mp found node original
    simp at absent
  | some first =>
    have included : first ∈ reachableNodes graph root := reachableNodes_mem.mpr
      ⟨List.mem_of_find?_eq_some found, by
        have same := beq_iff_eq.mp (List.find?_some
          (p := fun declaration : Node => declaration.name == node.name) found)
        simpa [same] using ancestor⟩
    have same := beq_iff_eq.mp (List.find?_some
      (p := fun declaration : Node => declaration.name == node.name) found)
    have identical := unique_named_member unique included present same
    exact congrArg some identical

/-- All parent names of included declarations have included declarations;
finite graph evidence derives this closure once reachable names are unique. -/
theorem reachable_declarations_closed (trace : GraphTrace graph root output tail)
    (unique : ReachableUnique graph root) :
    ∀ node ∈ reachableNodes graph root, ∀ parent ∈ node.parentOrders.flatten,
      parent ∈ (reachableNodes graph root).map Node.name := by
  intro node present parent edge
  have ancestor := (reachableNodes_mem.mp present).2
  have found := reachable_declaration_lookup unique present
  obtain ⟨_, _, nodeTrace, _⟩ := trace.ancestor ancestor
  obtain ⟨_, _, parentTrace, _⟩ := nodeTrace.parent found edge
  obtain ⟨declaration, original, same⟩ := parentTrace.declared
  have earlier : Ancestor graph parent root := (Ancestor.parent found edge Ancestor.self).trans ancestor
  exact List.mem_map.mpr ⟨declaration, reachableNodes_mem.mpr ⟨original, same ▸ earlier⟩, same⟩

/-- Actual validation success is derived, no longer an execution premise. -/
theorem reachable_validate_complete (trace : GraphTrace graph root output tail)
    (unique : ReachableUnique graph root) : (Graph.mk (reachableNodes graph root)).validate = .ok () :=
  Graph.validate_complete unique (reachable_declarations_closed trace unique)

theorem linearizeWith_unique_complete (trace : GraphTrace graph root output tail)
    (unique : ReachableUnique graph root) (checked : Bool) : linearizeWith graph root checked = .ok output :=
  linearizeWith_complete trace (reachable_validate_complete trace unique) checked

/-- Global declaration uniqueness is a sufficient, stronger condition. -/
theorem reachableUnique_of_global (unique : (graph.nodes.map Node.name).Nodup) : ReachableUnique graph root :=
  (List.Sublist.map Node.name (List.filter_sublist)).nodup unique

end LinearizeState

theorem linearize_unique_complete (trace : GraphTrace graph root output tail)
    (unique : LinearizeState.ReachableUnique graph root) : linearize graph root = .ok output :=
  LinearizeState.linearizeWith_unique_complete trace unique false

theorem linearizeChecked_unique_complete (trace : GraphTrace graph root output tail)
    (unique : LinearizeState.ReachableUnique graph root) : linearizeChecked graph root = .ok output :=
  LinearizeState.linearizeWith_unique_complete trace unique true

end LeanPoo.C4
