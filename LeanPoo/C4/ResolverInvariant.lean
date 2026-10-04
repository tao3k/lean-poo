import LeanPoo.C4.GraphComputeInvariant

namespace LeanPoo.C4.LinearizeState

/-- Resolution retains all old cache entries and restricts new keys to an
explicit set. This also supplies freshness for the next node insertion. -/
structure CacheGrowth (before after : Table) (allowed : String → Prop) : Prop where
  retains : ∀ name entry, lookup before name = some entry → lookup after name = some entry
  introduced : ∀ name entry, lookup after name = some entry → lookup before name = none → allowed name

theorem CacheGrowth.refl (table : Table) (allowed : String → Prop) : CacheGrowth table table allowed := by
  refine ⟨fun _ _ found => found, ?_⟩
  intro name entry found absent; rw [absent] at found; cases found

theorem CacheGrowth.trans (first : CacheGrowth before middle allowed)
    (second : CacheGrowth middle after allowed) : CacheGrowth before after allowed := by
  refine ⟨fun name entry found => second.retains name entry (first.retains name entry found), ?_⟩
  intro name entry found absent
  cases cached : lookup middle name with
  | none => exact second.introduced name entry found cached
  | some old => exact first.introduced name old cached absent

theorem CacheGrowth.weaken (growth : CacheGrowth before after allowed)
    (subset : ∀ name, allowed name → larger name) : CacheGrowth before after larger :=
  ⟨growth.retains, fun name entry found absent => subset name (growth.introduced name entry found absent)⟩

theorem CacheGrowth.fresh (growth : CacheGrowth before after allowed)
    (absent : lookup before name = none) (excluded : ¬ allowed name) : lookup after name = none := by
  cases found : lookup after name with
  | none => rfl
  | some entry => exact False.elim (excluded (growth.introduced name entry found absent))

theorem CacheGrowth.insert (fresh : lookup table name = none) (permitted : allowed name) :
    CacheGrowth table (table.insert name entry) allowed := by
  refine ⟨fun _ _ found => fresh_insert_retains fresh found, ?_⟩
  intro query cached found absent
  by_cases same : name = query
  · simpa [same] using permitted
  · simp [lookup_insert, same, absent] at found

/-- A proof-facing name for the existing imperative parent loop. -/
def resolveParents (action : String → Table → Except Error Table) (names : List String) (table : Table) :
    Except Error Table :=
  forIn names table fun parent ready => do
    let next ← action parent ready
    pure (.yield next)

/-- Sequential parent resolution preserves metadata, accumulated cache entries,
and successful lookup of every parent, including repeated parent names. -/
theorem resolveParents_complete (valid : MetadataInvariant graph table)
    (step : ∀ parent ∈ names, ∀ ready, MetadataInvariant graph ready →
      ∃ next, action parent ready = .ok next ∧ MetadataInvariant graph next ∧
        CacheGrowth ready next allowed ∧ ∃ entry, lookup next parent = some entry) :
    ∃ ready, resolveParents action names table = .ok ready ∧ MetadataInvariant graph ready ∧
      CacheGrowth table ready allowed ∧ ∀ parent ∈ names, ∃ entry, lookup ready parent = some entry := by
  induction names generalizing table with
  | nil => exact ⟨table, rfl, valid, CacheGrowth.refl _ _, by simp⟩
  | cons parent rest ih =>
    obtain ⟨middle, first, validMiddle, firstGrowth, entry, cached⟩ :=
      step parent (by simp) table valid
    obtain ⟨ready, remaining, validReady, restGrowth, available⟩ :=
      ih validMiddle (fun name member => step name (by simp [member]))
    refine ⟨ready, ?_, validReady, firstGrowth.trans restGrowth, ?_⟩
    · simpa only [resolveParents, List.forIn_cons, first, Except.bind, Except.pure, pure, bind] using remaining
    · intro name member
      rcases List.mem_cons.mp member with same | member
      · subst name; exact ⟨entry, restGrowth.retains parent entry cached⟩
      · exact available name member

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4

/-- Direct parent outputs lie entirely in the child's ancestry, excluding its
fresh head. This is stronger than preservation in the full child output. -/
theorem GraphTrace.parent_ancestry {node : Node} {parent : String} (trace : GraphTrace graph name output tail)
    (found : graph.findNode? name = some node) (member : parent ∈ node.parentOrders.flatten) :
    ∃ parentOutput parentTail, GraphTrace graph parent parentOutput parentTail ∧
      parentOutput.Sublist output.tail := by
  cases trace with
  | node actual rows names parentTraces certificate =>
    have same := Option.some.inj (actual.symm.trans found)
    subst node
    rw [← names] at member
    obtain ⟨row, present, rowName⟩ := List.mem_map.mp member
    refine ⟨row.2.1, row.2.2, by simpa [rowName] using parentTraces row present, ?_⟩
    exact certificate.ancestry.preserves (List.mem_append_left _ (List.mem_map.mpr ⟨row, present, rfl⟩))

theorem GraphTrace.root_not_tail (trace : GraphTrace graph name output tail) : name ∉ output.tail := by
  cases trace with
  | node _ _ _ _ certificate => exact certificate.fresh

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

/-- Cache hits bypass recursion even when no fuel remains. -/
theorem resolveNode_cached (cached : lookup table name = some entry) :
    resolveNode index root name table checked fuel = .ok table := by
  cases fuel <;> simp [resolveNode, cached, pure, Except.pure]

private theorem cached_receipt (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (cached : lookup table name = some entry) :
    ∃ ready, resolveNode (nodeIndex graph) root name table checked fuel = .ok ready ∧
      MetadataInvariant graph ready ∧ CacheGrowth table ready (fun item => item ∈ output) ∧
      ∃ result, lookup ready name = some result ∧ result.precedence = output := by
  exact ⟨table, resolveNode_cached cached, valid, CacheGrowth.refl _ _, entry, cached,
    ((valid.tail name entry cached).unique trace).1⟩

/-- The actual recursive resolver completes a finite graph derivation with a
precedence-length fuel bound, preserves strong metadata and old entries, and
adds only names in that derivation. Both runtime modes satisfy the same law. -/
theorem resolveNode_complete (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (budget : output.length ≤ fuel) :
    ∃ ready, resolveNode (nodeIndex graph) root name table checked fuel = .ok ready ∧
      MetadataInvariant graph ready ∧ CacheGrowth table ready (fun item => item ∈ output) ∧
      ∃ result, lookup ready name = some result ∧ result.precedence = output := by
  induction fuel generalizing name output tail table with
  | zero =>
    cases cached : lookup table name with
    | some entry => exact cached_receipt valid trace cached
    | none =>
      have nonempty := List.length_pos_of_mem trace.root_mem
      omega
  | succ fuel ih =>
    cases cached : lookup table name with
    | some entry => exact cached_receipt valid trace cached
    | none =>
      have declaration : ∃ node, graph.findNode? name = some node ∧ node.name = name := by
        cases trace with
        | node found _ _ _ _ =>
          exact ⟨_, found, beq_iff_eq.mp (List.find?_some
            (p := fun declaration : Node => declaration.name == name) found)⟩
      obtain ⟨node, found, nameSame⟩ := declaration
      subst name
      have step : ∀ parent ∈ parents node, ∀ ready, MetadataInvariant graph ready →
          ∃ next, resolveNode (nodeIndex graph) root parent ready checked fuel = .ok next ∧
            MetadataInvariant graph next ∧ CacheGrowth ready next (fun item => item ∈ output.tail) ∧
            ∃ entry, lookup next parent = some entry := by
        intro parent member ready validReady
        obtain ⟨parentOutput, parentTail, parentTrace, subset⟩ :=
          trace.parent_ancestry found (parents_mem.mp member)
        have lengthBound := subset.length_le
        have nonempty := List.length_pos_of_mem trace.root_mem
        simp only [List.length_tail] at lengthBound
        have parentBudget : parentOutput.length ≤ fuel := by omega
        obtain ⟨next, computed, validNext, growth, entry, cachedParent, _⟩ :=
          ih validReady parentTrace parentBudget
        exact ⟨next, computed, validNext, growth.weaken (fun _ member => subset.subset member), entry, cachedParent⟩
      obtain ⟨ready, parentsDone, validReady, growth, available⟩ := resolveParents_complete valid step
      have fresh : lookup ready node.name = none := growth.fresh cached trace.root_not_tail
      obtain ⟨entries, collected⟩ := collectParents_success_iff.mpr
        (fun parent member => available parent (parents_mem.mpr member))
      obtain ⟨result, computed, same, inserted⟩ :=
        computeNode_metadata_insert validReady trace found fresh collected checked
      have afterGrowth : CacheGrowth table (ready.insert node.name result) (fun item => item ∈ output) :=
        (growth.weaken (fun _ member => List.mem_of_mem_tail member)).trans
          (CacheGrowth.insert fresh trace.root_mem)
      refine ⟨ready.insert node.name result, ?_, inserted, afterGrowth, result, ?_, same⟩
      · have indexed : (nodeIndex graph).get? node.name = some node :=
          (nodeIndex_lookup graph node.name).trans found
        simp only [resolveNode, cached, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, indexed]
        change (do
          let next ← resolveParents (fun parent ready =>
            resolveNode (nodeIndex graph) root parent ready checked fuel) (parents node) table
          let entry ← computeNode next node checked
          pure (next.insert node.name entry)) = .ok (ready.insert node.name result)
        rw [parentsDone]
        simp only [bind, Except.bind, computed, pure, Except.pure]
      · simp [lookup_insert]

/-- Original graph declaration count is sufficient resolver fuel. This starts
from the empty strong invariant and proves actual root cache population. -/
theorem resolveNode_graph_complete (trace : GraphTrace graph root output tail) (checked : Bool) :
    ∃ table, resolveNode (nodeIndex graph) root root {} checked graph.nodes.length = .ok table ∧
      MetadataInvariant graph table ∧ ∃ entry, lookup table root = some entry ∧ entry.precedence = output := by
  obtain ⟨table, computed, valid, _, result⟩ :=
    resolveNode_complete (MetadataInvariant.empty graph) trace trace.length_bound
  exact ⟨table, computed, valid, result⟩

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

/-- Exact observable root precedence, without exposing the existential cache. -/
theorem resolveNode_output (valid : MetadataInvariant graph table)
    (trace : GraphTrace graph name output tail) (budget : output.length ≤ fuel) :
    ((resolveNode (nodeIndex graph) root name table checked fuel).toOption.bind
      (fun ready => lookup ready name)).map (·.precedence) = some output := by
  obtain ⟨ready, computed, _, _, entry, cached, same⟩ := resolveNode_complete (root := root) (checked := checked) valid trace budget
  simp [computed, Except.toOption, cached, same]

end LeanPoo.C4.LinearizeState
