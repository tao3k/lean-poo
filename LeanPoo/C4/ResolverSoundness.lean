import LeanPoo.C4.NodeSoundness
import LeanPoo.C4.ReachabilityInvariant

namespace LeanPoo.C4.LinearizeState

/-- Recover metadata and cache growth from a successful parent loop. No
completion premise is required for unsuccessful parent executions. -/
theorem resolveParents_sound (valid : MetadataInvariant graph table)
    (step : ∀ parent ∈ names, ∀ before after, MetadataInvariant graph before →
      action parent before = .ok after → MetadataInvariant graph after ∧
        CacheGrowth before after allowed ∧ ∃ entry, lookup after parent = some entry)
    (success : resolveParents action names table = .ok ready) :
    MetadataInvariant graph ready ∧ CacheGrowth table ready allowed ∧
      ∀ parent ∈ names, ∃ entry, lookup ready parent = some entry := by
  induction names generalizing table with
  | nil =>
    have same : table = ready := Except.ok.inj success
    subst ready
    exact ⟨valid, CacheGrowth.refl _ _, by simp⟩
  | cons parent rest ih =>
    cases first : action parent table with
    | error error => simp [resolveParents, List.forIn_cons, first, bind, Except.bind] at success
    | ok middle =>
      have remaining : resolveParents action rest middle = .ok ready := by
        simpa only [resolveParents, List.forIn_cons, first, bind, Except.bind, pure, Except.pure] using success
      obtain ⟨validMiddle, firstGrowth, entry, cached⟩ := step parent (by simp) table middle valid first
      obtain ⟨validReady, restGrowth, available⟩ := ih validMiddle
        (fun name member => step name (by simp [member])) remaining
      refine ⟨validReady, firstGrowth.trans restGrowth, ?_⟩
      intro name member
      rcases List.mem_cons.mp member with same | member
      · subst name; exact ⟨entry, restGrowth.retains parent entry cached⟩
      · exact available name member

/-- Actual checked recursion preserves canonical graph metadata, retains old
entries, and introduces only ancestors of the requested node. -/
theorem resolveNode_checked_sound (valid : MetadataInvariant graph table)
    (success : resolveNode (nodeIndex graph) root name table true fuel = .ok ready) :
    MetadataInvariant graph ready ∧ CacheGrowth table ready (fun item => Ancestor graph item name) ∧
      ∃ entry, lookup ready name = some entry := by
  induction fuel generalizing name table ready with
  | zero =>
    cases cached : lookup table name with
    | none => simp [resolveNode, cached] at success
    | some entry =>
      have same : table = ready := by simpa [resolveNode, cached] using success
      subst ready; exact ⟨valid, CacheGrowth.refl _ _, entry, cached⟩
  | succ fuel ih =>
    cases cached : lookup table name with
    | some entry =>
      have same : table = ready := by simpa [resolveNode, cached, pure, Except.pure] using success
      subst ready; exact ⟨valid, CacheGrowth.refl _ _, entry, cached⟩
    | none =>
      cases indexed : (nodeIndex graph)[name]? with
      | none => simp [resolveNode, cached, Std.HashMap.get?_eq_getElem?, indexed] at success
      | some node =>
        have found : graph.findNode? name = some node := (nodeIndex_lookup graph name).symm.trans indexed
        have nameSame : node.name = name := (nodeIndex_declared indexed).2
        subst name
        have execution : (do
          let next ← resolveParents (fun parent ready => resolveNode (nodeIndex graph) root parent ready true fuel)
            (parents node) table
          let result ← computeNode next node true
          pure (next.insert node.name result)) = .ok ready := by
          simp only [resolveNode, cached, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
            Std.HashMap.get?_eq_getElem?, indexed] at success
          exact success
        cases parentsDone : resolveParents (fun parent ready =>
            resolveNode (nodeIndex graph) root parent ready true fuel) (parents node) table with
        | error error => simp [parentsDone, bind, Except.bind] at execution
        | ok next =>
          let allowed := fun item => ∃ parent ∈ parents node, Ancestor graph item parent
          have step : ∀ parent ∈ parents node, ∀ before after, MetadataInvariant graph before →
              resolveNode (nodeIndex graph) root parent before true fuel = .ok after →
              MetadataInvariant graph after ∧ CacheGrowth before after allowed ∧
                ∃ entry, lookup after parent = some entry := by
            intro parent member before after validBefore done
            obtain ⟨validAfter, growth, available⟩ := ih validBefore done
            exact ⟨validAfter, growth.weaken (fun _ path => ⟨parent, member, path⟩), available⟩
          obtain ⟨validNext, growth, _⟩ := resolveParents_sound valid step parentsDone
          cases computed : computeNode next node true with
          | error error => simp [parentsDone, computed, bind, Except.bind] at execution
          | ok result =>
            have trace := computeNode_checked_graph_sound validNext found computed
            have excluded : ¬ allowed node.name := by
              rintro ⟨parent, member, path⟩
              obtain ⟨parentOutput, parentTail, parentTrace, included⟩ :=
                trace.parent_ancestry found (parents_mem.mp member)
              exact trace.root_not_tail (included.subset (parentTrace.covers.mpr path))
            have fresh := growth.fresh cached excluded
            have inserted := computeNode_checked_insert_sound validNext found fresh computed
            have same : next.insert node.name result = ready := by
              simpa [parentsDone, computed, bind, Except.bind, pure, Except.pure] using execution
            subst ready
            refine ⟨inserted, ?_, result, by simp [lookup_insert]⟩
            exact (growth.weaken (by
              intro item path
              obtain ⟨parent, member, earlier⟩ := path
              exact Ancestor.parent found (parents_mem.mp member) earlier)).trans
                (CacheGrowth.insert fresh Ancestor.self)

/-- A successful checked resolver yields an original graph trace for its
actual cached result, starting from any canonical cache. -/
theorem resolveNode_checked_graph_sound (valid : MetadataInvariant graph table)
    (success : resolveNode (nodeIndex graph) root name table true fuel = .ok ready) :
    ∃ entry, lookup ready name = some entry ∧
      GraphTrace graph name entry.precedence (selectedTail ready entry.mostSpecificSuffix) := by
  obtain ⟨validReady, _, entry, cached⟩ := resolveNode_checked_sound valid success
  exact ⟨entry, cached, validReady.tail name entry cached⟩

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4

/-- Successful checked compilation is sound on the original graph, with no
caller trace, uniqueness, validation, or cache invariant premise. -/
theorem linearizeChecked_graph_sound (success : linearizeChecked graph root = .ok output) :
    ∃ tail, GraphTrace graph root output tail := by
  unfold linearizeChecked LinearizeState.linearizeWith at success
  cases indexed : (LinearizeState.nodeIndex graph)[root]? with
  | none =>
    simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_none, ↓reduceIte,
      bind, Except.bind] at success
    cases success
  | some node =>
    simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_some,
      Bool.false_eq_true, ↓reduceIte] at success
    generalize declarations : graph.nodes.filter (fun node =>
      ((LinearizeState.reachable graph (LinearizeState.nodeIndex graph) root).foldl
        (fun seen name => seen.insert name) ({} : Std.HashSet String)).contains node.name) = nodes at success
    cases validated : (Graph.mk nodes).validate with
    | error error => simp [validated, bind, Except.bind] at success
    | ok acceptedUnit =>
      cases computed : LinearizeState.resolveNode (LinearizeState.nodeIndex graph) root root {} true nodes.length with
      | error error => simp [validated, computed, bind, Except.bind] at success
      | ok table =>
        obtain ⟨entry, cached, trace⟩ := LinearizeState.resolveNode_checked_graph_sound
          (LinearizeState.MetadataInvariant.empty graph) computed
        have same : entry.precedence = output := by
          simpa [validated, computed, bind, Except.bind, cached, pure, Except.pure] using success
        exact ⟨_, same ▸ trace⟩

end LeanPoo.C4
