import LeanPoo.C4.ValidationInvariant

namespace LeanPoo.C4.LinearizeState

/-- A successful suffix read returns the actual cache projection. -/
theorem readSuffix_sound (success : readSuffix table chosen = .ok tail) :
    tail = selectedTail table chosen := by
  cases chosen with
  | none => simpa [readSuffix, selectedTail, pure, Except.pure] using success.symm
  | some name =>
    cases cached : lookup table name with
    | none => simp [readSuffix, cached] at success
    | some entry => simpa [readSuffix, selectedTail, cached, pure, Except.pure] using success.symm

/-- Successful checked execution itself supplies normalized node evidence and
binds it to the exact output, inherited link, and most-specific link. -/
theorem computeNode_checked_evidence (success : computeNode table node true = .ok result) :
    ∃ entries chosen tails, ∃ certificate : NodeCertified node.name
      (entries.map (·.precedence) ++ MergeState.pending node.parentOrders) tails,
      collectParents table (parents node) = .ok entries ∧
      selectSuffix table (entries.map (·.mostSpecificSuffix)) none = .ok chosen ∧
      collectSuffixTails table (entries.map (·.mostSpecificSuffix)) = .ok tails ∧
      certificate.selection.output = selectedTail table chosen ∧
      result = {
        precedence := certificate.output
        inheritedSuffix := chosen
        mostSpecificSuffix := if node.suffix then some node.name else chosen } := by
  unfold computeNode at success
  cases collected : collectParents table (parents node) with
  | error error => simp [collected, bind, Except.bind] at success
  | ok entries =>
    cases selected : selectSuffix table (entries.map (·.mostSpecificSuffix)) none with
    | error error => simp [collected, selected, bind, Except.bind] at success
    | ok chosen =>
      cases read : readSuffix table chosen with
      | error error => simp [collected, selected, read, bind, Except.bind] at success
      | ok tail =>
        have tailSame := readSuffix_sound read
        simp only [collected, selected, read, bind, Except.bind] at success
        split at success
        · simp at success
        · cases tailsFound : collectSuffixTails table (entries.map (·.mostSpecificSuffix)) with
          | error error => simp [tailsFound] at success
          | ok tails =>
            cases certified : certifyNode node.name
                (entries.map (·.precedence) ++ node.parentOrders.filter (fun order => !order.isEmpty)) tails tail with
            | error error => simp [tailsFound, certified] at success
            | ok certificate =>
              have claimed := certifyNode_claimed certified
              refine ⟨entries, chosen, tails, certificate, rfl, selected, tailsFound,
                claimed.trans tailSame, ?_⟩
              simp only [tailsFound, certified, pure, Except.pure, ↓reduceIte] at success
              exact Except.ok.inj success.symm

/-- Every accepted checked node is duplicate-free, preserves all actual parent
and nonempty local orders, and has its selected tail as a literal suffix. -/
theorem computeNode_checked_laws (success : computeNode table node true = .ok result) :
    result.precedence.Nodup ∧ result.precedence.head? = some node.name ∧
      (selectedTail table result.inheritedSuffix).IsSuffix result.precedence ∧
      ∃ entries, collectParents table (parents node) = .ok entries ∧
        ∀ order ∈ entries.map (·.precedence) ++ MergeState.pending node.parentOrders,
          order.Sublist result.precedence := by
  obtain ⟨entries, chosen, tails, certificate, collected, _, _, claimed, same⟩ :=
    computeNode_checked_evidence success
  subst result
  exact ⟨certificate.nodup, certificate.head, claimed ▸ certificate.inherited_suffix,
    entries, collected, fun order member => certificate.preserves member⟩

/-- Checked acceptance implies ordinary acceptance with the exact same node
result. This does not require a graph derivation or cache invariant. -/
theorem computeNode_checked_ordinary (success : computeNode table node true = .ok result) :
    computeNode table node false = .ok result := by
  obtain ⟨entries, chosen, tails, certificate, collected, selected, _, claimed, same⟩ :=
    computeNode_checked_evidence success
  have raw := MergeState.merge_complete certificate.ancestry.trace
  have merged : merge
      (entries.map (fun entry => withoutTail entry.precedence (selectedTail table chosen)) ++
        (MergeState.pending node.parentOrders).map (fun order => withoutTail order (selectedTail table chosen))) =
      .ok certificate.ancestry.front := by
    simpa only [claimed, List.map_append, List.map_map, Function.comp_def] using raw
  have read : readSuffix table chosen = .ok (selectedTail table chosen) := by
    cases available : readSuffix table chosen with
    | error error =>
      unfold computeNode at success
      simp [collected, selected, available, bind, Except.bind] at success
    | ok tail => rw [← readSuffix_sound available]
  have accepted : (MergeState.pending node.parentOrders).all
      (fun order => respectsSuffixTail order (selectedTail table chosen)) = true := by
    apply List.all_eq_true.mpr
    intro order member
    rw [← claimed]
    exact respectsSuffixTail_complete
      (certificate.ancestry.compatible order (List.mem_append_right _ member)) certificate.tailUnique
  subst result
  simp only [computeNode, collected, selected, read, show node.parentOrders.filter (fun order => !order.isEmpty) =
    MergeState.pending node.parentOrders from rfl, accepted, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, merged, bind, Except.bind, pure, Except.pure, NodeCertified.output,
    SuffixCertified.output, claimed]

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

private theorem resolveParents_transfer
    (transfer : ∀ parent ready next, first parent ready = .ok next → second parent ready = .ok next)
    (success : resolveParents first names table = .ok ready) : resolveParents second names table = .ok ready := by
  induction names generalizing table with
  | nil => exact success
  | cons parent rest ih =>
    cases step : first parent table with
    | error error => simp [resolveParents, List.forIn_cons, step, bind, Except.bind] at success
    | ok next =>
      have other := transfer parent table next step
      simp only [resolveParents, List.forIn_cons, step, bind, Except.bind, pure, Except.pure] at success
      have tailSuccess : resolveParents first rest next = .ok ready := success
      have transferred := ih tailSuccess
      simpa only [resolveParents, List.forIn_cons, other, bind, Except.bind, pure, Except.pure] using transferred

/-- Successful checked recursion is simulated by ordinary recursion with the
same complete cache, including arbitrary starting tables and fuel budgets. -/
theorem resolveNode_checked_ordinary (success : resolveNode index root name table true fuel = .ok ready) :
    resolveNode index root name table false fuel = .ok ready := by
  induction fuel generalizing name table ready with
  | zero => exact success
  | succ fuel ih =>
    by_cases hit : (lookup table name).isSome = true
    · simpa only [resolveNode, hit, ↓reduceIte, pure, Except.pure] using success
    · cases found : index[name]? with
      | none => simp only [resolveNode, hit, Bool.false_eq_true, ↓reduceIte, Std.HashMap.get?_eq_getElem?, found] at success
                cases success
      | some node =>
        have execution : (do
          let next ← resolveParents (fun parent ready => resolveNode index root parent ready true fuel) (parents node) table
          let result ← computeNode next node true
          pure (next.insert name result)) = .ok ready := by
            simp only [resolveNode, hit, Bool.false_eq_true, ↓reduceIte, Std.HashMap.get?_eq_getElem?, found] at success
            exact success
        cases parentsDone : resolveParents (fun parent ready => resolveNode index root parent ready true fuel) (parents node) table with
        | error error => simp [parentsDone, bind, Except.bind] at execution
        | ok next =>
          have parentsOther := resolveParents_transfer (fun _ _ _ success => ih success) parentsDone
          cases computed : computeNode next node true with
          | error error => simp [parentsDone, computed, bind, Except.bind] at execution
          | ok result =>
            have ordinary := computeNode_checked_ordinary computed
            have identical : next.insert name result = ready := by
              simpa [parentsDone, computed, bind, Except.bind, pure, Except.pure] using execution
            simp only [resolveNode, hit, Bool.false_eq_true, ↓reduceIte, Std.HashMap.get?_eq_getElem?, found]
            change (do
              let next ← resolveParents (fun parent ready => resolveNode index root parent ready false fuel) (parents node) table
              let result ← computeNode next node false
              pure (next.insert name result)) = .ok ready
            simp only [parentsOther, ordinary, bind, Except.bind, pure, Except.pure, identical]

/-- Checked top-level acceptance implies ordinary acceptance with exact output.
No finite graph evidence or name-uniqueness premise is required. -/
theorem linearizeChecked_ordinary (success : linearizeChecked graph root = .ok output) :
    linearize graph root = .ok output := by
  unfold linearizeChecked linearize LinearizeState.linearizeWith at *
  cases indexed : (nodeIndex graph)[root]? with
  | none => simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_none, ↓reduceIte, bind, Except.bind] at success
            cases success
  | some node =>
    simp only [Std.HashMap.get?_eq_getElem?, indexed, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at *
    generalize declarations : graph.nodes.filter (fun node =>
      ((reachable graph (nodeIndex graph) root).foldl (fun seen name => seen.insert name)
        ({} : Std.HashSet String)).contains node.name) = nodes at *
    cases validated : (Graph.mk nodes).validate with
    | error error => simp [validated, bind, Except.bind] at success
    | ok acceptedUnit =>
      cases computed : resolveNode (nodeIndex graph) root root {} true nodes.length with
      | error error => simp [validated, computed, bind, Except.bind] at success
      | ok table =>
        have ordinary := resolveNode_checked_ordinary computed
        simp only [validated, computed, bind, Except.bind] at success
        simp only [ordinary, bind, Except.bind]
        exact success

end LeanPoo.C4.LinearizeState
