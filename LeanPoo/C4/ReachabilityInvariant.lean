import LeanPoo.C4.ResolverInvariant
import Std.Data.HashSet.Lemmas
import Init.Data.Range.Lemmas

namespace LeanPoo.C4.LinearizeState

abbrev ReachState := List String × Std.HashSet String × List String

/-- Proof model of one iteration of the existing breadth-first loop. -/
def reachStep (index : Std.HashMap String Node) : ReachState → ReachState
  | ([], seen, reversed) => ([], seen, reversed)
  | (name :: rest, seen, reversed) =>
    if !seen.contains name then
      match index.get? name with
      | some node => (rest ++ parents node, seen.insert name, name :: reversed)
      | none => (rest, seen.insert name, name :: reversed)
    else (rest, seen, reversed)

def reachWalk (index : Std.HashMap String Node) : Nat → ReachState → ReachState
  | 0, state => state
  | fuel + 1, state => match state.1 with
    | [] => state
    | _ :: _ => reachWalk index fuel (reachStep index state)

private def reachBody (index : Std.HashMap String Node) (_ : Nat) (state : ReachState) : Id (ForInStep ReachState) :=
  match state.1 with
  | [] => pure (.done (state.1, state.2.1, state.2.2))
  | name :: rest =>
    if !state.2.1.contains name then
      match index.get? name with
      | some node => pure (.yield (rest ++ parents node, state.2.1.insert name, name :: state.2.2))
      | _ => pure (.yield (rest, state.2.1.insert name, name :: state.2.2))
    else pure (.yield (rest, state.2.1, state.2.2))

private theorem reach_loop (ticks : List Nat) (state : ReachState) :
    forIn ticks state (reachBody index) =
      (show Id ReachState from pure (reachWalk index ticks.length state)) := by
  induction ticks generalizing state with
  | nil => rfl
  | cons tick rest ih =>
    cases state with
    | mk pending stored =>
      cases stored with
      | mk seen reversed =>
        cases pending with
        | nil => simp [List.forIn_cons, reachBody, reachWalk]
        | cons name remaining =>
          by_cases visited : seen.contains name
          · simpa [List.forIn_cons, reachBody, reachWalk, reachStep, visited] using
              ih (remaining, seen, reversed)
          · cases indexed : index[name]? <;>
              simpa [List.forIn_cons, reachBody, reachWalk, reachStep, visited, indexed] using
                ih (reachStep index (name :: remaining, seen, reversed))

/-- The proof model is exactly the existing runtime loop, including early
queue exhaustion, first-write indexing, duplicates, and absent declarations. -/
theorem reachable_walk (graph : Graph) (index : Std.HashMap String Node) (root : String) :
    reachable graph index root =
      (reachWalk index (graph.nodes.foldl (fun total node => total + node.parentOrders.flatten.length) 1)
        ([root], {}, [])).2.2.reverse := by
  unfold reachable
  simp only [Id.run, bind, pure]
  change (forIn [:(graph.nodes.foldl (fun total node => total + node.parentOrders.flatten.length) 1)]
    ([root], {}, []) (reachBody index)).run.2.2.reverse = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range', reach_loop]
  simp [Std.Legacy.Range.size]

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

private def unseenWeight (nodes : List Node) (seen : Std.HashSet String) : Nat :=
  (nodes.map fun node => if seen.contains node.name then 0 else node.parentOrders.flatten.length).sum

private theorem unseen_insert_le (nodes : List Node) :
    unseenWeight nodes (seen.insert name) ≤ unseenWeight nodes seen := by
  induction nodes with
  | nil => simp [unseenWeight]
  | cons node rest ih =>
    simp only [unseenWeight, List.map_cons, List.sum_cons] at *
    by_cases same : name = node.name <;> by_cases visited : seen.contains node.name <;>
      simp [Std.HashSet.contains_insert, same, visited] at * <;> omega

private theorem unseen_insert_consumes (member : node ∈ nodes) (absent : seen.contains node.name = false) :
    unseenWeight nodes (seen.insert node.name) + node.parentOrders.flatten.length ≤ unseenWeight nodes seen := by
  induction nodes with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst first
      have bound := unseen_insert_le (seen := seen) (name := node.name) rest
      change (if (seen.insert node.name).contains node.name then 0 else node.parentOrders.flatten.length) +
        unseenWeight rest (seen.insert node.name) + node.parentOrders.flatten.length ≤
        (if seen.contains node.name then 0 else node.parentOrders.flatten.length) + unseenWeight rest seen
      simp only [Std.HashSet.contains_insert, BEq.rfl, Bool.true_or, absent, Bool.false_eq_true, ↓reduceIte]
      omega
    · have bound := ih member
      by_cases same : node.name = first.name <;> by_cases visited : seen.contains first.name <;>
        simp [unseenWeight, Std.HashSet.contains_insert, same, visited] at * <;> omega

private def reachMeasure (graph : Graph) (state : ReachState) : Nat :=
  state.1.length + unseenWeight graph.nodes state.2.1

private theorem reach_measure_step (nonempty : state.1 ≠ []) :
    reachMeasure graph (reachStep (nodeIndex graph) state) < reachMeasure graph state := by
  rcases state with ⟨pending, seen, reversed⟩
  cases pending with
  | nil => exact False.elim (nonempty rfl)
  | cons name rest =>
    by_cases visited : seen.contains name
    · simp [reachMeasure, reachStep, visited]
    · have absent : seen.contains name = false := Bool.eq_false_iff.mpr visited
      cases indexed : (nodeIndex graph)[name]? with
      | none =>
        have bound := unseen_insert_le (seen := seen) (name := name) graph.nodes
        simp [reachMeasure, reachStep, visited, indexed]
        omega
      | some node =>
        obtain ⟨present, same⟩ := nodeIndex_declared indexed
        have consumes := unseen_insert_consumes present (same ▸ absent)
        have parentBound : (parents node).length ≤ node.parentOrders.flatten.length := (parents_sublist (node := node)).length_le
        simp [reachMeasure, reachStep, visited, indexed]
        rw [same] at consumes
        omega

private theorem reachWalk_drained (budget : reachMeasure graph state ≤ fuel) :
    (reachWalk (nodeIndex graph) fuel state).1 = [] := by
  induction fuel generalizing state with
  | zero =>
    have empty : state.1 = [] := List.length_eq_zero_iff.mp (by unfold reachMeasure at budget; omega)
    exact empty
  | succ fuel ih =>
    cases pending : state.1 with
    | nil => simp [reachWalk, pending]
    | cons name rest =>
      have nonempty : state.1 ≠ [] := by simp [pending]
      have smaller := reach_measure_step (graph := graph) nonempty
      simpa [reachWalk, pending] using ih (state := reachStep (nodeIndex graph) state) (by omega)

private theorem unseen_empty_fold (nodes : List Node) (base : Nat) :
    nodes.foldl (fun total node => total + node.parentOrders.flatten.length) base =
      base + unseenWeight nodes {} := by
  induction nodes generalizing base with
  | nil => simp [unseenWeight]
  | cons node rest ih =>
    rw [List.foldl_cons, ih]
    simp only [unseenWeight, List.map_cons, List.sum_cons, Std.HashSet.contains_empty, Bool.false_eq_true, ↓reduceIte]
    omega

/-- The original edge-count budget exhausts the queue, including repeats,
cycles, missing names, and duplicate graph declarations. -/
theorem reachable_queue_drained (graph : Graph) (root : String) :
    (reachWalk (nodeIndex graph)
      (graph.nodes.foldl (fun total node => total + node.parentOrders.flatten.length) 1)
      ([root], {}, [])).1 = [] := by
  apply reachWalk_drained
  rw [unseen_empty_fold]
  exact Nat.le_refl _

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4

theorem Ancestor.trans {ancestor middle root : String} (first : Ancestor graph ancestor middle)
    (second : Ancestor graph middle root) : Ancestor graph ancestor root := by
  induction second with
  | self => exact first
  | parent found member earlier ih => exact .parent found member (ih first)

end LeanPoo.C4

namespace LeanPoo.C4.LinearizeState

/-- Discovered names stay in the frontier or visited list, and all visited
nodes have their complete original parent edges discovered. -/
structure ReachInvariant (graph : Graph) (root : String) (state : ReachState) : Prop where
  seen : ∀ name, state.2.1.contains name = true ↔ name ∈ state.2.2
  located : root ∈ state.1 ∨ root ∈ state.2.2
  closed : ∀ name ∈ state.2.2, ∀ node, graph.findNode? name = some node →
    ∀ parent ∈ node.parentOrders.flatten, parent ∈ state.1 ∨ parent ∈ state.2.2
  sound : ∀ name, name ∈ state.1 ∨ name ∈ state.2.2 → Ancestor graph name root

private theorem visit_move (member : item ∈ name :: rest ∨ item ∈ reversed) :
    item ∈ rest ++ extras ∨ item ∈ name :: reversed := by
  rcases member with queued | stored
  · rcases List.mem_cons.mp queued with same | later
    · exact .inr (List.mem_cons.mpr (.inl same))
    · exact .inl (List.mem_append_left _ later)
  · exact .inr (List.mem_cons.mpr (.inr stored))

private theorem ReachInvariant.visit {seen : Std.HashSet String} {name : String} {rest reversed extras : List String} (valid : ReachInvariant graph root (name :: rest, seen, reversed))
    (children : ∀ node, graph.findNode? name = some node → ∀ parent ∈ node.parentOrders.flatten, parent ∈ extras)
    (extraSound : ∀ item ∈ extras, Ancestor graph item root) :
    ReachInvariant graph root (rest ++ extras, seen.insert name, name :: reversed) := by
  constructor
  · intro item
    change (seen.insert name).contains item = true ↔ item ∈ name :: reversed
    rw [Std.HashSet.contains_insert]
    simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    exact or_congr eq_comm (valid.seen item)
  · exact visit_move valid.located
  · intro item member node found parent edge
    rcases List.mem_cons.mp member with same | old
    · subst item; exact .inl (List.mem_append_right _ (children node found parent edge))
    · exact visit_move (valid.closed item old node found parent edge)
  · intro item member
    rcases member with queued | stored
    · rcases List.mem_append.mp queued with old | extra
      · exact valid.sound item (.inl (List.mem_cons.mpr (.inr old)))
      · exact extraSound item extra
    · rcases List.mem_cons.mp stored with same | old
      · subst item; exact valid.sound name (.inl (by simp))
      · exact valid.sound item (.inr old)

private theorem ReachInvariant.pop {seen : Std.HashSet String} {name : String} {rest reversed : List String} (valid : ReachInvariant graph root (name :: rest, seen, reversed))
    (visited : seen.contains name = true) : ReachInvariant graph root (rest, seen, reversed) := by
  have recorded := (valid.seen name).mp visited
  have move (item : String) (member : item ∈ name :: rest ∨ item ∈ reversed) :
      item ∈ rest ∨ item ∈ reversed := by
    rcases member with queued | stored
    · rcases List.mem_cons.mp queued with same | later
      · subst item; exact .inr recorded
      · exact .inl later
    · exact .inr stored
  refine ⟨valid.seen, move root valid.located, ?_, ?_⟩
  · intro item member node found parent edge; exact move parent (valid.closed item member node found parent edge)
  · intro item member
    exact valid.sound item (member.elim (fun queued => .inl (List.mem_cons.mpr (.inr queued))) Or.inr)

private theorem reach_step_invariant (valid : ReachInvariant graph root state) :
    ReachInvariant graph root (reachStep (nodeIndex graph) state) := by
  rcases state with ⟨pending, seen, reversed⟩
  cases pending with
  | nil => exact valid
  | cons name rest =>
    by_cases visited : seen.contains name
    · simpa [reachStep, visited] using valid.pop visited
    · cases indexed : (nodeIndex graph)[name]? with
      | none =>
        have missing : graph.findNode? name = none := (nodeIndex_lookup graph name).symm.trans indexed
        have next := valid.visit (extras := []) (by intro node found; rw [missing] at found; cases found) (by simp)
        simpa [reachStep, visited, indexed] using next
      | some node =>
        have found : graph.findNode? name = some node := (nodeIndex_lookup graph name).symm.trans indexed
        have next := valid.visit (extras := parents node) (by
          intro declaration declared parent edge
          have same := Option.some.inj (declared.symm.trans found)
          subst declaration; exact parents_mem.mpr edge) (by
          intro parent member
          exact (Ancestor.parent found (parents_mem.mp member) Ancestor.self).trans
            (valid.sound name (.inl (by simp))))
        simpa [reachStep, visited, indexed] using next

private theorem reach_walk_invariant (valid : ReachInvariant graph root state) :
    ReachInvariant graph root (reachWalk (nodeIndex graph) fuel state) := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
    cases pending : state.1 with
    | nil => simpa [reachWalk, pending] using valid
    | cons name rest => simpa [reachWalk, pending] using ih (reach_step_invariant valid)

private theorem reached_ancestor (valid : ReachInvariant graph root state) (empty : state.1 = [])
    (path : Ancestor graph target source) (present : source ∈ state.2.2) : target ∈ state.2.2 := by
  induction path with
  | self => exact present
  | parent found member earlier ih =>
    have discovered := valid.closed _ present _ found _ member
    rw [empty] at discovered
    exact ih (by simpa using discovered)

/-- Exact discovery of all graph ancestors by the actual bounded runtime BFS.
Unknown names can be ancestors through edges; declaration validation is separate. -/
theorem reachable_iff (graph : Graph) (root name : String) :
    name ∈ reachable graph (nodeIndex graph) root ↔ Ancestor graph name root := by
  have initial : ReachInvariant graph root ([root], {}, []) := by
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro item member; have same : item = root := by simpa using member
    subst item; exact .self
  have valid := reach_walk_invariant (fuel := graph.nodes.foldl
    (fun total node => total + node.parentOrders.flatten.length) 1) initial
  have drained := reachable_queue_drained graph root
  rw [reachable_walk, List.mem_reverse]
  constructor
  · intro member; exact valid.sound name (.inr member)
  · intro ancestor
    have rootPresent := valid.located
    rw [drained] at rootPresent
    exact reached_ancestor valid drained ancestor (by simpa using rootPresent)

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

private theorem inserted_names (names : List String) (seen : Std.HashSet String) (name : String) :
    (names.foldl (fun seen name => seen.insert name) seen).contains name = true ↔
      name ∈ names ∨ seen.contains name = true := by
  induction names generalizing seen with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    simp only [eq_comm (a := first) (b := name)]
    simp only [or_assoc, or_left_comm]

/-- The exact reachable-declaration filter used by linearizeWith. -/
def reachableNodes (graph : Graph) (root : String) : List Node :=
  let names := reachable graph (nodeIndex graph) root
  let namesSet := names.foldl (fun seen name => seen.insert name) ({} : Std.HashSet String)
  graph.nodes.filter (fun node => namesSet.contains node.name)

theorem reachableNodes_mem : node ∈ reachableNodes graph root ↔
    node ∈ graph.nodes ∧ Ancestor graph node.name root := by
  simp only [reachableNodes, List.mem_filter, inserted_names, Std.HashSet.contains_empty,
    Bool.false_eq_true, or_false, reachable_iff]

/-- The smaller budget actually used by the top-level runtime is sufficient
for every finite original graph derivation. Duplicate declarations need not
be excluded to establish this length bound. -/
theorem reachableNodes_budget (trace : GraphTrace graph root output tail) :
    output.length ≤ (reachableNodes graph root).length := by
  have bound : output.length ≤ ((reachableNodes graph root).map Node.name).length :=
    trace.nodup.length_le_of_subset (by
      intro item member
      have ancestor := trace.covers.mp member
      obtain ⟨_, _, derivation, _⟩ := trace.ancestor ancestor
      obtain ⟨node, present, same⟩ := derivation.declared
      exact List.mem_map.mpr ⟨node, reachableNodes_mem.mpr ⟨present, same ▸ ancestor⟩, same⟩)
  simpa using bound

/-- Exact top-level completeness once the actual reachable-declaration
validation succeeds. Discovery, root lookup, fuel, and cache success are derived. -/
theorem linearizeWith_complete (trace : GraphTrace graph root output tail)
    (validated : (Graph.mk (reachableNodes graph root)).validate = .ok ()) (checked : Bool) :
    linearizeWith graph root checked = .ok output := by
  obtain ⟨table, resolved, _, _, entry, cached, same⟩ :=
    resolveNode_complete (root := root) (checked := checked) (MetadataInvariant.empty graph)
      trace (reachableNodes_budget trace)
  have found : ∃ node, (nodeIndex graph).get? root = some node := by
    cases trace with
    | node found _ _ _ _ => exact ⟨_, (nodeIndex_lookup graph root).trans found⟩
  obtain ⟨node, indexed⟩ := found
  unfold linearizeWith
  simp only [indexed, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  change (do
    (Graph.mk (reachableNodes graph root)).validate
    let ready ← resolveNode (nodeIndex graph) root root {} checked (reachableNodes graph root).length
    let some result := lookup ready root | throw (Error.cycle root)
    pure result.precedence) = .ok output
  rw [validated]
  simp only [bind, Except.bind, resolved, cached, same, pure, Except.pure]

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4.LinearizeState

private theorem reach_step_nodup (valid : ReachInvariant graph root state) (unique : state.2.2.Nodup) :
    (reachStep (nodeIndex graph) state).2.2.Nodup := by
  rcases state with ⟨pending, seen, reversed⟩
  cases pending with
  | nil => exact unique
  | cons name rest =>
    by_cases visited : seen.contains name
    · simpa [reachStep, visited] using unique
    · have absent : name ∉ reversed := fun member => visited ((valid.seen name).mpr member)
      cases indexed : (nodeIndex graph)[name]? <;>
        simpa [reachStep, visited, indexed] using List.nodup_cons.mpr ⟨absent, unique⟩

private theorem reach_walk_nodup (valid : ReachInvariant graph root state) (unique : state.2.2.Nodup) :
    (reachWalk (nodeIndex graph) fuel state).2.2.Nodup := by
  induction fuel generalizing state with
  | zero => exact unique
  | succ fuel ih =>
    cases pending : state.1 with
    | nil => simpa [reachWalk, pending] using unique
    | cons name rest =>
      simpa [reachWalk, pending] using ih (reach_step_invariant valid) (reach_step_nodup valid unique)

theorem reachable_nodup (graph : Graph) (root : String) :
    (reachable graph (nodeIndex graph) root).Nodup := by
  have initial : ReachInvariant graph root ([root], {}, []) := by
    refine ⟨by simp, by simp, by simp, ?_⟩
    intro item member; have same : item = root := by simpa using member
    subst item; exact .self
  rw [reachable_walk]
  simpa only [List.Nodup, List.pairwise_reverse, ne_comm] using
    reach_walk_nodup (fuel := graph.nodes.foldl (fun total node => total + node.parentOrders.flatten.length) 1) initial (by simp)

theorem reachable_trace_names (trace : GraphTrace graph root output tail) :
    name ∈ reachable graph (nodeIndex graph) root ↔ name ∈ output :=
  (reachable_iff graph root name).trans trace.covers.symm

end LeanPoo.C4.LinearizeState

namespace LeanPoo.C4

theorem linearize_complete (trace : GraphTrace graph root output tail)
    (validated : (Graph.mk (LinearizeState.reachableNodes graph root)).validate = .ok ()) :
    linearize graph root = .ok output := LinearizeState.linearizeWith_complete trace validated false

theorem linearizeChecked_complete (trace : GraphTrace graph root output tail)
    (validated : (Graph.mk (LinearizeState.reachableNodes graph root)).validate = .ok ()) :
    linearizeChecked graph root = .ok output := LinearizeState.linearizeWith_complete trace validated true

end LeanPoo.C4
