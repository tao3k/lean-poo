import LeanPoo.Proof.Reuse
import LeanPoo.C4.Ranked

namespace LeanPoo.Proof

universe u v

/-- The changed dependency keys of one obligation. -/
def changedDependencies [DecidableEq Key]
    (obligation : Obligation Key Value) (patch : Patch Key Value) : List Key :=
  obligation.dependencies.filter (fun key => decide (key ∈ patch.touched))

/-- Old obligations requiring new proofs, followed by newly introduced ones. -/
def pending [DecidableEq Key]
    (object : ProofObject Key Value) (patch : Patch Key Value) :
    List (Obligation Key Value) :=
  object.obligations.filter (fun obligation =>
    !(changedDependencies obligation patch).isEmpty) ++ patch.obligations

private theorem unaffected_of_empty [DecidableEq Key]
    (obligation : Obligation Key Value) (patch : Patch Key Value)
    (empty : changedDependencies obligation patch = []) :
    unaffected obligation patch := by
  intro key dependency touched
  have found : key ∈ changedDependencies obligation patch := by
    simp [changedDependencies, dependency, touched]
  simp [empty] at found

private theorem empty_of_unaffected [DecidableEq Key]
    (obligation : Obligation Key Value) (patch : Patch Key Value)
    (safe : unaffected obligation patch) :
    changedDependencies obligation patch = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro key membership
  have ⟨dependency, touched⟩ :
      key ∈ obligation.dependencies ∧ key ∈ patch.touched := by
    simpa [changedDependencies] using membership
  exact safe key dependency touched

/-- The executable pending filter agrees exactly with the proof-reuse criterion. -/
theorem mem_pending_iff [DecidableEq Key]
    (object : ProofObject Key Value) (patch : Patch Key Value)
    (obligation : Obligation Key Value) :
    obligation ∈ pending object patch ↔
      (obligation ∈ object.obligations ∧ ¬ unaffected obligation patch) ∨
        obligation ∈ patch.obligations := by
  rw [pending, List.mem_append]
  constructor
  · intro membership
    rcases membership with old | fresh
    · obtain ⟨owned, nonempty⟩ := List.mem_filter.mp old
      left
      refine ⟨owned, ?_⟩
      intro safe
      simp [empty_of_unaffected obligation patch safe] at nonempty
    · exact Or.inr fresh
  · intro membership
    rcases membership with ⟨owned, affected⟩ | fresh
    · left
      apply List.mem_filter.mpr
      refine ⟨owned, ?_⟩
      by_cases empty : changedDependencies obligation patch = []
      · exact False.elim (affected (unaffected_of_empty obligation patch empty))
      · simpa [List.isEmpty_iff] using empty
    · exact Or.inr fresh

/-- Proofs for the executable pending list close the complete proof object. -/
theorem closePending [DecidableEq Key]
    (object : ProofObject Key Value) (patch : Patch Key Value)
    (certificate : Certificate object)
    (discharged : ∀ obligation, obligation ∈ pending object patch →
      obligation.holds (append object patch).state) :
    Certificate (append object patch) := by
  apply close object patch certificate
  · intro obligation owned affected
    apply discharged obligation
    apply List.mem_append.mpr
    left
    apply List.mem_filter.mpr
    refine ⟨owned, ?_⟩
    by_cases empty : changedDependencies obligation patch = []
    · exact False.elim (affected (unaffected_of_empty obligation patch empty))
    · simpa [List.isEmpty_iff] using empty
  · intro obligation added
    exact discharged obligation (List.mem_append.mpr (Or.inr added))

/-- Reachability in the reverse inheritance direction: changed nodes and
every descendant whose precedence can depend on them. -/
def impactStep (graph : C4.Graph) (affected : List String) : List String :=
  (affected ++ graph.nodes.filterMap (fun node =>
    if node.parentOrders.flatten.any affected.contains then some node.name
    else none)).eraseDups

/-- Apply reverse-edge propagation a fixed number of times. -/
def impactN (graph : C4.Graph) : Nat → List String → List String
  | 0, affected => affected
  | steps + 1, affected => impactN graph steps (impactStep graph affected)

def invalidatedNodes (graph : C4.Graph) (changed : List String) : List String :=
  impactN graph graph.nodes.length changed.eraseDups


theorem mem_impactStep_of_mem (graph : C4.Graph) (affected : List String)
    (name : String) (membership : name ∈ affected) :
    name ∈ impactStep graph affected := by
  simp [impactStep, membership]

private theorem mem_impactN_of_mem (graph : C4.Graph)
    (steps : Nat) (affected : List String) (name : String)
    (membership : name ∈ affected) :
    name ∈ impactN graph steps affected := by
  induction steps generalizing affected with
  | zero => exact membership
  | succ previous inductionHypothesis =>
      exact inductionHypothesis (impactStep graph affected)
        (mem_impactStep_of_mem graph affected name membership)

theorem mem_impactStep_of_parent (graph : C4.Graph)
    (affected : List String) (node : C4.Node) (parent : String)
    (nodeMember : node ∈ graph.nodes)
    (parentMember : parent ∈ node.parentOrders.flatten)
    (parentAffected : parent ∈ affected) :
    node.name ∈ impactStep graph affected := by
  have childSelected : node ∈ graph.nodes.filter (fun candidate =>
      candidate.parentOrders.flatten.any affected.contains) := by
    apply List.mem_filter.mpr
    refine ⟨nodeMember, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨parent, parentMember, by simpa using parentAffected⟩
  simp only [impactStep, List.mem_eraseDups, List.mem_append]
  right
  apply List.mem_filterMap.mpr
  refine ⟨node, nodeMember, ?_⟩
  have selected : node.parentOrders.flatten.any affected.contains = true :=
    (List.mem_filter.mp childSelected).2
  simp [selected]

private theorem mem_impactStep_cases (graph : C4.Graph)
    (affected : List String) (name : String)
    (membership : name ∈ impactStep graph affected) :
    name ∈ affected ∨
      ∃ node ∈ graph.nodes, node.name = name ∧
        ∃ parent ∈ affected, parent ∈ node.parentOrders.flatten := by
  have inAppend : name ∈ affected ++ graph.nodes.filterMap (fun node =>
      if node.parentOrders.flatten.any affected.contains then some node.name
      else none) := by
    simpa [impactStep] using membership
  rcases List.mem_append.mp inAppend with previous | added
  · exact Or.inl previous
  · right
    obtain ⟨node, member, selected⟩ := List.mem_filterMap.mp added
    by_cases hasParent : node.parentOrders.flatten.any affected.contains = true
    · simp [hasParent] at selected
      refine ⟨node, member, selected, ?_⟩
      obtain ⟨parent, edge, present⟩ := List.any_eq_true.mp hasParent
      exact ⟨parent, by simpa using present, edge⟩
    · simp [hasParent] at selected

theorem mem_invalidated_of_changed (graph : C4.Graph)
    (changed : List String) (name : String) (membership : name ∈ changed) :
    name ∈ invalidatedNodes graph changed := by
  unfold invalidatedNodes
  exact mem_impactN_of_mem graph _ _ name (by simpa using membership)

/-- A parent-to-child path, indexed by its number of inheritance edges. -/
inductive Descendant (graph : C4.Graph) (origin : String) : Nat → String → Prop where
  | self : Descendant graph origin 0 origin
  | child {steps : Nat} {parent : String}
      (path : Descendant graph origin steps parent)
      (node : C4.Node) (member : node ∈ graph.nodes)
      (edge : parent ∈ node.parentOrders.flatten) :
      Descendant graph origin (steps + 1) node.name

private theorem impactN_succ_right (graph : C4.Graph)
    (steps : Nat) (affected : List String) :
    impactN graph (steps + 1) affected =
      impactStep graph (impactN graph steps affected) := by
  induction steps generalizing affected with
  | zero => rfl
  | succ previous inductionHypothesis =>
      simpa [impactN] using inductionHypothesis (impactStep graph affected)

/-- The recursive iterator agrees with the original finite fold. -/
theorem impactN_eq_foldl (graph : C4.Graph)
    (steps : Nat) (affected : List String) :
    impactN graph steps affected =
      (List.range steps).foldl (fun current _ => impactStep graph current) affected := by
  induction steps generalizing affected with
  | zero => rfl
  | succ previous inductionHypothesis =>
      rw [impactN_succ_right, List.range_succ]
      simp [inductionHypothesis]

private theorem mem_impactN_of_path (graph : C4.Graph)
    (origin : String) (affected : List String) (steps : Nat)
    (name : String) (path : Descendant graph origin steps name)
    (originMember : origin ∈ affected) :
    name ∈ impactN graph steps affected := by
  induction path with
  | self => exact originMember
  | child path node member edge inductionHypothesis =>
      rw [impactN_succ_right]
      exact mem_impactStep_of_parent graph (impactN graph _ affected)
        node _ member edge inductionHypothesis

private theorem mem_impactN_add (graph : C4.Graph)
    (steps extra : Nat) (affected : List String) (name : String)
    (membership : name ∈ impactN graph steps affected) :
    name ∈ impactN graph (steps + extra) affected := by
  induction extra with
  | zero => simpa using membership
  | succ previous inductionHypothesis =>
      rw [Nat.add_succ, impactN_succ_right]
      exact mem_impactStep_of_mem graph _ name inductionHypothesis

/-- Every path within the finite propagation bound reaches the result. -/
theorem mem_invalidated_of_descendant (graph : C4.Graph)
    (changed : List String) (origin name : String) (steps : Nat)
    (originChanged : origin ∈ changed)
    (path : Descendant graph origin steps name)
    (withinBound : steps ≤ graph.nodes.length) :
    name ∈ invalidatedNodes graph changed := by
  unfold invalidatedNodes
  have reached := mem_impactN_of_path graph origin changed.eraseDups
    steps name path (by simpa using originChanged)
  have extended := mem_impactN_add graph steps
    (graph.nodes.length - steps) changed.eraseDups name reached
  simpa [Nat.add_sub_of_le withinBound] using extended

/-- The finite propagation result contains only nodes with bounded paths
from a declared change. -/
theorem descendant_of_mem_invalidated (graph : C4.Graph)
    (changed : List String) (name : String)
    (membership : name ∈ invalidatedNodes graph changed) :
    ∃ origin ∈ changed, ∃ steps,
      steps ≤ graph.nodes.length ∧ Descendant graph origin steps name := by
  have classify : ∀ (steps : Nat) (name : String),
      name ∈ impactN graph steps changed.eraseDups →
      ∃ origin ∈ changed, ∃ distance,
        distance ≤ steps ∧ Descendant graph origin distance name := by
    intro steps
    induction steps with
    | zero =>
        intro current present
        exact ⟨current, by simpa [impactN] using present, 0, Nat.le_refl _, .self⟩
    | succ previous inductionHypothesis =>
        intro current present
        rw [impactN_succ_right] at present
        rcases mem_impactStep_cases graph _ current present with old | new
        · obtain ⟨origin, changedMember, distance, bounded, path⟩ :=
            inductionHypothesis current old
          exact ⟨origin, changedMember, distance,
            Nat.le_trans bounded (Nat.le_succ previous), path⟩
        · obtain ⟨node, nodeMember, same, parent, parentMember, edge⟩ := new
          obtain ⟨origin, changedMember, distance, bounded, path⟩ :=
            inductionHypothesis parent parentMember
          subst current
          exact ⟨origin, changedMember, distance + 1,
            Nat.succ_le_succ bounded, .child path node nodeMember edge⟩
  exact classify graph.nodes.length name membership

/-- Exact specification of the executable finite invalidation result. -/
theorem mem_invalidated_iff_bounded_descendant (graph : C4.Graph)
    (changed : List String) (name : String) :
    name ∈ invalidatedNodes graph changed ↔
      ∃ origin ∈ changed, ∃ steps,
        steps ≤ graph.nodes.length ∧ Descendant graph origin steps name := by
  constructor
  · exact descendant_of_mem_invalidated graph changed name
  · intro ⟨origin, originChanged, steps, withinBound, path⟩
    exact mem_invalidated_of_descendant graph changed origin name steps
      originChanged path withinBound

/-- Every inheritance edge consumes at least one rank level. -/
theorem Descendant.rank_distance {graph : C4.Graph} (ranked : C4.Ranked graph)
    {origin name : String} {steps : Nat} (path : Descendant graph origin steps name) :
    ranked.rank origin + steps ≤ ranked.rank name := by
  induction path with
  | self => simp
  | child path node member edge ih =>
    have lower := ranked.parentLower node member _ edge
    omega

/-- A ranked finite graph bounds every path, without a caller-supplied
distance bound or membership assumption on the change origin. -/
theorem Descendant.within_graph_bound {graph : C4.Graph} (ranked : C4.Ranked graph)
    {origin name : String} {steps : Nat} (path : Descendant graph origin steps name) :
    steps ≤ graph.nodes.length := by
  cases path with
  | self => omega
  | child path node member edge =>
    have distance := (Descendant.child path node member edge).rank_distance ranked
    have bounded := ranked.bounded node member
    omega

/-- A positive cycle contradicts the checked parent-rank discipline. -/
theorem Descendant.no_positive_cycle {graph : C4.Graph} (ranked : C4.Ranked graph)
    (name : String) (steps : Nat) : ¬ Descendant graph name (steps + 1) name := by
  intro path
  have distance := path.rank_distance ranked
  omega

/-- Exact unbounded reachability specification for certified finite graphs. -/
theorem mem_invalidated_iff_descendant {graph : C4.Graph} (ranked : C4.Ranked graph)
    (changed : List String) (name : String) :
    name ∈ invalidatedNodes graph changed ↔
      ∃ origin ∈ changed, ∃ steps, Descendant graph origin steps name := by
  constructor
  · intro present
    obtain ⟨origin, member, steps, _, path⟩ :=
      descendant_of_mem_invalidated graph changed name present
    exact ⟨origin, member, steps, path⟩
  · intro ⟨origin, member, steps, path⟩
    exact mem_invalidated_of_descendant graph changed origin name steps member path
      (path.within_graph_bound ranked)

/-- After the finite propagation pass, another pass adds no affected names. -/
theorem mem_impactStep_invalidated_iff {graph : C4.Graph} (ranked : C4.Ranked graph)
    (changed : List String) (name : String) :
    name ∈ impactStep graph (invalidatedNodes graph changed) ↔
      name ∈ invalidatedNodes graph changed := by
  constructor
  · intro present
    rcases mem_impactStep_cases graph _ name present with old | new
    · exact old
    · obtain ⟨node, member, same, parent, affected, edge⟩ := new
      obtain ⟨origin, changedMember, steps, path⟩ :=
        (mem_invalidated_iff_descendant ranked changed parent).mp affected
      subst name
      exact (mem_invalidated_iff_descendant ranked changed node.name).mpr
        ⟨origin, changedMember, steps + 1, .child path node member edge⟩
  · exact mem_impactStep_of_mem graph _ name

/-- An executable structural impact list with an exact reachability proof. -/
structure CertifiedInvalidation (graph : C4.Graph) (changed : List String) where
  names : List String
  characterizes : ∀ name, name ∈ names ↔
    ∃ origin ∈ changed, ∃ steps, Descendant graph origin steps name

/-- Check the whole inheritance graph before returning a complete impact
list. This concerns structural names, not inferred dependencies of slot bodies. -/
def certifyInvalidation (graph : C4.Graph) (changed : List String) :
    Except C4.RankError (CertifiedInvalidation graph changed) := do
  let ranked ← graph.inferRanked
  return {
    names := invalidatedNodes graph changed
    characterizes := mem_invalidated_iff_descendant ranked changed }


end LeanPoo.Proof
