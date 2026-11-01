import LeanPoo.Proof.Invalidation

/-! Mutable native sources clear derived state together. The graph models all
registered source edges (parents, hooks and descriptors). Correct registration,
sequential evaluation and graph finiteness are explicit native obligations. -/
namespace LeanPoo.Object
/-- One retained derived cache cell, tagged by the source's logical revision. -/
structure RevisionCache (Value : Type) where
  revision : Nat
  derived : Option Value
/-- Clear every reached owner; retain unaffected owners exactly. -/
def invalidateCaches (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) : String → RevisionCache Value :=
  fun name => if name ∈ Proof.invalidatedNodes graph changed then
    ⟨(cache name).revision + 1, none⟩ else cache name
/-- A finite registered path always clears its descendant, including shared joins. -/
theorem invalidateCaches_descendant (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (origin name : String) (steps : Nat)
    (member : origin ∈ changed) (path : Proof.Descendant graph origin steps name)
    (bounded : steps ≤ graph.nodes.length) :
    (invalidateCaches graph changed cache name).derived = none := by
  simp [invalidateCaches, Proof.mem_invalidated_of_descendant graph changed origin name steps member path bounded]
/-- A source edit advances a shared descendant exactly once, regardless of path count. -/
theorem invalidateCaches_once (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (name : String)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    (invalidateCaches graph changed cache name).revision = (cache name).revision + 1 := by
  simp [invalidateCaches, affected]
/-- An owner outside the registered reverse closure is unchanged. -/
theorem invalidateCaches_frame (graph : C4.Graph) (changed : List String)
    (cache : String → RevisionCache Value) (name : String)
    (untouched : name ∉ Proof.invalidatedNodes graph changed) :
    invalidateCaches graph changed cache name = cache name := by simp [invalidateCaches, untouched]
/-- Native preflight rejects sealed sources or edits during any affected computation. -/
def guardedEdit (sealed active : Bool) (old : State) (edit : State → State) : Except String State :=
  if sealed then .error "sealed prototype" else
  if active then .error "object mutation during computation" else .ok (edit old)
/-- A refused edit publishes the caller's original source exactly. -/
def publishEdit (old : State) (result : Except String State) : State :=
  match result with | .error _ => old | .ok next => next
/-- Source refusal does not invoke an edit or advance the published revision. -/
theorem publishEdit_sealed (old : State) (edit : State → State) (active : Bool) :
    publishEdit old (guardedEdit true active old edit) = old := rfl

/-- Root preflight has already run. Its successful snapshot records whether a
weak dependency table exists and the current children, including newly registered
ones. The existing checked traversal returns descendant-first owners without root.
This models a finite faithful graph, not weak-table collection or callback rollback. -/
def invalidationAfterCheck (root : Node) (checked : Except Cause (Bool × List Node))
    (walk : List Node → Except Cause (List Node)) : Except Cause (List Node) := do
  let (retained, children) ← checked
  if retained then
    let owners ← walk children
    pure (owners ++ [root])
  else pure [root]

/-- Reference traversal preparation always handles the admitted root's children. -/
def generalInvalidationOrder (root : Node) (checked : Except Cause (Bool × List Node))
    (walk : List Node → Except Cause (List Node)) : Except Cause (List Node) := do
  let (_, children) ← checked
  let owners ← walk children
  pure (owners ++ [root])

/-- A pristine post-check leaf never calls the graph walker. -/
theorem invalidationAfterCheck_leaf (root : Node)
    (walk : List Node → Except Cause (List Node)) :
    invalidationAfterCheck root (.ok (false, [])) walk = .ok [root] := rfl

/-- Root refusal keeps its exact cause, including false-like host exceptions. -/
theorem invalidationAfterCheck_refused (root : Node) (cause : Cause)
    (walk : List Node → Except Cause (List Node)) :
    invalidationAfterCheck root (.error cause) walk = .error cause := rfl

/-- Registered dependencies, even an empty retained table, keep the old traversal.
The faithful-absence premise is required only for the pristine branch. -/
theorem invalidationAfterCheck_eq_general (root : Node) (retained : Bool)
    (children : List Node) (walk : List Node → Except Cause (List Node))
    (absent : retained = false → children = []) (empty : walk [] = .ok []) :
    invalidationAfterCheck root (.ok (retained, children)) walk =
      generalInvalidationOrder root (.ok (retained, children)) walk := by
  cases retained with
  | false => have h := absent rfl; subst children
             change (.ok [root] : Except Cause (List Node)) =
               (walk []).map (fun owners => owners ++ [root])
             rw [empty]; rfl
  | true => rfl

/-- A child added during root preflight is checked; refusal cannot become a leaf hit. -/
theorem invalidationAfterCheck_child_refused (root : Node) (children : List Node)
    (cause : Cause) (walk : List Node → Except Cause (List Node))
    (refused : walk children = .error cause) :
    invalidationAfterCheck root (.ok (true, children)) walk = .error cause := by
  change (walk children).map (fun owners => owners ++ [root]) = .error cause
  rw [refused]; rfl

/-- Revision advancement precedes clear. Clear return values are discarded, but
clear failures do not roll back the revision, matching the existing callback API. -/
def finishInvalidation (old : RevisionCache Value) (cleared : Except Cause Result) :
    RevisionCache Value × Except Cause Unit :=
  (⟨old.revision + 1, none⟩, cleared.map (fun _ => ()))

/-- Function/false/multiple-value payloads do not escape the unit-return boundary. -/
theorem finishInvalidation_ok (old : RevisionCache Value) (result : Result) :
    finishInvalidation old (Except.ok result : Except Cause Result) =
      (⟨old.revision + 1, none⟩, .ok ()) := rfl

/-- A thrown clear failure still leaves its already advanced source generation. -/
theorem finishInvalidation_error (old : RevisionCache Value) (cause : Cause) :
    finishInvalidation old (Except.error cause : Except Cause Unit) =
      (⟨old.revision + 1, none⟩, .error cause) := rfl

/-- Logical temporary counts: one traversal table and two list/pair cells per
pending owner on the retained path; no physical allocation or GC theorem. -/
def invalidationScratch (retained : Bool) (owners : Nat) : Nat × Nat :=
  if retained then (1, 2 * owners) else (0, 0)

/-- Every pristine leaf avoids the reference path's one table and two cells. -/
theorem invalidationScratch_leaf : invalidationScratch false 1 = (0, 0) ∧
    invalidationScratch true 1 = (1, 2) := ⟨rfl, rfl⟩

/-- Existing reverse-closure semantics specialize to a singleton without changing
unrelated owners, revisions or cached Function payloads. Closure fidelity remains
an explicit hypothesis; this does not decide whether a weak key was collected. -/
theorem invalidateCaches_leaf (graph : C4.Graph) (root : String)
    (cache : String → RevisionCache Value)
    (closure : Proof.invalidatedNodes graph [root] = [root]) :
    invalidateCaches graph [root] cache = fun name =>
      if name = root then ⟨(cache name).revision + 1, none⟩ else cache name := by
  funext name
  simp [invalidateCaches, closure]

/-- Add captured external source names to the existing finite dependency graph.
This is a source-edge graph, not a request to change C3 inheritance. Duplicate
and older edges are conservative; host weak tables implement membership updates. -/
def registerSlotSources (graph : C4.Graph) (owner : String) (sources : List String) : C4.Graph :=
  let external := sources.filter (· != owner)
  if external = [] then graph else
    ⟨graph.nodes.map (fun node => if node.name = owner then
      { node with parentOrders := node.parentOrders ++ [external] } else node)⟩

/-- Empty and receiver-local observations do not create source edges. -/
theorem registerSlotSources_local (graph : C4.Graph) (owner : String)
    (sources : List String) (localOnly : ∀ source ∈ sources, source = owner) :
    registerSlotSources graph owner sources = graph := by
  have empty : sources.filter (· != owner) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro source present
    simp [localOnly source present]
  simp [registerSlotSources, empty]

/-- Registering captured sources never adds or removes an object identity. -/
theorem registerSlotSources_names (graph : C4.Graph) (owner : String) (sources : List String) :
    (registerSlotSources graph owner sources).nodes.map C4.Node.name = graph.nodes.map C4.Node.name := by
  unfold registerSlotSources
  dsimp only
  split
  · rfl
  · simp only [List.map_map]
    apply List.map_congr_left
    intro node _
    dsimp only [Function.comp_apply]
    split <;> rfl

/-- Every old dependency remains registered, including conditional earlier reads. -/
theorem registerSlotSources_old_edge (graph : C4.Graph) (owner : String) (sources : List String)
    (node : C4.Node) (member : node ∈ graph.nodes) (source : String)
    (edge : source ∈ node.parentOrders.flatten) :
    ∃ next ∈ (registerSlotSources graph owner sources).nodes,
      next.name = node.name ∧ source ∈ next.parentOrders.flatten := by
  unfold registerSlotSources
  dsimp only
  split
  · exact ⟨node, member, rfl, edge⟩
  · let next := if node.name = owner then
      { node with parentOrders := node.parentOrders ++ [sources.filter (· != owner)] } else node
    refine ⟨next, List.mem_map.mpr ⟨node, member, rfl⟩, ?_, ?_⟩
    · dsimp [next]; split <;> rfl
    · dsimp [next]; split <;> simp_all

/-- A captured non-self source creates an actual one-edge invalidation path. -/
theorem registerSlotSources_path (graph : C4.Graph) (owner source : String) (sources : List String)
    (node : C4.Node) (member : node ∈ graph.nodes) (named : node.name = owner)
    (captured : source ∈ sources) (different : source ≠ owner) :
    Proof.Descendant (registerSlotSources graph owner sources) source 1 owner := by
  have present : source ∈ sources.filter (· != owner) := by simp [captured, different]
  have nonempty : sources.filter (· != owner) ≠ [] := by
    intro empty; rw [empty] at present; simp at present
  let next : C4.Node := { node with parentOrders := node.parentOrders ++ [sources.filter (· != owner)] }
  have nextMember : next ∈ (registerSlotSources graph owner sources).nodes := by
    simp only [registerSlotSources, nonempty, ↓reduceIte]
    exact List.mem_map.mpr ⟨node, member, by simp [named, next]⟩
  have edge : source ∈ next.parentOrders.flatten := by simp [next, present]
  have path := Proof.Descendant.child (Proof.Descendant.self :
    Proof.Descendant (registerSlotSources graph owner sources) source 0 source) next nextMember edge
  simpa [next, named] using path

/-- Source registration preserves every old transitive path. -/
theorem registerSlotSources_descendant (graph : C4.Graph) (owner : String) (sources : List String)
    {origin target : String} {steps : Nat} (path : Proof.Descendant graph origin steps target) :
    Proof.Descendant (registerSlotSources graph owner sources) origin steps target := by
  induction path with
  | self => exact .self
  | child path node member edge ih =>
    obtain ⟨next, nextMember, named, nextEdge⟩ := registerSlotSources_old_edge graph owner sources node member _ edge
    simpa [named] using Proof.Descendant.child ih next nextMember nextEdge

/-- A faithful captured external edge clears the ordinary derived cache on edit.
The owner is an existing finite node; no new evaluator or cache is introduced. -/
theorem registeredSlotSource_cleared (graph : C4.Graph) (owner source : String) (sources : List String)
    (node : C4.Node) (member : node ∈ graph.nodes) (named : node.name = owner)
    (captured : source ∈ sources) (different : source ≠ owner)
    (cache : String → RevisionCache Value) :
    (invalidateCaches (registerSlotSources graph owner sources) [source] cache owner).derived = none := by
  have width := congrArg List.length (registerSlotSources_names graph owner sources)
  simp only [List.length_map] at width
  apply invalidateCaches_descendant _ _ cache source owner 1 (by simp)
    (registerSlotSources_path graph owner source sources node member named captured different)
  rw [width]
  cases shape : graph.nodes with
  | nil => simp [shape] at member
  | cons first rest => simp

/-- The graph denotes host state after work effects; those effects are not rolled
back. Whole capture admission precedes this invocation's registration. Source exceptions, including
false-like causes, are never replaced by a later epoch or stale-read refusal. -/
def withSlotDependencies (graph : C4.Graph) (owner : String)
    (capture : Except Cause (Value × List String)) (epoch : Except Cause Unit)
    (admit : List String → Except Cause Unit)
    (registration : List String → List String := id) : Except Cause (Value × C4.Graph) := do
  let (value, sources) ← capture
  let _ ← epoch
  if sources = [] then pure (value, graph) else
    let _ ← admit sources
    pure (value, registerSlotSources graph owner (registration sources))

/-- Failed work performs no later admission or registration and keeps its cause. -/
theorem withSlotDependencies_source_error (graph : C4.Graph) (owner : String) (cause : Cause)
    (epoch : Except Cause Unit) (admit : List String → Except Cause Unit) :
    withSlotDependencies graph owner (.error cause : Except Cause (Value × List String)) epoch admit =
      .error cause := rfl

/-- A retired owner refuses even a callback-free result before publishing it. -/
theorem withSlotDependencies_epoch_error (graph : C4.Graph) (owner : String)
    (value : Value) (sources : List String) (cause : Cause) (admit : List String → Except Cause Unit) :
    withSlotDependencies graph owner (.ok (value, sources)) (.error cause) admit = .error cause := rfl

/-- A stale captured graph cannot publish a partial set of source edges. -/
theorem withSlotDependencies_refused (graph : C4.Graph) (owner : String) (value : Value)
    (sources : List String) (nonempty : sources ≠ []) (cause : Cause)
    (admit : List String → Except Cause Unit) (refused : admit sources = .error cause) :
    withSlotDependencies graph owner (.ok (value, sources)) (.ok ()) admit = .error cause := by
  simp [withSlotDependencies, nonempty, refused, bind, Except.bind]

/-- Successful admission retains the exact value and installs only declared reads. -/
theorem withSlotDependencies_ok (graph : C4.Graph) (owner : String) (value : Value)
    (sources : List String) (nonempty : sources ≠ [])
    (admit : List String → Except Cause Unit) (ready : admit sources = .ok ()) :
    withSlotDependencies graph owner (.ok (value, sources)) (.ok ()) admit =
      .ok (value, registerSlotSources graph owner sources) := by
  simp [withSlotDependencies, nonempty, ready, bind, Except.bind]
  rfl

/-- No getter reads means no replay preparation or new edges. -/
theorem withSlotDependencies_empty (graph : C4.Graph) (owner : String) (value : Value)
    (admit : List String → Except Cause Unit) :
    withSlotDependencies graph owner (.ok (value, [])) (.ok ()) admit = .ok (value, graph) := rfl

/-- Logical weak-edge update attempts, excluding capture, full read admission,
projection preparation, hashing, allocation and GC. Repeated receivers count. -/
def slotSourceRegistrationWork (owner : String) (sources : List String) : Nat :=
  (sources.filter (· != owner)).length

/-- Self-edge suppression never needs more updates than the captured read row. -/
theorem slotSourceRegistrationWork_le (owner : String) (sources : List String) :
    slotSourceRegistrationWork owner sources ≤ sources.length := by
  exact List.length_filter_le _ _

/-- Distinct external receiver identities represented by the existing traversal
set. Host enumeration order is irrelevant to weak-edge membership. -/
def distinctSlotSources (owner : String) (sources : List String) : List String :=
  (sources.filter (· != owner)).eraseDups

/-- Deduplication preserves exactly the external source set, never read admission. -/
theorem mem_distinctSlotSources (owner source : String) (sources : List String) :
    source ∈ distinctSlotSources owner sources ↔ source ∈ sources ∧ source ≠ owner := by
  simp [distinctSlotSources]

/-- Observe source edges independently of duplicate parent rows or enumeration. -/
private def sourceParent (graph : C4.Graph) (parent child : String) : Prop :=
  ∃ node ∈ graph.nodes, node.name = child ∧ parent ∈ node.parentOrders.flatten

/-- Concrete registration adds exactly the external captured membership. -/
private theorem sourceParent_registered (graph : C4.Graph) (owner parent child : String)
    (sources : List String) :
    sourceParent (registerSlotSources graph owner sources) parent child ↔
      ∃ node ∈ graph.nodes, node.name = child ∧
        (parent ∈ node.parentOrders.flatten ∨
          (node.name = owner ∧ parent ∈ sources ∧ parent ≠ owner)) := by
  unfold sourceParent registerSlotSources
  dsimp only
  split
  · rename_i empty
    constructor
    · rintro ⟨node, member, named, edge⟩
      exact ⟨node, member, named, .inl edge⟩
    · rintro ⟨node, member, named, edge | ⟨_, captured, different⟩⟩
      · exact ⟨node, member, named, edge⟩
      · have present : parent ∈ sources.filter (· != owner) := by simp [captured, different]
        simp [empty] at present
  · constructor
    · rintro ⟨next, member, named, edge⟩
      obtain ⟨node, originalMember, rfl⟩ := List.mem_map.mp member
      by_cases owned : node.name = owner
      · simp only [owned, ↓reduceIte] at named edge
        refine ⟨node, originalMember, by simpa [owned] using named, ?_⟩
        simpa [owned] using edge
      · simp only [owned, ↓reduceIte] at named edge
        exact ⟨node, originalMember, named, .inl edge⟩
    · rintro ⟨node, member, named, edge⟩
      let next := if node.name = owner then
        { node with parentOrders := node.parentOrders ++ [sources.filter (· != owner)] } else node
      refine ⟨next, List.mem_map.mpr ⟨node, member, rfl⟩, ?_, ?_⟩
      · dsimp [next]; split <;> exact named
      · dsimp [next]
        split
        · rename_i owned
          simpa [owned] using edge
        · rename_i external
          simpa [external] using edge

/-- The traversal's distinct receiver set changes no source edge. All read
credentials still undergo the original ordered admission separately. -/
theorem distinctSlotSources_parent_iff (graph : C4.Graph) (owner parent child : String)
    (sources : List String) :
    sourceParent (registerSlotSources graph owner (distinctSlotSources owner sources)) parent child ↔
      sourceParent (registerSlotSources graph owner sources) parent child := by
  simp only [sourceParent_registered, mem_distinctSlotSources, and_assoc, and_self]

/-- Transport a finite path through equal source-edge observations. -/
private theorem sourceParent_descendant {left right : C4.Graph}
    (edges : ∀ parent child, sourceParent left parent child ↔ sourceParent right parent child)
    {origin target : String} {steps : Nat} (path : Proof.Descendant left origin steps target) :
    Proof.Descendant right origin steps target := by
  induction path with
  | self => exact .self
  | child path node member edge ih =>
    have registered : sourceParent left _ node.name := ⟨node, member, rfl, edge⟩
    obtain ⟨next, nextMember, named, nextEdge⟩ := (edges _ _).mp registered
    simpa [named] using Proof.Descendant.child ih next nextMember nextEdge

/-- Receiver deduplication preserves every transitive source path in both directions. -/
theorem distinctSlotSources_descendant_iff (graph : C4.Graph) (owner : String)
    (sources : List String) (origin target : String) (steps : Nat) :
    Proof.Descendant (registerSlotSources graph owner (distinctSlotSources owner sources)) origin steps target ↔
      Proof.Descendant (registerSlotSources graph owner sources) origin steps target := by
  constructor
  · exact sourceParent_descendant (fun parent child => distinctSlotSources_parent_iff graph owner parent child sources)
  · exact sourceParent_descendant (fun parent child => (distinctSlotSources_parent_iff graph owner parent child sources).symm)

/-- Distinct writes preserve complete cache/revision observations, including
unaffected owners, shared joins, conservative old edges and multiple edits. -/
theorem distinctSlotSources_invalidate_eq (graph : C4.Graph) (owner : String)
    (sources changed : List String) (cache : String → RevisionCache Value) :
    invalidateCaches (registerSlotSources graph owner (distinctSlotSources owner sources)) changed cache =
      invalidateCaches (registerSlotSources graph owner sources) changed cache := by
  have before := congrArg List.length (registerSlotSources_names graph owner sources)
  have after := congrArg List.length (registerSlotSources_names graph owner (distinctSlotSources owner sources))
  simp only [List.length_map] at before after
  funext name
  have membership : name ∈ Proof.invalidatedNodes
      (registerSlotSources graph owner (distinctSlotSources owner sources)) changed ↔
      name ∈ Proof.invalidatedNodes (registerSlotSources graph owner sources) changed := by
    simp only [Proof.mem_invalidated_iff_bounded_descendant, before, after,
      distinctSlotSources_descendant_iff]
  simp only [invalidateCaches, membership]

/-- A length bound for the standard finite deduplication operation. -/
private theorem sourceDedup_length (sources : List String) :
    sources.eraseDups.length ≤ sources.length := by
  match sources with
  | [] => simp
  | first :: rest =>
    rw [List.eraseDups_cons]
    simp only [List.length_cons]
    exact Nat.succ_le_succ (Nat.le_trans (sourceDedup_length _) (List.length_filter_le _ _))
termination_by sources.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Distinct registration cannot exceed per-read weak-table writes. This excludes
capture, issuance/route checks, graph traversal, hash cost, allocation and GC. -/
theorem distinctSlotSources_work_le (owner : String) (sources : List String) :
    (distinctSlotSources owner sources).length ≤ slotSourceRegistrationWork owner sources :=
  sourceDedup_length _

/-- A repeated receiver/key footprint still creates the same invalidation path. -/
theorem distinctSlotSource_cleared (graph : C4.Graph) (owner source : String)
    (sources : List String) (node : C4.Node) (member : node ∈ graph.nodes)
    (named : node.name = owner) (captured : source ∈ sources) (different : source ≠ owner)
    (cache : String → RevisionCache Value) :
    (invalidateCaches (registerSlotSources graph owner (distinctSlotSources owner sources))
      [source] cache owner).derived = none :=
  registeredSlotSource_cleared graph owner source _ node member named
    ((mem_distinctSlotSources owner source sources).mpr ⟨captured, different⟩) different cache

/-- Empty and self-only footprints retain the original graph after deduplication. -/
theorem distinctSlotSources_local (graph : C4.Graph) (owner : String)
    (sources : List String) (localOnly : ∀ source ∈ sources, source = owner) :
    registerSlotSources graph owner (distinctSlotSources owner sources) = graph := by
  apply registerSlotSources_local
  intro source member
  exact localOnly source ((mem_distinctSlotSources owner source sources).mp member).1

/-- Receiver deduplication acts only after full read admission. A rejected key or
epoch cannot be hidden by another current key from the same receiver. -/
theorem withSlotDependencies_distinct_refused (graph : C4.Graph) (owner : String)
    (value : Value) (sources : List String) (nonempty : sources ≠ []) (cause : Cause)
    (admit : List String → Except Cause Unit) (refused : admit sources = .error cause) :
    withSlotDependencies graph owner (.ok (value, sources)) (.ok ()) admit
      (distinctSlotSources owner) = .error cause := by
  simp [withSlotDependencies, nonempty, refused, bind, Except.bind]

/-- Successful full admission retains the exact value and all external edges,
while registering each receiver through the existing traversal's set. -/
theorem withSlotDependencies_distinct_ok (graph : C4.Graph) (owner : String)
    (value : Value) (sources : List String) (nonempty : sources ≠ [])
    (admit : List String → Except Cause Unit) (ready : admit sources = .ok ()) :
    withSlotDependencies graph owner (.ok (value, sources)) (.ok ()) admit
      (distinctSlotSources owner) =
      .ok (value, registerSlotSources graph owner (distinctSlotSources owner sources)) := by
  simp [withSlotDependencies, nonempty, ready, bind, Except.bind]
  rfl

end LeanPoo.Object
