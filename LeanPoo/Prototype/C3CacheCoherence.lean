import LeanPoo.Prototype.C3DAG

/-! Complete production/reference C3 coherence on every finite graph, including
cycles. Successful cached derivations cannot conceal a cycle. Actual active
paths and the finite declaration count justify reference replay at a cache hit.
No acyclic-graph premise or externally supplied rank map is required. -/
namespace LeanPoo.Prototype.C3
open LeanPoo.C4

/-- An edge from the actual first declaration selected by both traversals. -/
def Edge (graph : Graph) (source target : String) : Prop :=
  ∃ entry, graph.find? (fun row => row.1 == source) = some entry ∧ target ∈ entry.2

/-- A nonempty directed walk; a self walk represents a genuine ancestry cycle. -/
inductive Reaches (graph : Graph) : String → String → Prop where
  | edge (step : Edge graph source target) : Reaches graph source target
  | trans (first : Reaches graph source middle) (next : Reaches graph middle target) :
      Reaches graph source target

private theorem ParentDerivations.member (derived : ParentDerivations graph parents orders)
    (member : parent ∈ parents) :
    ∃ order ∈ orders, GraphDerivation graph parent order := by
  induction parents generalizing orders with
  | nil => simp at member
  | cons first rest ih =>
    cases derived with
    | cons head tail =>
      rcases List.mem_cons.mp member with equal | later
      · subst parent
        exact ⟨_, by simp, head⟩
      · obtain ⟨order, present, proof⟩ := ih tail later
        exact ⟨order, List.mem_cons_of_mem _ present, proof⟩

/-- Every edge below a derived node has a strictly shorter derived order. -/
theorem GraphDerivation.edge_decreases (derived : GraphDerivation graph name order)
    (edge : Edge graph name parent) :
    ∃ child, GraphDerivation graph parent child ∧ child.length < order.length := by
  cases derived with
  | @node _ entry orders tail found parents source certified =>
    obtain ⟨other, lookup, member⟩ := edge
    have equal : other = entry := Option.some.inj (lookup.symm.trans found)
    subst other
    obtain ⟨child, present, proof⟩ := parents.member member
    have bound := (certified.preserves (List.mem_append_left _ present)).length_le
    exact ⟨child, proof, by simp only [List.length_cons]; omega⟩

/-- A nonempty ancestry walk strictly decreases the successful order size. -/
theorem GraphDerivation.reaches_decreases (derived : GraphDerivation graph name order)
    (walk : Reaches graph name target) :
    ∃ child, GraphDerivation graph target child ∧ child.length < order.length := by
  induction walk generalizing order with
  | edge step => exact derived.edge_decreases step
  | trans first next ihFirst ihNext =>
    obtain ⟨middle, middleProof, lower⟩ := ihFirst derived
    obtain ⟨child, childProof, smaller⟩ := ihNext middleProof
    exact ⟨child, childProof, by omega⟩

/-- A finite successful C3 derivation cannot inhabit an ancestry cycle. -/
theorem GraphDerivation.no_cycle (derived : GraphDerivation graph name order) :
    ¬ Reaches graph name name := by
  intro cycle
  obtain ⟨child, other, smaller⟩ := derived.reaches_decreases cycle
  have same := derived.unique other
  subst child
  omega

/-- Precisely the path information maintained by the actual recursive visit. -/
structure ActivePath (graph : Graph) (name : String) (path : List String) : Prop where
  nodup : path.Nodup
  declared : ∀ ancestor ∈ path, ancestor ∈ graph.map Prod.fst
  reaches : ∀ ancestor ∈ path, Reaches graph ancestor name

theorem ActivePath.empty (graph : Graph) (name : String) : ActivePath graph name [] :=
  ⟨by simp, by simp, by simp⟩

private theorem found_name {graph : Graph} {name : String} {entry : String × List String}
    (found : graph.find? (fun row => row.1 == name) = some entry) :
    entry.1 = name := by
  have matched := List.find?_some found
  exact eq_of_beq matched

theorem ActivePath.length_le (active : ActivePath graph name path) :
    path.length ≤ graph.length := by
  have bound := List.Nodup.length_le_of_subset active.nodup active.declared
  simpa using bound

/-- Extend only after the production freshness check and actual row lookup. -/
theorem ActivePath.parent {parent : String} (active : ActivePath graph name path)
    (fresh : name ∉ path)
    (found : graph.find? (fun row => row.1 == name) = some entry)
    (member : parent ∈ entry.2) : ActivePath graph parent (name :: path) := by
  have edge : Edge graph name parent := ⟨entry, found, member⟩
  refine ⟨List.nodup_cons.mpr ⟨fresh, active.nodup⟩, ?_, ?_⟩
  · intro ancestor present
    rcases List.mem_cons.mp present with equal | later
    · subst ancestor
      have original := List.mem_of_find?_eq_some found
      exact List.mem_map.mpr ⟨entry, original, found_name found⟩
    · exact active.declared ancestor later
  · intro ancestor present
    rcases List.mem_cons.mp present with equal | later
    · subst ancestor
      exact .edge edge
    · exact .trans (active.reaches ancestor later) (.edge edge)

/-- Derived cache entries are fresh on every genuine active ancestry path. -/
theorem ActivePath.fresh (active : ActivePath graph name path)
    (derived : GraphDerivation graph name order) : name ∉ path := by
  intro member
  exact derived.no_cycle (active.reaches name member)

private theorem referenceParents_complete (graph : Graph) (name : String)
    (path : List String) (fuel : Nat) (parents : List String) (orders : List (List String))
    (step : ∀ parent ∈ parents, ∀ order, GraphDerivation graph parent order →
      referenceVisit graph parent (name :: path) fuel = .ok order)
    (derived : ParentDerivations graph parents orders) :
    parents.mapM (fun parent => referenceVisit graph parent (name :: path) fuel) = .ok orders := by
  induction parents generalizing orders with
  | nil => cases derived; rfl
  | cons parent rest ih =>
    cases derived with
    | cons head tail =>
      have first := step parent (by simp) _ head
      have later := ih _ (fun p hp => step p (by simp [hp])) tail
      simp [List.mapM_cons, first, later, bind, Except.bind, pure, Except.pure]

/-- Every derived cache value executes in the reference traversal at the
production remaining budget. The bound counts actual declared active names. -/
theorem referenceVisit_complete_active (graph : Graph) (name : String)
    (path : List String) (fuel : Nat) (order : List String)
    (active : ActivePath graph name path)
    (bound : graph.length < path.length + fuel)
    (derived : GraphDerivation graph name order) :
    referenceVisit graph name path fuel = .ok order := by
  induction fuel generalizing name path order with
  | zero => have finite := active.length_le; omega
  | succ fuel ih =>
    have fresh := active.fresh derived
    cases derived with
    | @node _ entry orders tail found parents source certified =>
      have children := referenceParents_complete graph name path fuel entry.2 orders
        (fun parent member order proof =>
          ih parent (name :: path) order (active.parent fresh found member)
            (by simp only [List.length_cons]; omega) proof) parents
      obtain ⟨certificate, merged, output⟩ := Precedence.mergeCertified_complete certified
      simp [referenceVisit, fresh, found, children, merged, output,
        bind, Except.bind, pure, Except.pure]

private theorem visitParents_reference (graph : Graph) (name : String)
    (path : List String) (fuel : Nat) (parents : List String)
    (step : ∀ parent ∈ parents, ∀ cache, CacheDerivations graph cache →
      (visit graph parent (name :: path) cache fuel).map Prod.fst =
        referenceVisit graph parent (name :: path) fuel)
    (cache : Cache) (acc : List (List String)) (valid : CacheDerivations graph cache) :
    ((forIn parents (cache, acc) (fun parent state => do
      let result ← visit graph parent (name :: path) state.fst fuel
      pure (ForInStep.yield (result.snd, result.fst :: state.snd)))) :
      Except Error (Cache × List (List String))).map Prod.snd =
    (parents.mapM (fun parent => referenceVisit graph parent (name :: path) fuel)).map
      (fun orders => orders.reverse ++ acc) := by
  induction parents generalizing cache acc with
  | nil => simp [Except.map, List.forIn_nil, List.mapM_nil, pure, Except.pure]
  | cons parent rest ih =>
    have coherent := step parent (by simp) cache valid
    simp only [List.forIn_cons, List.mapM_cons]
    rw [← coherent]
    cases first : visit graph parent (name :: path) cache fuel with
    | error err => simp [Except.map, bind, Except.bind]
    | ok pair =>
      obtain ⟨order, updated⟩ := pair
      have updatedValid := (visit_sound graph parent (name :: path) cache fuel
        order updated valid first).2
      simp only [Except.map, bind, Except.bind, pure, Except.pure]
      change ((forIn rest (updated, order :: acc) (fun parent state => do
        let result ← visit graph parent (name :: path) state.fst fuel
        pure (ForInStep.yield (result.snd, result.fst :: state.snd)))) :
        Except Error (Cache × List (List String))).map Prod.snd = _
      rw [ih (fun p hp => step p (by simp [hp])) updated (order :: acc) updatedValid]
      cases remaining : rest.mapM
          (fun parent => referenceVisit graph parent (name :: path) fuel) with
      | error err => rfl
      | ok orders => simp [Except.map, List.reverse_cons, List.append_assoc]

/-- Exact scalar values and errors for every finite graph and every sound
warm cache on an actual active path, at the production remaining budget. -/
theorem visit_reference_active (graph : Graph) (name : String)
    (path : List String) (cache : Cache) (fuel : Nat)
    (active : ActivePath graph name path)
    (bound : graph.length < path.length + fuel)
    (valid : CacheDerivations graph cache) :
    (visit graph name path cache fuel).map Prod.fst = referenceVisit graph name path fuel := by
  induction fuel generalizing name path cache with
  | zero => simp [visit, referenceVisit, Except.map]
  | succ fuel ih =>
    by_cases fresh : name ∈ path
    · simp [visit, referenceVisit, fresh, Except.map, bind, Except.bind]; rfl
    · simp only [visit, referenceVisit, List.contains_iff_mem, fresh, ↓reduceIte]
      cases hit : cache.get? name with
      | some order =>
        have complete := referenceVisit_complete_active graph name path (fuel + 1)
          order active bound (valid name order hit)
        simp [visit, referenceVisit, fresh, hit, Except.map, pure, Except.pure] at complete ⊢
        exact complete.symm
      | none =>
        cases found : graph.find? (fun row => row.1 == name) with
        | none => simp [found, Except.map]; rfl
        | some entry =>
          simp only [found]
          have parents := visitParents_reference graph name path fuel entry.2
            (fun parent member cache cacheValid =>
              ih parent (name :: path) cache (active.parent fresh found member)
                (by simp only [List.length_cons]; omega) cacheValid) cache [] valid
          cases loop : ((forIn entry.2 (cache, []) (fun parent state => do
            let result ← visit graph parent (name :: path) state.fst fuel
            pure (ForInStep.yield (result.snd, result.fst :: state.snd)))) :
              Except Error (Cache × List (List String))) with
          | error err =>
            have source : entry.2.mapM
                (fun parent => referenceVisit graph parent (name :: path) fuel) = .error err := by
              rw [loop] at parents
              cases result : entry.2.mapM
                  (fun parent => referenceVisit graph parent (name :: path) fuel) with
              | error other => simpa [result, Except.map] using parents.symm
              | ok orders => simp [result, Except.map] at parents
            simp [source, Except.map, bind, Except.bind]
          | ok pair =>
            obtain ⟨current, reversed⟩ := pair
            have source : entry.2.mapM
                (fun parent => referenceVisit graph parent (name :: path) fuel) = .ok reversed.reverse := by
              rw [loop] at parents
              cases result : entry.2.mapM
                  (fun parent => referenceVisit graph parent (name :: path) fuel) with
              | error err => simp [result, Except.map] at parents
              | ok orders =>
                have reverseEq : reversed = orders.reverse := by
                  simpa [result, Except.map] using parents
                simp [reverseEq]
            simp only [source, bind, Except.bind]
            cases merged : Precedence.mergeCertified (reversed.reverse ++ [entry.2]) with
            | error err => simp [Except.map]
            | ok certificate => simp [Except.map, pure, Except.pure]

/-- General warm-cache root coherence, including cyclic and malformed graphs. -/
theorem visit_reference_root (graph : Graph) (name : String) (cache : Cache)
    (valid : CacheDerivations graph cache) :
    (visit graph name [] cache (graph.length + 1)).map Prod.fst =
      referenceVisit graph name [] (graph.length + 1) :=
  visit_reference_active graph name [] cache (graph.length + 1)
    (ActivePath.empty graph name) (by simp) valid

/-- Complete cached/reference batch equality for arbitrary finite graphs and
root lists. Includes exact cycle names, missing nodes, inconsistent merges,
validation failures, empty/repeated roots and sound ancestor cache reuse. -/
theorem linearizeMany_eq_uncached (graph : Graph) (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  cases valid : validateGraph graph with
  | error err => exact linearizeMany_eq_uncached_validation_error graph roots err valid
  | ok value =>
    cases value
    apply linearizeMany_eq_uncached_of_visit_coherence graph valid
    intro root cache cacheValid
    rw [visit_reference_root graph root cache cacheValid, ← sourceVisit_reference]
    simp [linearizeUncached, linearizeMany, valid, bind, Except.bind, Except.map,
      pure, Except.pure]

theorem linearize_eq_uncached (graph : Graph) (root : String) :
    linearize graph root = linearizeUncached graph root := by
  cases valid : validateGraph graph with
  | error err => simp [linearize, linearizeUncached, linearizeMany, valid, bind, Except.bind, Except.map]
  | ok value =>
    cases value
    have coherent := visit_reference_root graph root {} (CacheDerivations.empty graph)
    rw [← sourceVisit_reference] at coherent
    simpa [linearize, linearizeUncached, linearizeMany, valid, bind, Except.bind, Except.map,
      pure, Except.pure] using coherent

/-- Package the existing semantic receipt from an actual cached success.
The reference proof follows by general coherence, without executing a replay. -/
def GraphCertificate.of_cached (graph : Graph) (roots : List String)
    (orders : List (List String)) (success : linearizeMany graph roots = .ok orders) :
    GraphCertificate graph roots :=
  ⟨orders, success, by rw [← linearizeMany_eq_uncached graph roots]; exact success⟩

end LeanPoo.Prototype.C3
