import LeanPoo.Prototype.C3GraphTrace

/-! Optional admission of the production C3 cache against the proof-producing
uncached finite interpreter. -/

namespace LeanPoo.Prototype.C3

open LeanPoo.C4

/-- Every value retained by a memo table has a paper graph derivation.
The relation does not depend on the depth at which the value was computed. -/
def CacheDerivations (graph : Graph) (cache : Cache) : Prop :=
  ∀ (root : String) (order : List String),
    cache.get? root = some order → GraphDerivation graph root order

/-- An empty memo table trivially has no unproved entries. -/
theorem CacheDerivations.empty (graph : Graph) :
    CacheDerivations graph ({} : Cache) := by
  intro root order found
  simp at found

/-- Inserting a newly derived node preserves the memo-table invariant. -/
theorem CacheDerivations.insert (valid : CacheDerivations graph cache)
    (derived : GraphDerivation graph root order) :
    CacheDerivations graph (cache.insert root order) := by
  intro queried candidate found
  rw [Std.HashMap.get?_insert] at found
  split at found
  · rename_i same
    have equalRoot : root = queried := eq_of_beq same
    subst queried
    cases found
    exact derived
  · exact valid queried candidate found

/-- A cache hit backed by the invariant equals any independently derived
paper order for that graph and root. -/
theorem CacheDerivations.agrees (valid : CacheDerivations graph cache)
    (found : cache.get? root = some cached)
    (source : GraphDerivation graph root expected) : cached = expected :=
  (valid root cached found).unique source

private theorem visitParents_sound (graph : Graph) (path : List String) (fuel : Nat)
    (step : ∀ (parent : String) (cache : Cache) (order : List String) (updated : Cache),
      CacheDerivations graph cache →
      visit graph parent path cache fuel = .ok (order, updated) →
      GraphDerivation graph parent order ∧ CacheDerivations graph updated)
    (names : List String) (cache : Cache) (acc : List (List String))
    (final : Cache) (result : List (List String))
    (valid : CacheDerivations graph cache)
    (success : (forIn names (cache, acc) (fun parent state => do
      let __x ← visit graph parent path state.fst fuel
      pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
      Except Error (Cache × List (List String))) = .ok (final, result)) :
    ∃ orders, result = orders.reverse ++ acc ∧
      ParentDerivations graph names orders ∧ CacheDerivations graph final := by
  induction names generalizing cache acc final result with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure] at success
    cases success
    exact ⟨[], by simp, .nil, valid⟩
  | cons parent rest ih =>
    rw [List.forIn_cons] at success
    cases first : visit graph parent path cache fuel with
    | error err => simp [first, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨order, updated⟩ := pair
      have ⟨derived, validUpdated⟩ := step parent cache order updated valid first
      simp [first, bind, Except.bind] at success
      obtain ⟨orders, resultEq, proofs, validFinal⟩ :=
        ih updated (order :: acc) final result validUpdated success
      refine ⟨order :: orders, ?_, .cons derived proofs, validFinal⟩
      simpa [List.reverse_cons, List.append_assoc] using resultEq

/-- A successful production visit yields a paper derivation and preserves the
memo-table invariant, for any recursion budget and any proven incoming cache. -/
theorem visit_sound (graph : Graph) (name : String) (path : List String)
    (cache : Cache) (fuel : Nat) (order : List String) (updated : Cache)
    (valid : CacheDerivations graph cache)
    (success : visit graph name path cache fuel = .ok (order, updated)) :
    GraphDerivation graph name order ∧ CacheDerivations graph updated := by
  induction fuel generalizing name path cache order updated with
  | zero => simp [visit] at success
  | succ fuel ih =>
    simp only [visit] at success
    by_cases inPath : path.contains name = true
    · simp only [inPath, ↓reduceIte] at success
      simp [bind, Except.bind] at success
    · simp only [inPath, Bool.false_eq_true, ↓reduceIte] at success
      cases hit : cache.get? name with
      | some prior =>
        simp only [hit, pure, Except.pure] at success
        cases success
        exact ⟨valid name order hit, valid⟩
      | none =>
        simp only [hit] at success
        cases lookup : graph.find? (fun entry => entry.1 == name) with
        | none => simp [lookup] at success
        | some entry =>
          simp only [lookup] at success
          cases loop : (forIn entry.2 (cache, []) (fun parent state => do
              let __x ← visit graph parent (name :: path) state.fst fuel
              pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
              Except Error (Cache × List (List String))) with
          | error err =>
            rw [loop] at success
            simp [bind, Except.bind] at success
          | ok state =>
            obtain ⟨current, reverseOrders⟩ := state
            obtain ⟨parentOrders, reverseEq, parentProofs, validCurrent⟩ :=
              visitParents_sound graph (name :: path) fuel
                (fun parent cache child next sound success =>
                  ih parent (name :: path) cache child next sound success)
                entry.2 cache [] current reverseOrders valid loop
            simp only [List.append_nil] at reverseEq
            cases merged : Precedence.mergeCertified (reverseOrders.reverse ++ [entry.2]) with
            | error err =>
              rw [loop] at success
              simp only [bind, Except.bind, pure, Except.pure] at success
              rw [merged] at success
              simp at success
            | ok tail =>
              rw [loop] at success
              simp only [bind, Except.bind, pure, Except.pure] at success
              rw [merged] at success
              cases success
              have ordersEq : reverseOrders.reverse = parentOrders := by
                simpa using congrArg List.reverse reverseEq
              subst parentOrders
              have derived : GraphDerivation graph name (name :: tail.output) :=
                .node lookup parentProofs (mergeCertified_sourceTrace _ tail) tail.trace
              exact ⟨derived, validCurrent.insert derived⟩

/-- Every successful scalar production traversal has a paper graph proof. -/
theorem linearize_derivation (graph : Graph) (root : String) (output : List String)
    (success : linearize graph root = .ok output) :
    GraphDerivation graph root output := by
  unfold linearize at success
  cases valid : validateGraph graph with
  | error err => simp [valid, bind, Except.bind] at success
  | ok _ =>
    cases result : visit graph root [] {} (graph.length+1) with
    | error err => simp [valid, result, bind, Except.bind] at success
    | ok pair =>
      obtain ⟨order, updated⟩ := pair
      simp [valid, result, bind, Except.bind] at success
      cases success
      exact (visit_sound graph root [] {} (graph.length+1) output updated
        (CacheDerivations.empty graph) result).1

/-- Every successful shared-cache production batch has a paper derivation
for each requested root, without running the uncached interpreter. -/
theorem linearizeMany_derivation (graph : Graph) (roots : List String)
    (orders : List (List String))
    (success : linearizeMany graph roots = .ok orders) :
    ParentDerivations graph roots orders := by
  unfold linearizeMany at success
  cases valid : validateGraph graph with
  | error err => simp [valid, bind, Except.bind] at success
  | ok _ =>
    simp only [valid, bind, Except.bind, pure, Except.pure] at success
    split at success
    · simp at success
    · rename_i _ result loopEq
      change (forIn roots (({} : Cache), ([] : List (List String)))
        (fun root state => do
          let __x ← visit graph root [] state.fst (graph.length+1)
          pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
        Except Error (Cache × List (List String))) = .ok result at loopEq
      obtain ⟨sourceOrders, reverseEq, source, _⟩ :=
        visitParents_sound graph [] (graph.length+1)
          (fun root cache order updated valid success =>
            visit_sound graph root [] cache (graph.length+1) order updated valid success)
          roots {} [] result.fst result.snd (CacheDerivations.empty graph) loopEq
      simp only [List.append_nil] at reverseEq
      cases success
      simpa [reverseEq] using source

/-- A successful production batch agrees with any paper-style derivation of
the same graph and requested roots; no reference interpreter is rerun. -/
theorem linearizeMany_eq_derivation (graph : Graph) (roots : List String)
    (orders : List (List String))
    (success : linearizeMany graph roots = .ok orders)
    (source : ParentDerivations graph roots expected) : orders = expected :=
  (linearizeMany_derivation graph roots orders success).unique source

/-- Successful production batches preserve positional output cardinality. -/
theorem linearizeMany_order_count (graph : Graph) (roots : List String)
    (orders : List (List String))
    (success : linearizeMany graph roots = .ok orders) :
    orders.length = roots.length :=
  (linearizeMany_derivation graph roots orders success).length

/-- If both executable traversals succeed, their orders coincide on every
graph and root list. The remaining coherence question concerns outcomes. -/
theorem linearizeMany_eq_uncached_success (graph : Graph) (roots : List String)
    (cachedOrders referenceOrders : List (List String))
    (cached : linearizeMany graph roots = .ok cachedOrders)
    (reference : linearizeUncachedMany graph roots = .ok referenceOrders) :
    cachedOrders = referenceOrders :=
  (linearizeMany_derivation graph roots cachedOrders cached).unique
    (linearizeUncachedMany_derivation graph roots referenceOrders reference)

/-- Empty batches now agree on both successful output and graph-validation
errors, for every graph. This also covers duplicate-name and parent errors. -/
theorem linearizeMany_nil_eq_uncached (graph : Graph) :
    linearizeMany graph [] = linearizeUncachedMany graph [] := by
  cases valid : validateGraph graph with
  | error err =>
    simp [linearizeMany, linearizeUncachedMany, valid, bind, Except.bind]
  | ok _ =>
    simp [linearizeMany, linearizeUncachedMany, valid, bind, Except.bind]
    rfl

/-- Every graph-validation failure is identical in both batch APIs, for any
requested roots. No traversal or cache access occurs after that failure. -/
theorem linearizeMany_eq_uncached_validation_error (graph : Graph)
    (roots : List String) (error : C4.Error)
    (invalid : validateGraph graph = .error error) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  simp [linearizeMany, linearizeUncachedMany, invalid, bind, Except.bind]

private theorem uncachedMany_mapM (graph : Graph)
    (valid : validateGraph graph = .ok ()) (roots : List String) :
    linearizeUncachedMany graph roots = roots.mapM (linearizeUncached graph) := by
  have emptyOk : linearizeMany graph [] = .ok [] := by
    simp [linearizeMany, valid, bind, Except.bind]
    rfl
  simp only [linearizeUncachedMany, emptyOk, bind, Except.bind]
  congr 1
  funext root
  simp [linearizeUncached, emptyOk, bind, Except.bind, Except.map]
  rfl

private def batchLoop (graph : Graph) (roots : List String)
    (cache : Cache) (acc : List (List String)) :
    Except C4.Error (Cache × List (List String)) :=
  forIn roots (cache, acc) (fun root state => do
    let result ← visit graph root [] state.fst (graph.length+1)
    pure (ForInStep.yield (result.snd, result.fst :: state.snd)))

private theorem visitMany_coherent (graph : Graph)
    (coherent : ∀ (root : String) (cache : Cache),
      CacheDerivations graph cache →
      (visit graph root [] cache (graph.length+1)).map Prod.fst =
        linearizeUncached graph root)
    (roots : List String) (cache : Cache) (acc : List (List String))
    (valid : CacheDerivations graph cache) :
    (batchLoop graph roots cache acc).map (fun state => state.snd.reverse) =
    (roots.mapM (linearizeUncached graph)).map
      (fun orders => acc.reverse ++ orders) := by
  induction roots generalizing cache acc with
  | nil => simp [batchLoop, List.forIn_nil, List.mapM_nil, pure, Except.pure, Except.map]
  | cons root rest ih =>
    simp only [batchLoop, List.forIn_cons, List.mapM_cons]
    cases first : visit graph root [] cache (graph.length+1) with
    | error err =>
      have scalar : linearizeUncached graph root = .error err := by
        rw [← coherent root cache valid, first]
        rfl
      simp [scalar, bind, Except.bind, Except.map]
    | ok pair =>
      obtain ⟨order, updated⟩ := pair
      have validUpdated : CacheDerivations graph updated :=
        (visit_sound graph root [] cache (graph.length+1)
          order updated valid first).2
      have scalar : linearizeUncached graph root = .ok order := by
        rw [← coherent root cache valid, first]
        rfl
      simp [scalar, bind, Except.bind, Except.map, pure, Except.pure]
      change (batchLoop graph rest updated (order :: acc)).map
          (fun state => state.snd.reverse) = _
      rw [ih updated (order :: acc) validUpdated]
      cases tail : rest.mapM (linearizeUncached graph) with
      | error err => simp [Except.map]
      | ok orders => simp [List.reverse_cons, List.append_assoc, Except.map]

/-- To prove full batch outcome equality on a validated graph, it suffices to
prove one-root `Except` coherence for every memo table whose entries already
have paper derivations. Successful visits preserve that invariant, so the
premise applies to each later requested root, including after cache reuse. -/
theorem linearizeMany_eq_uncached_of_visit_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (coherent : ∀ (root : String) (cache : Cache),
      CacheDerivations graph cache →
      (visit graph root [] cache (graph.length+1)).map Prod.fst =
        linearizeUncached graph root)
    (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  have cached : linearizeMany graph roots =
      (batchLoop graph roots {} []).map (fun state => state.snd.reverse) := by
    simp [linearizeMany, batchLoop, valid, bind, Except.bind, Except.map,
      pure, Except.pure]
  rw [cached, uncachedMany_mapM graph valid roots]
  have h := visitMany_coherent graph coherent roots {} []
    (CacheDerivations.empty graph)
  cases result : roots.mapM (linearizeUncached graph) with
  | error err => simpa [result, Except.map] using h
  | ok orders => simpa [result, Except.map] using h

theorem GraphDerivation.leaf_singleton (graph : Graph)
    (derived : GraphDerivation graph root order)
    (entry : String × List String)
    (lookupLeaf : graph.find? (fun row => row.1 == root) = some entry)
    (leaf : entry.2 = []) : order = [root] := by
  cases derived with
  | @node name derivedEntry orders tail lookup parents merged certified =>
    have sameEntry := Option.some.inj (lookup.symm.trans lookupLeaf)
    subst derivedEntry
    cases entry with
    | mk entryName parentNames =>
      dsimp at leaf
      subst parentNames
      cases parents
      have zero : SourceTrace ([[]] : List (List String)) [] :=
        .done (by simp [removeNulls])
      have tailEmpty : tail = [] := merged.unique zero
      simp [tailEmpty]

/-- A leaf returns its singleton order at every positive fuel and path where
its own name has not already been visited. -/
theorem visit_leaf_at (graph : Graph)
    (root : String) (entry : String × List String)
    (lookup : graph.find? (fun row => row.1 == root) = some entry)
    (leaf : entry.2 = []) (path : List String)
    (fresh : path.contains root = false) (fuel : Nat) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root path cache (fuel+1)).map Prod.fst = .ok [root] := by
  cases hit : cache.get? root with
  | some order =>
    have singleton := (cacheValid root order hit).leaf_singleton graph entry lookup leaf
    have visitHit : visit graph root path cache (fuel+1) =
        .ok (order, cache) := by
      simp only [visit, fresh, Bool.false_eq_true, ↓reduceIte, hit]
      rfl
    simp [visitHit, singleton, Except.map]
  | none =>
    cases entry with
    | mk entryName parents =>
      dsimp at leaf
      subst parents
      simp only [visit, fresh, Bool.false_eq_true, ↓reduceIte, hit, lookup]
      rfl

/-- A leaf row remains a singleton under any derivation-backed memo table,
even when the rest of the graph has parent edges. -/
theorem visit_leaf_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (root : String) (entry : String × List String)
    (lookup : graph.find? (fun row => row.1 == root) = some entry)
    (leaf : entry.2 = []) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  rw [linearizeUncached_leaf graph valid root entry lookup leaf]
  exact visit_leaf_at graph root entry lookup leaf [] (by rfl)
    graph.length cache cacheValid

private theorem visit_leaf_parents (graph : Graph) (root : String)
    (fuel : Nat) (names : List String) (cache : Cache)
    (acc : List (List String))
    (fresh : root ∉ names)
    (leaves : ∀ parent ∈ names,
      graph.find? (fun row => row.1 == parent) = some (parent, []))
    (valid : CacheDerivations graph cache) :
    ∃ updated,
      (forIn names (cache, acc) (fun parent state => do
        let __x ← visit graph parent [root] state.fst (fuel+1)
        pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
        Except Error (Cache × List (List String))) =
        .ok (updated, (names.map (fun parent => [parent])).reverse ++ acc) ∧
      CacheDerivations graph updated := by
  induction names generalizing cache acc with
  | nil =>
    exact ⟨cache, by simp [List.forIn_nil, pure, Except.pure], valid⟩
  | cons parent rest ih =>
    have notRoot : parent ≠ root := by
      intro same
      exact fresh (same ▸ List.mem_cons_self)
    have freshParent : [root].contains parent = false := by
      simp [notRoot]
    have parentLookup := leaves parent List.mem_cons_self
    have parentOrder := visit_leaf_at graph parent (parent, []) parentLookup rfl
      [root] freshParent fuel cache valid
    cases first : visit graph parent [root] cache (fuel+1) with
    | error err => simp [first, Except.map] at parentOrder
    | ok pair =>
      obtain ⟨order, after⟩ := pair
      have orderEq : order = [parent] := by
        simpa [first, Except.map] using parentOrder
      have validAfter : CacheDerivations graph after :=
        (visit_sound graph parent [root] cache (fuel+1)
          order after valid first).2
      have restFresh : root ∉ rest := by
        intro member
        exact fresh (List.mem_cons_of_mem parent member)
      have restLeaves : ∀ name ∈ rest,
          graph.find? (fun row => row.1 == name) = some (name, []) := by
        intro name member
        exact leaves name (List.mem_cons_of_mem parent member)
      obtain ⟨final, tail, validFinal⟩ :=
        ih after (order :: acc) restFresh restLeaves validAfter
      refine ⟨final, ?_, validFinal⟩
      rw [List.forIn_cons]
      simp only [first, bind, Except.bind, pure, Except.pure]
      change (forIn rest (after, order :: acc) (fun parent state => do
        let __x ← visit graph parent [root] state.fst (fuel+1)
        pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
        Except Error (Cache × List (List String))) = _
      rw [tail]
      simp [orderEq, List.reverse_cons, List.append_assoc]

/-- A root with arbitrarily many distinct leaf parents agrees with the
uncached graph interpretation under any derivation-backed shared cache. -/
theorem visit_leaf_parents_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (root : String) (parents : List String)
    (rootLookup : graph.find? (fun row => row.1 == root) = some (root, parents))
    (fresh : root ∉ parents) (nodup : parents.Nodup)
    (leaves : ∀ parent ∈ parents,
      graph.find? (fun row => row.1 == parent) = some (parent, []))
    (cache : Cache) (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  have source : linearizeUncached graph root = .ok (root :: parents) :=
    linearizeUncached_leaf_parents graph valid root parents rootLookup fresh nodup leaves
  have sourceDerived : GraphDerivation graph root (root :: parents) :=
    linearizeUncached_derivation graph root (root :: parents) source
  rw [source]
  cases hit : cache.get? root with
  | some order =>
    have same : order = root :: parents :=
      cacheValid.agrees hit sourceDerived
    have visitHit : visit graph root [] cache (graph.length+1) =
        .ok (order, cache) := by
      simp only [visit, hit]
      rfl
    simp [visitHit, same, Except.map]
  | none =>
    cases graph with
    | nil => simp at rootLookup
    | cons row rest =>
      obtain ⟨updated, loop, _⟩ :=
        visit_leaf_parents (row :: rest) root rest.length parents cache []
          fresh leaves cacheValid
      obtain ⟨certificate, merged, output⟩ :=
        mergeCertified_leaf_parents parents nodup
      simp only [visit, List.contains_nil, Bool.false_eq_true, ↓reduceIte,
        hit, rootLookup]
      have loop' :
          (forIn parents (cache, []) (fun parent state => do
            let __x ← visit (row :: rest) parent [root] state.fst (row :: rest).length
            pure (ForInStep.yield (__x.snd, __x.fst :: state.snd))) :
            Except Error (Cache × List (List String))) =
            .ok (updated, (parents.map (fun parent => [parent])).reverse) := by
        simpa using loop
      rw [loop']
      simp only [bind, Except.bind, pure, Except.pure, Except.map]
      cases certificate with
      | mk certOutput certTrace =>
        dsimp at output
        subst certOutput
        rw [List.reverse_reverse, merged]

/-- The complete cached and uncached result agrees for one root with one
leaf parent, under any cache of proven graph orders. -/
theorem visit_one_leaf_parent_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (root parent : String) (distinct : root ≠ parent)
    (rootLookup : graph.find? (fun row => row.1 == root) = some (root, [parent]))
    (parentLookup : graph.find? (fun row => row.1 == parent) = some (parent, []))
    (cache : Cache) (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  refine visit_leaf_parents_coherence graph valid root [parent] rootLookup ?_ ?_ ?_
    cache cacheValid
  · simp [distinct]
  · simp
  · intro candidate member
    have same : candidate = parent := by simpa using member
    subst candidate
    exact parentLookup

/-- Two distinct leaf parents preserve their declared order with or without
memo hits, including a hit for the second parent after the first is visited. -/
theorem visit_two_leaf_parents_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (root left right : String)
    (rootLeft : root ≠ left) (rootRight : root ≠ right)
    (distinct : left ≠ right)
    (rootLookup : graph.find? (fun row => row.1 == root) =
      some (root, [left, right]))
    (leftLookup : graph.find? (fun row => row.1 == left) = some (left, []))
    (rightLookup : graph.find? (fun row => row.1 == right) = some (right, []))
    (cache : Cache) (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  refine visit_leaf_parents_coherence graph valid root [left, right] rootLookup ?_ ?_ ?_
    cache cacheValid
  · simp [rootLeft, rootRight]
  · simp [distinct]
  · intro candidate member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with same | same
    · subst candidate
      exact leftLookup
    · subst candidate
      exact rightLookup

/-- Every declared node is either a leaf or has one distinct leaf parent.
Different roots may share that parent; roots may be requested repeatedly. -/
def UnaryLeafGraph (graph : Graph) : Prop :=
  ∀ root entry, graph.find? (fun row => row.1 == root) = some entry →
    graph.find? (fun row => row.1 == root) = some (root, []) ∨
      ∃ parent, root ≠ parent ∧
        graph.find? (fun row => row.1 == root) = some (root, [parent]) ∧
        graph.find? (fun row => row.1 == parent) = some (parent, [])

/-- A missing node cannot have a derivation-backed cache entry. Both
interpreters therefore report the same unknown-node error. -/
theorem visit_missing_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ()) (root : String)
    (missing : graph.find? (fun row => row.1 == root) = none)
    (cache : Cache) (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  rw [linearizeUncached_missing graph valid root missing]
  have noHit : cache.get? root = none := by
    cases hit : cache.get? root with
    | none => rfl
    | some order =>
      obtain ⟨_, _, found, _, _, _⟩ :=
        (cacheValid root order hit).parent_order
      simp [missing] at found
  have missingVisit : visit graph root [] cache (graph.length+1) =
      .error (.unknownNode root) := by
    simp only [visit, noHit, missing]
    rfl
  simp [missingVisit, Except.map]

private theorem unary_visit_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (unary : UnaryLeafGraph graph)
    (root : String) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  cases lookup : graph.find? (fun row => row.1 == root) with
  | none =>
    exact visit_missing_coherence graph valid root lookup cache cacheValid
  | some entry =>
    rcases unary root entry lookup with leaf | ⟨parent, distinct, rootLookup, parentLookup⟩
    · exact visit_leaf_coherence graph valid root (root, []) leaf rfl cache cacheValid
    · exact visit_one_leaf_parent_coherence graph valid root parent distinct
        rootLookup parentLookup cache cacheValid

/-- Full cached/uncached `Except` equality for every batch on a validated
unary leaf graph, including shared parents, repeated roots, and late errors. -/
theorem linearizeMany_eq_uncached_unary_leaf (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (unary : UnaryLeafGraph graph) (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots :=
  linearizeMany_eq_uncached_of_visit_coherence graph valid
    (unary_visit_coherence graph valid unary) roots

/-- Every node is a leaf, has one leaf parent, or has two distinct leaf
parents in declared order. Other roots may share either parent. -/
def AtMostTwoLeafGraph (graph : Graph) : Prop :=
  ∀ root entry, graph.find? (fun row => row.1 == root) = some entry →
    (graph.find? (fun row => row.1 == root) = some (root, []) ∨
      ∃ parent, root ≠ parent ∧
        graph.find? (fun row => row.1 == root) = some (root, [parent]) ∧
        graph.find? (fun row => row.1 == parent) = some (parent, [])) ∨
      ∃ left right, root ≠ left ∧ root ≠ right ∧ left ≠ right ∧
        graph.find? (fun row => row.1 == root) = some (root, [left, right]) ∧
        graph.find? (fun row => row.1 == left) = some (left, []) ∧
        graph.find? (fun row => row.1 == right) = some (right, [])

/-- Existing unary-leaf proofs can be used as two-parent-class premises. -/
theorem AtMostTwoLeafGraph.of_unary (graph : Graph)
    (unary : UnaryLeafGraph graph) : AtMostTwoLeafGraph graph := by
  intro root entry lookup
  exact Or.inl (unary root entry lookup)

private theorem atMostTwo_visit_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (bounded : AtMostTwoLeafGraph graph)
    (root : String) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  cases lookup : graph.find? (fun row => row.1 == root) with
  | none =>
    exact visit_missing_coherence graph valid root lookup cache cacheValid
  | some entry =>
    rcases bounded root entry lookup with (leaf | ⟨parent, distinct, rootLookup, parentLookup⟩) |
      ⟨left, right, rootLeft, rootRight, distinct, rootLookup, leftLookup, rightLookup⟩
    · exact visit_leaf_coherence graph valid root (root, []) leaf rfl cache cacheValid
    · exact visit_one_leaf_parent_coherence graph valid root parent distinct
        rootLookup parentLookup cache cacheValid
    · exact visit_two_leaf_parents_coherence graph valid root left right
        rootLeft rootRight distinct rootLookup leftLookup rightLookup cache cacheValid

/-- Exact batch outcomes for validated height-one graphs with at most two
leaf parents per node, arbitrary root lists and shared cache reuse. -/
theorem linearizeMany_eq_uncached_atMostTwoLeaf (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (bounded : AtMostTwoLeafGraph graph) (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots :=
  linearizeMany_eq_uncached_of_visit_coherence graph valid
    (atMostTwo_visit_coherence graph valid bounded) roots

/-- A height-one graph may give each root any finite number of distinct leaf
parents. The stated row shape is checked at every lookup used by traversal. -/
def LeafParentGraph (graph : Graph) : Prop :=
  ∀ root entry, graph.find? (fun row => row.1 == root) = some entry →
    ∃ parents,
      graph.find? (fun row => row.1 == root) = some (root, parents) ∧
      root ∉ parents ∧ parents.Nodup ∧
      ∀ parent ∈ parents,
        graph.find? (fun row => row.1 == parent) = some (parent, [])

private theorem leafParent_visit_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (bounded : LeafParentGraph graph)
    (root : String) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  cases lookup : graph.find? (fun row => row.1 == root) with
  | none =>
    exact visit_missing_coherence graph valid root lookup cache cacheValid
  | some entry =>
    obtain ⟨parents, rootLookup, fresh, nodup, leaves⟩ :=
      bounded root entry lookup
    exact visit_leaf_parents_coherence graph valid root parents
      rootLookup fresh nodup leaves cache cacheValid

/-- Exact cached/uncached `Except` equality on any validated height-one
leaf-parent graph, for arbitrary root lists and shared cache reuse. -/
theorem linearizeMany_eq_uncached_leafParents (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (bounded : LeafParentGraph graph) (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots :=
  linearizeMany_eq_uncached_of_visit_coherence graph valid
    (leafParent_visit_coherence graph valid bounded) roots

private theorem flat_visit_coherence (graph : Graph)
    (valid : validateGraph graph = .ok ()) (flat : FlatGraph graph)
    (root : String) (cache : Cache)
    (cacheValid : CacheDerivations graph cache) :
    (visit graph root [] cache (graph.length+1)).map Prod.fst =
      linearizeUncached graph root := by
  cases hit : cache.get? root with
  | some order =>
    have derived := cacheValid root order hit
    obtain ⟨entry, _, lookup, _, _, _⟩ := derived.parent_order
    exact visit_leaf_coherence graph valid root entry lookup
      (flat root entry lookup) cache cacheValid
  | none =>
    cases lookup : graph.find? (fun row => row.1 == root) with
    | none =>
      rw [linearizeUncached_flat graph valid flat root]
      have visitMissing : visit graph root [] cache (graph.length+1) =
          .error (.unknownNode root) := by
        simp only [visit, hit, lookup]
        rfl
      simp [lookup, visitMissing, Except.map]
    | some entry =>
      exact visit_leaf_coherence graph valid root entry lookup
        (flat root entry lookup) cache cacheValid

/-- For every validated graph with no direct-parent edges, cached and
uncached traversal have the same complete result on arbitrary root lists.
This includes repeated roots, cache hits, and a missing root after earlier
successful requests. -/
theorem linearizeMany_eq_uncached_flat (graph : Graph)
    (valid : validateGraph graph = .ok ()) (flat : FlatGraph graph)
    (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots :=
  linearizeMany_eq_uncached_of_visit_coherence graph valid
    (flat_visit_coherence graph valid flat) roots

inductive GraphAdmissionError where
  | cached (error : C4.Error)
  | reference (error : C4.Error)
  deriving Repr, DecidableEq

/-- Proof that the cached batch agrees with the uncached interpretation on
the exact graph and root list supplied to admission. -/
structure GraphCertificate (graph : Graph) (roots : List String) where
  orders : List (List String)
  cached : linearizeMany graph roots = .ok orders
  reference : linearizeUncachedMany graph roots = .ok orders

/-- An admitted cached batch carries a paper-style recursive trace for every
requested root, including all visited parents and each node's C3 merge. -/
theorem GraphCertificate.source_traces (certificate : GraphCertificate graph roots) :
    ParentTraces graph (graph.length+1) roots certificate.orders :=
  linearizeUncachedMany_sound graph roots certificate.orders certificate.reference

/-- An admitted batch also has a paper derivation independent of the fuel
used at each visited node. This is the form needed for shared cache entries. -/
theorem GraphCertificate.derivations (certificate : GraphCertificate graph roots) :
    ParentDerivations graph roots certificate.orders :=
  linearizeMany_derivation graph roots certificate.orders certificate.cached

/-- Compare an admitted cached batch with any independently supplied
paper-style graph derivations, without rerunning either interpreter. -/
theorem GraphCertificate.eq_source (certificate : GraphCertificate graph roots)
    (source : ParentTraces graph fuel roots output) :
    certificate.orders = output :=
  certificate.source_traces.unique source

/-- Compare an admitted batch with a fuel-independent paper derivation. -/
theorem GraphCertificate.eq_derivation (certificate : GraphCertificate graph roots)
    (source : ParentDerivations graph roots output) :
    certificate.orders = output :=
  certificate.derivations.unique source

/-- A successful admission has as many output rows as requested roots. -/
theorem GraphCertificate.order_count (certificate : GraphCertificate graph roots) :
    certificate.orders.length = roots.length :=
  certificate.source_traces.length

theorem GraphCertificate.agrees (certificate : GraphCertificate graph roots) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  rw [certificate.cached, certificate.reference]

/-- Optional checked admission. It runs the uncached interpreter, so callers
should use `linearizeMany` for ordinary execution and admit only when they
need a graph-level semantic receipt. -/
def certifyGraph (graph : Graph) (roots : List String) :
    Except GraphAdmissionError (GraphCertificate graph roots) :=
  match cached : linearizeMany graph roots with
  | .error error => .error (.cached error)
  | .ok orders =>
    match reference : linearizeUncachedMany graph roots with
    | .error error => .error (.reference error)
    | .ok expected =>
      have same : orders = expected :=
        linearizeMany_eq_uncached_success graph roots orders expected cached reference
      .ok ⟨orders, cached, by simpa [same] using reference⟩

end LeanPoo.Prototype.C3
