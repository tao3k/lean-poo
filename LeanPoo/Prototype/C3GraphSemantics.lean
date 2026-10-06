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
