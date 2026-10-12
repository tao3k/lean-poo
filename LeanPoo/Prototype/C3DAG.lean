import LeanPoo.Prototype.C3GraphSemantics

/-! Complete cached/reference outcome correspondence on finite DAGs.
A rank decreases on every declared edge, including edges to missing nodes.
Missing-node and inconsistent-merge errors are retained exactly. -/
namespace LeanPoo.Prototype.C3

open LeanPoo.C4

/-- A finite acyclic declaration graph, witnessed by a bounded height map.
The bound is the actual production traversal budget. -/
structure DAG (graph : Graph) where
  rank : String → Nat
  bounded : ∀ name, rank name < graph.length + 1
  decreases : ∀ name entry,
    graph.find? (fun row => row.1 == name) = some entry →
    ∀ parent ∈ entry.2, rank parent < rank name

private def Above (rank : String → Nat) (name : String) (path : List String) : Prop :=
  ∀ ancestor ∈ path, rank name < rank ancestor

private theorem Above.fresh (safe : Above rank name path) :
    path.contains name = false := by
  cases h : path.contains name
  · rfl
  · have bad := safe name (List.contains_iff_mem.mp h)
    omega

private theorem Above.parent {rank : String → Nat} {name parent : String}
    {path : List String} (safe : Above rank name path)
    (lower : rank parent < rank name) : Above rank parent (name :: path) := by
  intro ancestor member
  simp only [List.mem_cons] at member
  rcases member with same | member
  · subst ancestor
    exact lower
  · have higher := safe ancestor member
    omega

/-- The proof-free reading of the source traversal. -/
def referenceVisit (graph : Graph) (name : String) (path : List String) :
    Nat → Except Error (List String)
  | 0 => .error (.cycle name)
  | fuel + 1 => do
    if path.contains name then throw (.cycle name)
    let some entry := graph.find? (fun row => row.1 == name) |
      throw (.unknownNode name)
    let orders ← entry.2.mapM (fun parent => referenceVisit graph parent (name :: path) fuel)
    let tail ← Precedence.mergeCertified (orders ++ [entry.2])
    return name :: tail.output

private theorem sourceParents_reference (graph : Graph) (name : String)
    (path : List String) (fuel : Nat)
    (step : ∀ parent,
      (sourceVisit graph parent (name :: path) fuel).map Subtype.val =
        referenceVisit graph parent (name :: path) fuel)
    (parents : List String) :
    (sourceVisit.parents graph name path fuel parents).map Subtype.val =
      parents.mapM (fun parent => referenceVisit graph parent (name :: path) fuel) := by
  induction parents with
  | nil => simp [sourceVisit.parents, Except.map, List.mapM_nil, pure, Except.pure]
  | cons parent rest ih =>
    simp only [sourceVisit.parents, List.mapM_cons]
    rw [← step parent]
    cases first : sourceVisit graph parent (name :: path) fuel with
    | error err => simp [Except.map, bind, Except.bind]
    | ok value =>
      rw [← ih]
      cases tail : sourceVisit.parents graph name path fuel rest with
      | error err => simp [Except.map, bind, Except.bind]
      | ok values => simp [Except.map, bind, Except.bind, pure, Except.pure]

/-- Erasing the source proof preserves every result and error. -/
theorem sourceVisit_reference (graph : Graph) (name : String) (path : List String)
    (fuel : Nat) :
    (sourceVisit graph name path fuel).map Subtype.val = referenceVisit graph name path fuel := by
  induction fuel generalizing name path with
  | zero => simp [sourceVisit, referenceVisit, Except.map]
  | succ fuel ih =>
    simp only [sourceVisit, referenceVisit]
    by_cases fresh : name ∈ path
    · simp [fresh, Except.map, bind, Except.bind]; rfl
    · simp only [List.contains_iff_mem, fresh, ↓reduceIte]
      split
      · rename_i found
        simp [found, Except.map]; rfl
      · rename_i entry found
        simp only [found]
        rw [← sourceParents_reference graph name path fuel
          (fun parent => ih parent (name :: path)) entry.2]
        cases parents : sourceVisit.parents graph name path fuel entry.2 with
        | error err => simp [Except.map, bind, Except.bind]
        | ok values =>
          simp only [Except.map, bind, Except.bind]
          cases merged : Precedence.mergeCertified (values.val ++ [entry.2]) with
          | error err => simp [mergeCertified, merged]
          | ok certificate => simp [mergeCertified, merged, pure, Except.pure]

private theorem referenceParents_complete (graph : Graph) (rank : String → Nat)
    (name : String) (path : List String) (fuel : Nat)
    (step : ∀ parent order, rank parent < fuel → Above rank parent (name :: path) →
      GraphDerivation graph parent order →
      referenceVisit graph parent (name :: path) fuel = .ok order)
    (safe : Above rank name path) (bound : rank name < fuel + 1)
    (parents : List String) (orders : List (List String))
    (lower : ∀ parent ∈ parents, rank parent < rank name)
    (derived : ParentDerivations graph parents orders) :
    parents.mapM (fun parent => referenceVisit graph parent (name :: path) fuel) = .ok orders := by
  induction parents generalizing orders with
  | nil => cases derived; rfl
  | cons parent rest ih =>
    cases derived with
    | @cons _ order _ orders head tail =>
    have edge := lower parent (by simp)
    have parentBound : rank parent < fuel := by omega
    have headOk := step parent order parentBound (safe.parent edge) head
    have tailOk := ih orders (fun p hp => lower p (by simp [hp])) tail
    simp [List.mapM_cons, headOk, tailOk, bind, Except.bind, pure, Except.pure]

/-- Every paper derivation is executable once the rank fits the fuel and
the active path consists only of higher ancestors. -/
private theorem referenceVisit_complete (graph : Graph) (dag : DAG graph)
    (name : String) (path : List String) (fuel : Nat) (order : List String)
    (bound : dag.rank name < fuel) (safe : Above dag.rank name path)
    (derived : GraphDerivation graph name order) :
    referenceVisit graph name path fuel = .ok order := by
  induction fuel generalizing name path order with
  | zero => omega
  | succ fuel ih =>
    cases derived with
    | @node _ entry orders tail found parents source trace =>
      have parentOk := referenceParents_complete graph dag.rank name path fuel
        (fun parent order bound safe derived => ih parent (name :: path) order bound safe derived)
        safe bound entry.2 orders (dag.decreases name entry found) parents
      obtain ⟨certificate, merged, output⟩ := Precedence.mergeCertified_complete trace
      have fresh : name ∉ path := by
        intro member
        have bad := safe name member
        omega
      simp [referenceVisit, fresh, found, parentOk, merged, output,
        bind, Except.bind, pure, Except.pure]

private theorem visitParents_reference (graph : Graph) (rank : String → Nat)
    (name : String) (path : List String) (fuel : Nat)
    (step : ∀ parent cache, rank parent < fuel → Above rank parent (name :: path) →
      CacheDerivations graph cache →
      (visit graph parent (name :: path) cache fuel).map Prod.fst =
        referenceVisit graph parent (name :: path) fuel)
    (safe : Above rank name path) (bound : rank name < fuel + 1)
    (parents : List String) (cache : Cache) (acc : List (List String))
    (valid : CacheDerivations graph cache)
    (lower : ∀ parent ∈ parents, rank parent < rank name) :
    ((forIn parents (cache, acc) (fun parent state => do
      let result ← visit graph parent (name :: path) state.fst fuel
      pure (ForInStep.yield (result.snd, result.fst :: state.snd)))) :
      Except Error (Cache × List (List String))).map Prod.snd =
    (parents.mapM (fun parent => referenceVisit graph parent (name :: path) fuel)).map
      (fun orders => orders.reverse ++ acc) := by
  induction parents generalizing cache acc with
  | nil => simp [Except.map, List.forIn_nil, List.mapM_nil, pure, Except.pure]
  | cons parent rest ih =>
    have edge := lower parent (by simp)
    have parentBound : rank parent < fuel := by omega
    have coherent := step parent cache parentBound (safe.parent edge) valid
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
      rw [ih updated (order :: acc) updatedValid (fun p hp => lower p (by simp [hp]))]
      cases remaining : rest.mapM
          (fun parent => referenceVisit graph parent (name :: path) fuel) with
      | error err => rfl
      | ok orders => simp [Except.map, List.reverse_cons, List.append_assoc]

/-- Complete scalar coherence for any derivation-backed cache, at any
sufficient fuel and any active ancestor path. -/
theorem visit_reference (graph : Graph) (dag : DAG graph)
    (name : String) (path : List String) (cache : Cache) (fuel : Nat)
    (bound : dag.rank name < fuel)
    (safe : ∀ ancestor ∈ path, dag.rank name < dag.rank ancestor)
    (valid : CacheDerivations graph cache) :
    (visit graph name path cache fuel).map Prod.fst =
      referenceVisit graph name path fuel := by
  induction fuel generalizing name path cache with
  | zero => omega
  | succ fuel ih =>
    have above : Above dag.rank name path := safe
    have fresh := above.fresh
    simp only [visit, fresh, Bool.false_eq_true, ↓reduceIte]
    cases hit : cache.get? name with
    | some order =>
      have source := referenceVisit_complete graph dag name path (fuel + 1)
        order bound above (valid name order hit)
      simp [source, Except.map, pure, Except.pure]
    | none =>
      cases found : graph.find? (fun row => row.1 == name) with
      | none =>
        simp only [found, referenceVisit, fresh, Bool.false_eq_true, ↓reduceIte]
        rfl
      | some entry =>
        simp only [found, referenceVisit, fresh, Bool.false_eq_true, ↓reduceIte]
        have parents := visitParents_reference graph dag.rank name path fuel
          (fun parent cache bound safe valid => ih parent (name :: path) cache bound safe valid)
          above bound entry.2 cache [] valid (dag.decreases name entry found)
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

/-- Arbitrary roots and DAG depth, including repeated roots, cache reuse,
missing declarations, merge errors and validation errors. -/
theorem linearizeMany_eq_uncached_dag (graph : Graph) (dag : DAG graph)
    (roots : List String) :
    linearizeMany graph roots = linearizeUncachedMany graph roots := by
  cases valid : validateGraph graph with
  | error err => exact linearizeMany_eq_uncached_validation_error graph roots err valid
  | ok value =>
    cases value
    apply linearizeMany_eq_uncached_of_visit_coherence graph valid
    intro root cache cacheValid
    have complete := visit_reference graph dag root [] cache (graph.length + 1)
      (dag.bounded root) (by simp) cacheValid
    rw [complete, ← sourceVisit_reference]
    simp [linearizeUncached, linearizeMany, valid, bind, Except.bind, Except.map,
      pure, Except.pure]

/-- Finite rank declarations; undeclared names have rank zero. -/
def rankOf (ranks : List (String × Nat)) (name : String) : Nat :=
  ((ranks.find? (fun row => row.1 == name)).map Prod.snd).getD 0

/-- Check a supplied rank map before using its full outcome theorem. -/
def certifyDAG (graph : Graph) (ranks : List (String × Nat)) : Except String (DAG graph) := do
  if bounded : ranks.all (fun row => row.2 < graph.length + 1) = true then
    if decreasing : graph.all (fun row => row.2.all
        (fun parent => rankOf ranks parent < rankOf ranks row.1)) = true then
      return {
        rank := rankOf ranks
        bounded := by
          intro name
          unfold rankOf
          cases found : ranks.find? (fun row => row.1 == name) with
          | none => simp
          | some row =>
            have bound := List.all_eq_true.mp bounded row (List.mem_of_find?_eq_some found)
            simpa using bound
        decreases := by
          intro name entry found parent member
          have matched := List.find?_some
            (p := fun row : String × List String => row.1 == name) found
          change (entry.1 == name) = true at matched
          have same : entry.1 = name := eq_of_beq matched
          have row := List.all_eq_true.mp decreasing entry (List.mem_of_find?_eq_some found)
          have edge := List.all_eq_true.mp row parent member
          simpa [same] using edge }
    else throw "C3 rank does not decrease on every edge"
  else throw "C3 rank exceeds the traversal budget"

private def height (graph : Graph) (name : String) (path : List String) :
    Nat → Except Error Nat
  | 0 => .error (.cycle name)
  | fuel + 1 => do
    if path.contains name then throw (.cycle name)
    match graph.find? (fun row => row.1 == name) with
    | none => return 0
    | some entry =>
      let parents ← entry.2.mapM (fun parent => height graph parent (name :: path) fuel)
      return 1 + parents.foldl max 0

/-- Infer and check ranks from finite declarations. Missing parents retain
rank zero so the subsequent C3 traversal reports its own unknown-node error. -/
def inferDAG (graph : Graph) : Except String (DAG graph) := do
  let ranks ← graph.mapM fun row => do
    let value ← (height graph row.1 [] (graph.length + 1)).mapError
      (fun _ => s!"cyclic C3 ancestry at {row.1}")
    return (row.1, value)
  certifyDAG graph ranks

end LeanPoo.Prototype.C3
