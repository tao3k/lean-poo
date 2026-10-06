import LeanPoo.Prototype.C3Semantics
import LeanPoo.C4.MergeInvariant

/-! A proof-producing, cache-free finite interpretation of the paper's C3
graph recursion. Each successful node records its parent derivations and the
paper-style merge trace; the path and fuel checks retain typed failure. -/

namespace LeanPoo.Prototype.C3

open LeanPoo.C4

mutual
/-- A source-style derivation of one finite graph node's C3 order. -/
inductive GraphTrace (graph : Graph) : Nat → String → List String → Prop where
  | node {fuel : Nat} {name : String} {entry : String × List String}
      {orders : List (List String)} {tail : List String}
      (lookup : graph.find? (fun row => row.1 == name) = some entry)
      (parents : ParentTraces graph fuel entry.2 orders)
      (merged : SourceTrace (orders ++ [entry.2]) tail)
      (certified : Precedence.Trace (orders ++ [entry.2]) tail) :
      GraphTrace graph (fuel+1) name (name :: tail)

/-- Positional derivations for a node's direct parents or for requested roots. -/
inductive ParentTraces (graph : Graph) : Nat → List String → List (List String) → Prop where
  | nil {fuel : Nat} : ParentTraces graph fuel [] []
  | cons {fuel : Nat} (head : GraphTrace graph fuel parent order)
      (tail : ParentTraces graph fuel parents orders) :
      ParentTraces graph fuel (parent :: parents) (order :: orders)
end

/-- Each graph derivation starts with the requested node. -/
theorem GraphTrace.root_head (trace : GraphTrace graph fuel root output) :
    output.head? = some root := by
  cases trace
  rfl

/-- Every derived node retains its direct-parent order in a duplicate-free
merged tail. The source-style trace is carried by the same node derivation. -/
theorem GraphTrace.parent_order (trace : GraphTrace graph fuel root output) :
    ∃ (entry : String × List String) (tail : List String),
      graph.find? (fun row => row.1 == root) = some entry ∧
      output = root :: tail ∧ entry.2.Sublist tail ∧ tail.Nodup := by
  cases trace with
  | @node fuel name entry orders tail lookup parentTraces merged certified =>
    exact ⟨entry, tail, lookup, rfl, certified.preserves (by simp), certified.nodup⟩

/-- Positional parent/root derivations retain the input cardinality. -/
theorem ParentTraces.length : (trace : ParentTraces graph fuel roots orders) →
    orders.length = roots.length
  | .nil => rfl
  | .cons _ tail => by
    simpa using congrArg Nat.succ tail.length

/-- Extract the first requested root's order and derivation without replay. -/
theorem ParentTraces.head (trace : ParentTraces graph fuel (root :: roots) orders) :
    ∃ order tail, orders = order :: tail ∧ GraphTrace graph fuel root order := by
  cases trace with
  | cons head _ => exact ⟨_, _, rfl, head⟩

private theorem parentTraces_unique_of
    (step : ∀ (root : String) (first second : List String),
      GraphTrace graph fuelLeft root first →
      GraphTrace graph fuelRight root second → first = second)
    (left : ParentTraces graph fuelLeft roots first)
    (right : ParentTraces graph fuelRight roots second) : first = second := by
  induction roots generalizing first second with
  | nil =>
    cases left
    cases right
    rfl
  | cons root rest ih =>
    cases left with
    | cons headLeft tailLeft =>
      cases right with
      | cons headRight tailRight =>
        have head := step root _ _ headLeft headRight
        have tail := ih tailLeft tailRight
        simp [head, tail]

/-- The paper-style recursive graph relation determines a unique output for
the same graph and root, even if successful derivations use different fuels. -/
theorem GraphTrace.unique (left : GraphTrace graph fuelLeft root first)
    (right : GraphTrace graph fuelRight root second) : first = second := by
  induction fuelLeft generalizing fuelRight root first second with
  | zero => cases left
  | succ fuel ih =>
    cases left with
    | @node _ _ entryLeft ordersLeft tailLeft lookupLeft parentsLeft mergedLeft certifiedLeft =>
      cases right with
      | @node _ _ entryRight ordersRight tailRight lookupRight parentsRight mergedRight certifiedRight =>
        have sameEntry : entryLeft = entryRight :=
          Option.some.inj (lookupLeft.symm.trans lookupRight)
        subst entryRight
        have sameParents : ordersLeft = ordersRight :=
          parentTraces_unique_of (fun parent left right a b => ih a b)
            parentsLeft parentsRight
        subst ordersRight
        have sameTail : tailLeft = tailRight := mergedLeft.unique mergedRight
        simp [sameTail]

/-- A list of source-style root derivations determines one positional batch,
independently of the fuel used by either derivation. -/
theorem ParentTraces.unique (left : ParentTraces graph fuelLeft roots first)
    (right : ParentTraces graph fuelRight roots second) : first = second :=
  parentTraces_unique_of (fun _ _ _ a b => a.unique b) left right

mutual
/-- The paper's graph derivation without an execution fuel index. This is
the relation retained for values reused from a cache at a different depth. -/
inductive GraphDerivation (graph : Graph) : String → List String → Prop where
  | node {name : String} {entry : String × List String}
      {orders : List (List String)} {tail : List String}
      (lookup : graph.find? (fun row => row.1 == name) = some entry)
      (parents : ParentDerivations graph entry.2 orders)
      (merged : SourceTrace (orders ++ [entry.2]) tail)
      (certified : Precedence.Trace (orders ++ [entry.2]) tail) :
      GraphDerivation graph name (name :: tail)

/-- Positional parent and root derivations without a common fuel index. -/
inductive ParentDerivations (graph : Graph) :
    List String → List (List String) → Prop where
  | nil : ParentDerivations graph [] []
  | cons (head : GraphDerivation graph parent order)
      (tail : ParentDerivations graph parents orders) :
      ParentDerivations graph (parent :: parents) (order :: orders)
end

/-- A fuel-independent derivation starts with its requested root. -/
theorem GraphDerivation.root_head (trace : GraphDerivation graph root output) :
    output.head? = some root := by
  cases trace
  rfl

/-- The actual direct-parent row is retained, ordered and duplicate-free. -/
theorem GraphDerivation.parent_order (trace : GraphDerivation graph root output) :
    ∃ (entry : String × List String) (tail : List String),
      graph.find? (fun row => row.1 == root) = some entry ∧
      output = root :: tail ∧ entry.2.Sublist tail ∧ tail.Nodup := by
  cases trace with
  | @node name entry orders tail lookup parents merged certified =>
    exact ⟨entry, tail, lookup, rfl, certified.preserves (by simp), certified.nodup⟩

/-- Fuel-independent positional proofs preserve the requested row count. -/
theorem ParentDerivations.length :
    (trace : ParentDerivations graph roots orders) → orders.length = roots.length
  | .nil => rfl
  | .cons _ tail => by simpa using congrArg Nat.succ tail.length

/-- Take the first requested root's derivation without replaying traversal. -/
theorem ParentDerivations.head
    (trace : ParentDerivations graph (root :: roots) orders) :
    ∃ order tail, orders = order :: tail ∧ GraphDerivation graph root order := by
  cases trace with
  | cons head _ => exact ⟨_, _, rfl, head⟩

private theorem parentTraces_erase_of
    (step : ∀ (root : String) (order : List String),
      GraphTrace graph fuel root order → GraphDerivation graph root order)
    (trace : ParentTraces graph fuel roots orders) :
    ParentDerivations graph roots orders := by
  induction roots generalizing orders with
  | nil =>
    cases trace
    exact .nil
  | cons root rest ih =>
    cases trace with
    | cons head tail => exact .cons (step root _ head) (ih tail)

/-- Forget the execution budget while retaining every paper premise. -/
theorem GraphTrace.eraseFuel (trace : GraphTrace graph fuel root output) :
    GraphDerivation graph root output := by
  induction fuel generalizing root output with
  | zero => cases trace
  | succ fuel ih =>
    cases trace with
    | node lookup parents merged certified =>
      exact .node lookup
        (parentTraces_erase_of (fun _ _ head => ih head) parents)
        merged certified

/-- Forget the common execution budget of a positional batch. -/
theorem ParentTraces.eraseFuel (trace : ParentTraces graph fuel roots orders) :
    ParentDerivations graph roots orders :=
  parentTraces_erase_of (fun _ _ head => head.eraseFuel) trace

private theorem graphDerivation_unique_core
    (left : GraphDerivation graph root first) :
    ∀ {second}, GraphDerivation graph root second → first = second :=
  GraphDerivation.recOn
    (motive_1 := fun root first _ =>
      ∀ {second}, GraphDerivation graph root second → first = second)
    (motive_2 := fun roots first _ =>
      ∀ {second}, ParentDerivations graph roots second → first = second)
    left
    (fun lookup parents merged certified ihParents => by
      intro second right
      cases right with
      | @node _ entryRight ordersRight tailRight lookupRight parentsRight mergedRight certifiedRight =>
        have sameEntry := Option.some.inj (lookup.symm.trans lookupRight)
        subst entryRight
        have sameParents := ihParents parentsRight
        subst ordersRight
        have sameTail := merged.unique mergedRight
        simp [sameTail])
    (by
      intro second right
      cases right
      rfl)
    (fun head tail ihHead ihTail => by
      intro second right
      cases right with
      | cons headRight tailRight =>
        have sameHead := ihHead headRight
        have sameTail := ihTail tailRight
        simp [sameHead, sameTail])

/-- The fuel-free paper relation determines a unique root order. -/
theorem GraphDerivation.unique (left : GraphDerivation graph root first)
    (right : GraphDerivation graph root second) : first = second :=
  graphDerivation_unique_core left right

/-- Positional batches of fuel-free paper derivations have unique orders. -/
theorem ParentDerivations.unique (left : ParentDerivations graph roots first)
    (right : ParentDerivations graph roots second) : first = second :=
  by
    induction roots generalizing first second with
    | nil =>
      cases left
      cases right
      rfl
    | cons root rest ih =>
      cases left with
      | cons headLeft tailLeft =>
        cases right with
        | cons headRight tailRight =>
          have head := headLeft.unique headRight
          have tail := ih tailLeft tailRight
          simp [head, tail]

private def sourceVisit (graph : Graph) (name : String) (path : List String) :
    (fuel : Nat) → Except C4.Error {order : List String // GraphTrace graph fuel name order}
  | 0 => .error (.cycle name)
  | fuel+1 => do
    if path.contains name then throw (.cycle name)
    match found : graph.find? (fun row => row.1 == name) with
    | none => throw (.unknownNode name)
    | some entry =>
      let rec parents : (names : List String) →
          Except C4.Error {orders : List (List String) // ParentTraces graph fuel names orders}
        | [] => .ok ⟨[], .nil⟩
        | parent :: rest => do
          let ⟨order, head⟩ ← sourceVisit graph parent (name :: path) fuel
          let ⟨orders, tail⟩ ← parents rest
          return ⟨order :: orders, .cons head tail⟩
      let ⟨orders, traces⟩ ← parents entry.2
      let tail ← mergeCertified (orders ++ [entry.2])
      let trace : GraphTrace graph (fuel+1) name (name :: tail.output) :=
        .node found traces (mergeCertified_sourceTrace _ tail) tail.trace
      return ⟨name :: tail.output, trace⟩

/-- Interpret a validated finite graph without any memoized ancestor order.
The empty-root batch performs exactly the public graph validation. -/
def linearizeUncached (graph : Graph) (root : String) :
    Except C4.Error (List String) := do
  let _ ← linearizeMany graph []
  return (← sourceVisit graph root [] (graph.length+1)).val

/-- Every successful lookup in the graph has no direct parents. Validation is
separate, since duplicate node declarations are still rejected. -/
def FlatGraph (graph : Graph) : Prop :=
  ∀ root entry,
    graph.find? (fun row => row.1 == root) = some entry → entry.2 = []

/-- Certify a flat graph from its finite declaration rows. -/
theorem FlatGraph.of_members (graph : Graph)
    (all : ∀ entry, entry ∈ graph → entry.2 = []) : FlatGraph graph := by
  intro root entry found
  exact all entry (List.mem_of_find?_eq_some found)

private theorem sourceVisit_leaf_at (graph : Graph) (root : String)
    (path : List String) (fuel : Nat) (entry : String × List String)
    (fresh : path.contains root = false)
    (lookup : graph.find? (fun row => row.1 == root) = some entry)
    (leaf : entry.2 = []) :
    (sourceVisit graph root path (fuel+1)).map Subtype.val = .ok [root] := by
  cases entry with
  | mk entryName parents =>
    dsimp at leaf
    subst parents
    simp only [sourceVisit, fresh, Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all
    · rename_i selected found
      have same : selected = (entryName, []) :=
        Option.some.inj (found.symm.trans lookup)
      subst selected
      simp [sourceVisit.parents, mergeCertified,
        bind, Except.bind, Except.map]
      rfl

/-- A single leaf needs no restriction on the other graph rows: its uncached
observation is the singleton order after graph validation. -/
theorem linearizeUncached_leaf (graph : Graph)
    (valid : validateGraph graph = .ok ()) (root : String)
    (entry : String × List String)
    (lookup : graph.find? (fun row => row.1 == root) = some entry)
    (leaf : entry.2 = []) : linearizeUncached graph root = .ok [root] := by
  have emptyOk : linearizeMany graph [] = .ok [] := by
    simp [linearizeMany, valid, bind, Except.bind]
    rfl
  have firstSource :=
    sourceVisit_leaf_at graph root [] graph.length entry rfl lookup leaf
  simpa [linearizeUncached, emptyOk, Except.map, bind, Except.bind,
    pure, Except.pure] using firstSource

/-- A missing root reports the same lookup error regardless of other rows. -/
theorem linearizeUncached_missing (graph : Graph)
    (valid : validateGraph graph = .ok ()) (root : String)
    (missing : graph.find? (fun row => row.1 == root) = none) :
    linearizeUncached graph root = .error (.unknownNode root) := by
  have emptyOk : linearizeMany graph [] = .ok [] := by
    simp [linearizeMany, valid, bind, Except.bind]
    rfl
  have firstSource : sourceVisit graph root [] (graph.length+1) =
      .error (.unknownNode root) := by
    simp [sourceVisit]
    split <;> simp_all <;> rfl
  simp [linearizeUncached, emptyOk, firstSource, bind, Except.bind]

/-- With no direct-parent edges, a validated reference lookup either reports
the missing root or returns its singleton precedence order. -/
theorem linearizeUncached_flat (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (flat : FlatGraph graph)
    (root : String) :
    linearizeUncached graph root =
      match graph.find? (fun row => row.1 == root) with
      | none => .error (.unknownNode root)
      | some _ => .ok [root] := by
  cases lookup : graph.find? (fun row => row.1 == root) with
  | none =>
    simpa [lookup] using linearizeUncached_missing graph valid root lookup
  | some entry =>
    simpa [lookup] using linearizeUncached_leaf graph valid root entry lookup
      (flat root entry lookup)

/-- A root with one direct parent whose own row is a leaf has the ordinary
two-element C3 order, independently of unrelated rows. -/
theorem linearizeUncached_one_leaf_parent (graph : Graph)
    (valid : validateGraph graph = .ok ())
    (root parent : String) (distinct : root ≠ parent)
    (rootLookup : graph.find? (fun row => row.1 == root) = some (root, [parent]))
    (parentLookup : graph.find? (fun row => row.1 == parent) = some (parent, [])) :
    linearizeUncached graph root = .ok [root, parent] := by
  have emptyOk : linearizeMany graph [] = .ok [] := by
    simp [linearizeMany, valid, bind, Except.bind]
    rfl
  cases graph with
  | nil => simp at rootLookup
  | cons row rest =>
    have fresh : [root].contains parent = false := by
      simp [distinct.symm]
    have parentSource := sourceVisit_leaf_at (row :: rest) parent [root]
      rest.length (parent, []) fresh parentLookup rfl
    cases result : sourceVisit (row :: rest) parent [root] (rest.length+1) with
    | error err => simp [result, Except.map] at parentSource
    | ok witness =>
      have order : witness.val = [parent] := by
        simpa [result, Except.map] using parentSource
      have selected : Precedence.choose [[parent], [parent]] = some parent := by
        simp [Precedence.choose, Precedence.heads, Precedence.eligible]
      have finished : Precedence.Trace
          (Precedence.advance [[parent], [parent]] parent) [] :=
        .done (by simp [Precedence.advance, Precedence.advanceOrder])
      obtain ⟨certificate, merged, output⟩ :=
        Precedence.mergeCertified_complete (.step selected finished)
      have rootSource :
          (sourceVisit (row :: rest) root [] ((row :: rest).length+1)).map
            Subtype.val = .ok [root, parent] := by
        simp [sourceVisit]
        split
        · simp_all
        · rename_i selected found
          have same : selected = (root, [parent]) :=
            Option.some.inj (found.symm.trans rootLookup)
          subst selected
          simp only [sourceVisit.parents, result, order, bind, Except.bind,
            pure, Except.pure, Except.map]
          cases certificate with
          | mk certOutput certTrace =>
            dsimp at output
            subst certOutput
            dsimp only [mergeCertified]
            simp only [List.cons_append, List.nil_append]
            rw [merged]
            rfl
      simpa [linearizeUncached, emptyOk, Except.map, bind, Except.bind,
        pure, Except.pure] using rootSource

/-- Every successful uncached order has a recursive paper-style graph trace. -/
theorem linearizeUncached_sound (graph : Graph) (root : String)
    (output : List String) (success : linearizeUncached graph root = .ok output) :
    GraphTrace graph (graph.length+1) root output := by
  unfold linearizeUncached at success
  cases valid : linearizeMany graph [] with
  | error err => simp [valid, bind, Except.bind] at success
  | ok _ =>
    cases result : sourceVisit graph root [] (graph.length+1) with
    | error err => simp [valid, result, bind, Except.bind] at success
    | ok witness =>
      simp [valid, result, bind, Except.bind] at success
      cases success
      exact witness.property

/-- Validate the graph once, then recompute every root and parent occurrence
independently. In particular, an empty root list still validates the graph. -/
def linearizeUncachedMany (graph : Graph) (roots : List String) :
    Except C4.Error (List (List String)) := do
  let _ ← linearizeMany graph []
  roots.mapM (fun root => (sourceVisit graph root [] (graph.length+1)).map Subtype.val)

/-- The one-root uncached batch has exactly the scalar result and error. -/
theorem linearizeUncachedMany_singleton (graph : Graph) (root : String) :
    linearizeUncachedMany graph [root] =
      (linearizeUncached graph root).map (fun order => [order]) := by
  cases valid : linearizeMany graph [] with
  | error err =>
    simp [linearizeUncachedMany, linearizeUncached, valid,
      bind, Except.bind, Except.map]
  | ok _ =>
    cases result : sourceVisit graph root [] (graph.length+1) with
    | error err =>
      simp [linearizeUncachedMany, linearizeUncached, valid, result,
        bind, Except.bind, Except.map]
    | ok witness =>
      simp [linearizeUncachedMany, linearizeUncached, valid, result,
        bind, Except.bind, Except.map]
      rfl

/-- Once both scalar traversals fail with the same error on the first root,
adding any later roots cannot change either batch outcome. -/
theorem linearizeMany_eq_uncached_of_first_scalar_error (graph : Graph)
    (root : String) (rest : List String) (error : C4.Error)
    (cached : linearize graph root = .error error)
    (reference : linearizeUncached graph root = .error error) :
    linearizeMany graph (root :: rest) =
      linearizeUncachedMany graph (root :: rest) := by
  cases valid : validateGraph graph with
  | error err =>
    simp [linearizeMany, linearizeUncachedMany, valid, bind, Except.bind]
  | ok _ =>
    have emptyOk : linearizeMany graph [] = .ok [] := by
      simp [linearizeMany, valid, bind, Except.bind]
      rfl
    unfold linearize at cached
    simp only [valid, bind, Except.bind] at cached
    unfold linearizeUncached at reference
    simp only [emptyOk, bind, Except.bind] at reference
    cases first : visit graph root [] {} (graph.length+1) with
    | ok pair => simp [first, pure, Except.pure] at cached
    | error cachedError =>
      cases source : sourceVisit graph root [] (graph.length+1) with
      | ok witness => simp [source, pure, Except.pure] at reference
      | error sourceError =>
        simp [first] at cached
        simp [source] at reference
        cases cached
        cases reference
        simp [linearizeMany, linearizeUncachedMany, valid,
          List.forIn_cons, List.mapM_cons, first, source,
          bind, Except.bind, Except.map]
        rfl

/-- If the first requested root is absent, neither interpreter reaches the
remaining roots or any cache reuse. The exact validation/unknown-node outcome
agrees for every graph. -/
theorem linearizeMany_eq_uncached_missing_first (graph : Graph)
    (root : String) (rest : List String)
    (missing : graph.find? (fun entry => entry.1 == root) = none) :
    linearizeMany graph (root :: rest) =
      linearizeUncachedMany graph (root :: rest) := by
  cases valid : validateGraph graph with
  | error err =>
    simp [linearizeMany, linearizeUncachedMany, valid, bind, Except.bind]
  | ok _ =>
    have firstCached : visit graph root [] {} (graph.length+1) =
        .error (.unknownNode root) := by
      simp [visit, missing]
      rfl
    have firstSource : sourceVisit graph root [] (graph.length+1) =
        .error (.unknownNode root) := by
      simp [sourceVisit]
      split <;> simp_all <;> rfl
    have cachedScalar : linearize graph root = .error (.unknownNode root) := by
      simp [linearize, valid, firstCached, bind, Except.bind]
    have sourceScalar : linearizeUncached graph root =
        .error (.unknownNode root) := by
      simp [linearizeUncached, linearizeMany, valid, firstSource,
        bind, Except.bind]
      rfl
    exact linearizeMany_eq_uncached_of_first_scalar_error graph root rest
      (.unknownNode root) cachedScalar sourceScalar

/-- A first root whose first direct parent is itself has the same exact
validation/cycle outcome in both interpreters, regardless of later roots. -/
theorem linearizeMany_eq_uncached_self_parent_first (graph : Graph)
    (root : String) (parents rest : List String)
    (found : graph.find? (fun entry => entry.1 == root) =
      some (root, root :: parents)) :
    linearizeMany graph (root :: rest) =
      linearizeUncachedMany graph (root :: rest) := by
  cases valid : validateGraph graph with
  | error err =>
    simp [linearizeMany, linearizeUncachedMany, valid, bind, Except.bind]
  | ok _ =>
    have repeatedCached (fuel : Nat) : visit graph root [root] {} fuel =
        .error (.cycle root) := by
      cases fuel <;> simp [visit, bind, Except.bind]
      rfl
    have firstCached : visit graph root [] {} (graph.length+1) =
        .error (.cycle root) := by
      simp [visit, found, List.forIn_cons, repeatedCached, bind, Except.bind]
    have firstSource : sourceVisit graph root [] (graph.length+1) =
        .error (.cycle root) := by
      have repeatedSource (fuel : Nat) : sourceVisit graph root [root] fuel =
          .error (.cycle root) := by
        cases fuel <;> simp [sourceVisit, bind, Except.bind]
        rfl
      simp [sourceVisit]
      split <;> simp_all [bind, Except.bind]
      subst_vars
      simp [sourceVisit.parents, repeatedSource, bind, Except.bind]
    have cachedScalar : linearize graph root = .error (.cycle root) := by
      simp [linearize, valid, firstCached, bind, Except.bind]
    have sourceScalar : linearizeUncached graph root = .error (.cycle root) := by
      simp [linearizeUncached, linearizeMany, valid, firstSource,
        bind, Except.bind]
      rfl
    exact linearizeMany_eq_uncached_of_first_scalar_error graph root rest
      (.cycle root) cachedScalar sourceScalar

private theorem sourceVisitMany_sound (graph : Graph) (roots : List String)
    (orders : List (List String))
    (success : roots.mapM (fun root =>
      (sourceVisit graph root [] (graph.length+1)).map Subtype.val) = .ok orders) :
    ParentTraces graph (graph.length+1) roots orders := by
  induction roots generalizing orders with
  | nil =>
    change Except.ok [] = Except.ok orders at success
    cases success
    exact .nil
  | cons root rest ih =>
    simp only [List.mapM_cons] at success
    cases first : (sourceVisit graph root [] (graph.length+1)).map Subtype.val with
    | error err => simp [first, bind, Except.bind] at success
    | ok order =>
      cases source : sourceVisit graph root [] (graph.length+1) with
      | error err => simp [source, Except.map] at first
      | ok witness =>
        have valEq : witness.val = order := by simpa [source, Except.map] using first
        subst order
        cases tail : rest.mapM (fun root =>
            (sourceVisit graph root [] (graph.length+1)).map Subtype.val) with
        | error err => simp [first, tail, bind, Except.bind] at success
        | ok tails =>
          simp [first, tail, bind, Except.bind] at success
          cases success
          exact .cons witness.property (ih tails tail)

/-- Successful uncached batch results have one graph derivation per root. -/
theorem linearizeUncachedMany_sound (graph : Graph) (roots : List String)
    (orders : List (List String)) (success : linearizeUncachedMany graph roots = .ok orders) :
    ParentTraces graph (graph.length+1) roots orders := by
  unfold linearizeUncachedMany at success
  cases valid : linearizeMany graph [] with
  | error err => simp [valid, bind, Except.bind] at success
  | ok _ =>
    simp [valid, bind, Except.bind] at success
    exact sourceVisitMany_sound graph roots orders success

/-- Successful uncached orders satisfy the fuel-independent paper relation. -/
theorem linearizeUncached_derivation (graph : Graph) (root : String)
    (output : List String) (success : linearizeUncached graph root = .ok output) :
    GraphDerivation graph root output :=
  (linearizeUncached_sound graph root output success).eraseFuel

/-- Successful uncached batches satisfy the positional paper relation. -/
theorem linearizeUncachedMany_derivation (graph : Graph) (roots : List String)
    (orders : List (List String))
    (success : linearizeUncachedMany graph roots = .ok orders) :
    ParentDerivations graph roots orders :=
  (linearizeUncachedMany_sound graph roots orders success).eraseFuel

end LeanPoo.Prototype.C3
