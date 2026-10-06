import LeanPoo.Prototype.C3Semantics

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

/-- Recompute every root and every parent occurrence independently. -/
def linearizeUncachedMany (graph : Graph) (roots : List String) :
    Except C4.Error (List (List String)) :=
  roots.mapM (linearizeUncached graph)

/-- Successful uncached batch results have one graph derivation per root. -/
theorem linearizeUncachedMany_sound (graph : Graph) (roots : List String)
    (orders : List (List String)) (success : linearizeUncachedMany graph roots = .ok orders) :
    ParentTraces graph (graph.length+1) roots orders := by
  induction roots generalizing orders with
  | nil =>
    change Except.ok [] = Except.ok orders at success
    cases success
    exact .nil
  | cons root rest ih =>
    simp only [linearizeUncachedMany, List.mapM_cons] at success
    cases first : linearizeUncached graph root with
    | error err => simp [first, bind, Except.bind] at success
    | ok order =>
      cases tail : rest.mapM (linearizeUncached graph) with
      | error err => simp [first, tail, bind, Except.bind] at success
      | ok tails =>
        simp [first, tail, bind, Except.bind] at success
        cases success
        exact .cons (linearizeUncached_sound graph root order first)
          (ih tails tail)

end LeanPoo.Prototype.C3
