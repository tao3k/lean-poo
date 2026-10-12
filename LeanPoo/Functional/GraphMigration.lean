import LeanPoo.Functional.ConsumerRevision

/-! Compile an arbitrary next graph/root, retain existing provider state by
name, install new providers, and prove when selected factories survive. -/
namespace LeanPoo.Functional

universe u v w
variable {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
variable [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key]

private def retainedState (registry : IndexedRegistry Context Key Value)
    (newProviders : String → Provider Context Key Value) (name : String) :=
  match registry.entries[name]? with
  | some state => state
  | none => IndexedOverlay.ofProvider (newProviders name)

/-- Retain whole indexed overlays for surviving names. New names receive the
supplied provider; removed names disappear. No factory body executes. -/
def IndexedRegistry.regraph (registry : IndexedRegistry Context Key Value) (graph : C4.Graph)
    (newProviders : String → Provider Context Key Value) : IndexedRegistry Context Key Value :=
  ⟨(graph.nodes.map C4.Node.name).foldl
    (fun table name => table.insert name (retainedState registry newProviders name)) {}⟩

omit [LawfulBEq Key] [DecidableEq Key] in
private theorem retained_lookup (names : List String)
    (state : String → IndexedOverlay Context Key Value)
    (table : Std.HashMap String (IndexedOverlay Context Key Value)) (name : String) :
    (names.foldl (fun table name => table.insert name (state name)) table)[name]? =
      if name ∈ names then some (state name) else table[name]? := by
  induction names generalizing table with
  | nil => simp
  | cons head rest ih =>
    rw [List.foldl_cons, ih]
    by_cases member : name ∈ rest
    · simp [member]
    · by_cases same : head = name
      · subst head; simp [member]
      · simp [member, Ne.symm same, Std.HashMap.getElem?_insert, same]

omit [LawfulBEq Key] [DecidableEq Key] in
theorem IndexedRegistry.regraph_lookup (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (newProviders : String → Provider Context Key Value)
    (member : name ∈ graph.nodes.map C4.Node.name) :
    (registry.regraph graph newProviders).entries[name]? =
      some (retainedState registry newProviders name) := by
  simp [regraph, retained_lookup, member]

omit [DecidableEq Key] in
theorem IndexedRegistry.regraph_missing (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (newProviders : String → Provider Context Key Value)
    (missing : name ∉ graph.nodes.map C4.Node.name) :
    (registry.regraph graph newProviders).dictionary name key = none := by
  simp [regraph, dictionary, retained_lookup, missing]

omit [DecidableEq Key] in
theorem IndexedRegistry.regraph_retained (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (newProviders : String → Provider Context Key Value)
    (member : name ∈ graph.nodes.map C4.Node.name) (found : registry.entries[name]? = some state) :
    (registry.regraph graph newProviders).dictionary name = registry.dictionary name := by
  simp [dictionary, regraph_lookup registry graph newProviders member, retainedState, found]

omit [DecidableEq Key] in
theorem IndexedRegistry.regraph_new (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (newProviders : String → Provider Context Key Value)
    (member : name ∈ graph.nodes.map C4.Node.name) (missing : registry.entries[name]? = none) :
    (registry.regraph graph newProviders).dictionary name = newProviders name := by
  simp [dictionary, regraph_lookup registry graph newProviders member, retainedState, missing]

/-- First selected provider identity, without evaluating its factory. -/
def selectionOrigin (names : List String) (providers : String → Provider Context Key Value)
    (key : Key) : Option String :=
  match names with
  | [] => none
  | name :: rest => if (providers name key).isSome then some name else selectionOrigin rest providers key

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] in
theorem selectionOrigin_none (names : List String) (providers : String → Provider Context Key Value)
    (key : Key) (absent : selectionOrigin names providers key = none) :
    select names providers key = none := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    cases found : providers name key <;> simp_all [selectionOrigin, select]

omit [BEq Key] [Hashable Key] [LawfulBEq Key] [DecidableEq Key] in
theorem selectionOrigin_some (names : List String) (providers : String → Provider Context Key Value)
    (key : Key) (selected : selectionOrigin names providers key = some name) :
    name ∈ names ∧ (providers name key).isSome = true ∧ select names providers key = providers name key := by
  induction names with
  | nil => simp [selectionOrigin] at selected
  | cons head rest ih =>
    cases found : providers head key with
    | none =>
      obtain ⟨member, present, same⟩ := ih (by simpa [selectionOrigin, found] using selected)
      exact ⟨by simp [member], present, by simpa [select, found] using same⟩
    | some factory =>
      have same : head = name := by simpa [selectionOrigin, found] using selected
      subst name
      simp [select, found]

private theorem order_declared (order : C4.VerifiedOrder graph root) (member : name ∈ order.output) :
    name ∈ graph.nodes.map C4.Node.name := by
  obtain ⟨_, _, trace, _⟩ := order.ancestor_order (order.covers.mp member)
  obtain ⟨node, included, same⟩ := trace.declared
  exact List.mem_map.mpr ⟨node, included, same⟩

omit [DecidableEq Key] in
/-- Same winning name is sufficient because regraph retains its exact old
overlay. Same absence also preserves selection. This compares no functions. -/
theorem regraph_selection_same (oldOrder : C4.VerifiedOrder oldGraph oldRoot)
    (nextOrder : C4.VerifiedOrder nextGraph nextRoot) (registry : IndexedRegistry Context Key Value)
    (newProviders : String → Provider Context Key Value) (key : Key)
    (same : selectionOrigin nextOrder.output (registry.regraph nextGraph newProviders).dictionary key =
      selectionOrigin oldOrder.output registry.dictionary key) :
    assemble nextOrder (registry.regraph nextGraph newProviders).dictionary key =
      assemble oldOrder registry.dictionary key := by
  cases old : selectionOrigin oldOrder.output registry.dictionary key with
  | none =>
    have next := selectionOrigin_none nextOrder.output _ key (same.trans old)
    exact next.trans (selectionOrigin_none oldOrder.output _ key old).symm
  | some name =>
    obtain ⟨_, present, first⟩ := selectionOrigin_some oldOrder.output _ key old
    obtain ⟨member, _, next⟩ := selectionOrigin_some nextOrder.output _ key (same.trans old)
    cases found : registry.entries[name]? with
    | none => simp [IndexedRegistry.dictionary, found] at present
    | some state =>
      change select _ _ _ = select _ _ _
      rw [next, first, IndexedRegistry.regraph_retained registry nextGraph newProviders
        (order_declared nextOrder member) found]

inductive GraphMigrationError where
  | graph (error : C4.Error)
  | provider (name : String)
  deriving Repr

structure PreparedGraphMigration (oldRegistry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (root : String) (newProviders : String → Provider Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) where
  index : C4.AncestryIndex graph root
  compiled : C4.linearizeChecked graph root = .ok index.order.output
  registry : IndexedRegistry Context Key Value
  applied : (oldRegistry.regraph graph newProviders).patchTransaction edits = .ok registry

/-- Graph compilation precedes provider edits. All successful state is indexed
by the actual target compilation and completed transaction; no prefix is returned
on a name error. New providers are consulted only for previously absent names. -/
def prepareGraphMigration (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (root : String) (newProviders : String → Provider Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) :
    Except GraphMigrationError (PreparedGraphMigration registry graph root newProviders edits) :=
  match C4.linearizeVerified graph root with
  | .error error => .error (.graph error)
  | .ok order =>
    match applied : (registry.regraph graph newProviders).patchTransaction edits with
    | .error name => .error (.provider name)
    | .ok next => .ok ⟨order.indexAncestors, order.accepted, next, applied⟩

omit [LawfulBEq Key] [DecidableEq Key] in
theorem prepareGraphMigration_graph_error (registry : IndexedRegistry Context Key Value)
    (newProviders : String → Provider Context Key Value) (edits : List (RegistryEdit Context Key Value))
    (failed : C4.linearizeVerified graph root = .error error) :
    prepareGraphMigration registry graph root newProviders edits = .error (.graph error) := by
  simp [prepareGraphMigration, failed]

omit [LawfulBEq Key] [DecidableEq Key] in
theorem prepareGraphMigration_ok_iff (registry : IndexedRegistry Context Key Value)
    (graph : C4.Graph) (root : String) (newProviders : String → Provider Context Key Value)
    (edits : List (RegistryEdit Context Key Value)) :
    (∃ target, prepareGraphMigration registry graph root newProviders edits = .ok target) ↔
      (∃ output, C4.linearizeChecked graph root = .ok output) ∧
      (∃ updated, (registry.regraph graph newProviders).patchTransaction edits = .ok updated) := by
  constructor
  · rintro ⟨target, _⟩
    exact ⟨⟨target.index.order.output, target.compiled⟩, ⟨target.registry, target.applied⟩⟩
  · rintro ⟨⟨output, compiled⟩, ⟨updated, applied⟩⟩
    cases verified : C4.linearizeVerified graph root with
    | error error =>
      have projection := C4.linearizeVerified_projection (graph := graph) (root := root)
      rw [verified, compiled] at projection
      contradiction
    | ok order =>
      unfold prepareGraphMigration
      simp only [verified]
      split
      · rename_i failed
        rw [applied] at failed
        contradiction
      · exact ⟨_, rfl⟩

variable {sourceRegistry : IndexedRegistry Context Key Value} {graph : C4.Graph} {root : String}
variable {newProviders : String → Provider Context Key Value} {edits : List (RegistryEdit Context Key Value)}
variable {keys : List Key}

/-- Compare actual winning identities before edits, then conservatively exclude
edits to any target ancestor at a requested key. Provider bodies are not compared.
The target ancestry and key indices are retained for later revisions. -/
def PreparedGraphMigration.canReuse (target : PreparedGraphMigration sourceRegistry graph root newProviders edits)
    (oldOrder : C4.VerifiedOrder oldGraph oldRoot) (scope : Requirements.KeyIndex keys) : Bool :=
  keys.all (fun key =>
    selectionOrigin target.index.order.output (sourceRegistry.regraph graph newProviders).dictionary key ==
      selectionOrigin oldOrder.output sourceRegistry.dictionary key) &&
    !Requirements.transactionMayAffectIndexed target.index scope edits

/-- A computable reuse decision supplies exact complete preparation equality,
including factory values and first missing errors at all future contexts. -/
theorem PreparedGraphMigration.reuse_preparation
    (target : PreparedGraphMigration sourceRegistry graph root newProviders edits)
    (oldOrder : C4.VerifiedOrder oldGraph oldRoot) (scope : Requirements.KeyIndex keys)
    (retained : target.canReuse oldOrder scope = true) :
    Requirements.prepare (assemble target.index.order target.registry.dictionary) keys =
      Requirements.prepare (assemble oldOrder sourceRegistry.dictionary) keys := by
  have conditions :
      keys.all (fun key =>
        selectionOrigin target.index.order.output (sourceRegistry.regraph graph newProviders).dictionary key ==
          selectionOrigin oldOrder.output sourceRegistry.dictionary key) = true ∧
      Requirements.transactionMayAffectIndexed target.index scope edits = false := by
    simpa [canReuse] using retained
  have unaffected : Requirements.transactionMayAffect target.index keys edits = false := by
    rw [← Requirements.transactionMayAffectIndexed_eq target.index scope edits]
    exact conditions.2
  rw [Requirements.prepare_indexedTransaction_of_unaffected target.index
    (sourceRegistry.regraph graph newProviders) edits keys target.applied unaffected]
  apply Requirements.prepare_congr
  intro key member
  apply regraph_selection_same oldOrder target.index.order sourceRegistry newProviders key
  exact beq_iff_eq.mp ((List.all_eq_true.mp conditions.1) key member)

end LeanPoo.Functional
