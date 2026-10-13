import LeanPoo.Prototype.MetaPrototype
import LeanPoo.Prototype.C3GraphSemantics

namespace LeanPoo.Prototype.MetaPrototype

inductive Aligned (relation : A → B → Prop) : List A → List B → Prop where
  | nil : Aligned relation [] []
  | cons : relation left right → Aligned relation lefts rights →
      Aligned relation (left :: lefts) (right :: rights)

theorem Aligned.functional (relation : A → B → Prop)
    (single : ∀ a b c, relation a b → relation a c → b = c)
    (left : Aligned relation names first) (right : Aligned relation names second) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | cons head tail ih =>
    cases right with
    | cons next rest => rw [single _ _ _ head next, ih rest]

/-- A captured parent function belongs to the exact registry snapshot. -/
def lookupFunction (registry : Registry α) (name : String) : Except String (Layer α) := do
  let some entry := registry.find? (fun entry => entry.1 == name) | throw s!"unknown super: {name}"
  function entry.2

private def selectLayers (registry : Registry α) : (names : List String) →
    Except String { layers : List (Layer α) //
      Aligned (fun name layer => lookupFunction registry name = .ok layer) names layers }
  | [] => .ok ⟨[], .nil⟩
  | name :: rest =>
    match selected : lookupFunction registry name with
    | .error message => .error message
    | .ok layer => do
      let tail ← selectLayers registry rest
      return ⟨layer :: tail.val, .cons selected tail.property⟩

def CacheAgreement (entry : String × Instance α) (expected : List String) : Prop :=
  precedence entry.2 = .ok (if entry.2.metadata.isNone then [] else expected)

private def checkCaches : (registry : Registry α) → (orders : List (List String)) →
    Except String (PLift (Aligned CacheAgreement registry orders))
  | [], [] => .ok ⟨.nil⟩
  | entry :: rest, expected :: orders =>
    match observed : precedence entry.2 with
    | .error message => .error message
    | .ok retained =>
      if same : retained = (if entry.2.metadata.isNone then [] else expected) then do
        let tail ← checkCaches rest orders
        return ⟨.cons (observed.trans (congrArg Except.ok same)) tail.down⟩
      else .error s!"retained precedence differs from C3: {entry.1}"
  | _, _ => .error "C3 cache cardinality differs from registry"

/-- Frozen metadata and functions carry the paper C3 derivation and exact
parent-cache/function selection proofs. Reuse needs no second traversal. -/
structure Prepared (α : Type) where private mk ::
  graph : C3.Graph
  root : String
  order : List String
  derivation : C3.GraphDerivation graph root order
  registry : Registry α
  parentOrders : List (List String)
  parentDerivations : C3.ParentDerivations graph (registry.map Prod.fst) parentOrders
  caches : Aligned CacheAgreement registry parentOrders
  private metadata : Meta α
  private inherited : List (Layer α)
  selection : Aligned (fun name layer => lookupFunction registry name = .ok layer)
    order.tail inherited
  private parents : List String
  graph_head : graph.head? = some (root, parents)
  private own : Layer α
  capturedParents : metadata.value.lookup .supers = some parents
  capturedFunction : metadata.value.lookup .function = some own

private def capture (value : Option α) (message : String) :
    Except String { captured : α // value = some captured } :=
  match _found : value with
  | none => .error message
  | some item => .ok ⟨item, rfl⟩

private structure Orders (graph : C3.Graph) (name : String) (names : List String) where
  order : List String
  others : List (List String)
  root : C3.GraphDerivation graph name order
  parents : C3.ParentDerivations graph names others

private def computeOrders (graph : C3.Graph) (name : String) (names : List String) :
    Except String (Orders graph name names) :=
  match result : C3.linearizeMany graph (name :: names) with
  | .error _ => .error "invalid C3 registry graph"
  | .ok [] => .error "missing root order"
  | .ok (order :: others) =>
    let source := C3.linearizeMany_derivation graph (name :: names) (order :: others) result
    let root : C3.GraphDerivation graph name order := by cases source; assumption
    let parents : C3.ParentDerivations graph names others := by cases source; assumption
    .ok ⟨order, others, root, parents⟩

/-- Validate caches and capture all three metadata fields on one immutable
registry snapshot. Every admitted order has a source-style C3 derivation. -/
def prepareChecked (name : String) (metadata : Meta α) (registry : Registry α) :
    Except String (Prepared α) := do
  let parents ← capture (metadata.value.lookup .supers) "missing metadata supers"
  let rows ← registry.mapM fun (parent,object) => do return (parent, ← supers object)
  let graph := (name,parents.val) :: rows
  let certified ← computeOrders graph name (registry.map Prod.fst)
  let caches ← checkCaches registry certified.others
  let own ← capture (metadata.value.lookup .function) "missing metadata function"
  let inherited ← selectLayers registry certified.order.tail
  return ⟨graph, name, certified.order, certified.root, registry, certified.others,
    certified.parents, caches.down, metadata, inherited.val, inherited.property,
    parents.val, rfl, own.val, parents.property, own.property⟩

/-- The actual prototype program uses the captured own function followed by
exactly the parent functions selected in the certified precedence order. -/
def Prepared.program (prepared : Prepared α) : Layer α :=
  DelayedProto.composeAll (prepared.own :: prepared.inherited)

theorem Prepared.order_unique (prepared : Prepared α) (order : List String)
    (source : C3.GraphDerivation prepared.graph prepared.root order) :
    prepared.order = order := prepared.derivation.unique source

theorem Prepared.program_selection (prepared : Prepared α) (order : List String)
    (source : C3.GraphDerivation prepared.graph prepared.root order) :
    ∃ layers, Aligned (fun name layer => lookupFunction prepared.registry name = .ok layer)
      order.tail layers ∧ prepared.program = DelayedProto.composeAll (prepared.own :: layers) := by
  rw [← prepared.order_unique order source]
  exact ⟨prepared.inherited, prepared.selection, rfl⟩

def Prepared.frozenMetadata (prepared : Prepared α) : MetaRecord α :=
  { lookup := fun key => match key with
    | .function => some prepared.own
    | .supers => some prepared.parents
    | .precedence => some prepared.order }

/-- Identify the captured program without evaluating an unchecked knot.
The function and each parent layer must come from this exact preparation. -/
theorem Prepared.program_eq (prepared : Prepared α) (own : Layer α) (layers : List (Layer α))
    (ownSelected : prepared.frozenMetadata.lookup .function = some own)
    (parentsSelected : Aligned (fun name layer => lookupFunction prepared.registry name = .ok layer)
      prepared.order.tail layers) : prepared.program = DelayedProto.composeAll (own :: layers) := by
  have sameOwn : prepared.own = own := Option.some.inj ownSelected
  have sameParents := Aligned.functional _
    (fun _ _ _ first second => Except.ok.inj (first.symm.trans second)) prepared.selection parentsSelected
  simp only [program, sameOwn, sameParents]

theorem Prepared.frozen_function (prepared : Prepared α) :
    prepared.frozenMetadata.lookup .function = prepared.metadata.value.lookup .function :=
  prepared.capturedFunction.symm

/-- Successful preparation retains the exact input registry and own function. -/
theorem prepareChecked_origin (name : String) (metadata : Meta α) (registry : Registry α)
    (prepared : Prepared α) (ready : prepareChecked name metadata registry = .ok prepared) :
    prepared.registry = registry ∧ prepared.frozenMetadata.lookup .function = metadata.value.lookup .function := by
  unfold prepareChecked at ready
  simp only [bind, Except.bind] at ready
  repeat' first | contradiction | split at ready
  all_goals cases ready; exact ⟨rfl, Prepared.frozen_function _⟩

/-- Lift compositional layer evidence through the actual captured selection. -/
theorem Prepared.program_property (prepared : Prepared α) (property : Layer α → Prop)
    (identity : property DelayedProto.identity)
    (compose : ∀ child parent, property child → property parent → property (DelayedProto.compose child parent))
    (own : ∀ layer, prepared.frozenMetadata.lookup .function = some layer → property layer)
    (parents : ∀ name layer, lookupFunction prepared.registry name = .ok layer → property layer) :
    property prepared.program := by
  have inherited : ∀ layer ∈ prepared.inherited, property layer := by
    have all {names layers} (selected : Aligned (fun name layer => lookupFunction prepared.registry name = .ok layer) names layers) :
        ∀ layer ∈ layers, property layer := by
      induction selected with
      | nil => simp
      | cons head tail ih =>
        intro layer member
        rcases List.mem_cons.mp member with equal | member
        · subst layer; exact parents _ _ head
        · exact ih layer member
    exact all prepared.selection
  have chain (layers : List (Layer α)) (all : ∀ layer ∈ layers, property layer) :
      property (DelayedProto.composeAll layers) := by
    induction layers with
    | nil => exact identity
    | cons layer rest ih =>
      exact compose layer _ (all layer (by simp)) (ih (fun item member => all item (by simp [member])))
  exact chain (prepared.own :: prepared.inherited) (by
    intro layer member
    rcases List.mem_cons.mp member with equal | member
    · subst layer; exact own _ rfl
    · exact inherited layer member)

theorem Prepared.frozen_supers (prepared : Prepared α) :
    prepared.frozenMetadata.lookup .supers = prepared.metadata.value.lookup .supers :=
  prepared.capturedParents.symm

theorem Prepared.frozen_order (prepared : Prepared α) (order : List String)
    (source : C3.GraphDerivation prepared.graph prepared.root order) :
    prepared.frozenMetadata.lookup .precedence = some order := by
  change some prepared.order = some order
  rw [prepared.order_unique order source]

private theorem caches_sound (registry : Registry α) (orders : List (List String))
    (caches : Aligned CacheAgreement registry orders)
    (source : C3.ParentDerivations graph (registry.map Prod.fst) orders) :
    ∀ entry ∈ registry, entry.2.metadata.isNone = false →
      ∃ order, precedence entry.2 = .ok order ∧ C3.GraphDerivation graph entry.1 order := by
  induction registry generalizing orders with
  | nil => simp
  | cons first rest ih =>
    cases caches with
    | cons head tail =>
      cases source with
      | cons firstSource restSource =>
        intro entry member present
        simp only [List.mem_cons] at member
        rcases member with equal | member
        · subst entry
          exact ⟨_, by simpa [CacheAgreement, present] using head, firstSource⟩
        · exact ih _ tail restSource entry member present

theorem Prepared.parent_cache_sound (prepared : Prepared α)
    (entry : String × Instance α) (member : entry ∈ prepared.registry)
    (present : entry.2.metadata.isNone = false) :
    ∃ order, precedence entry.2 = .ok order ∧ C3.GraphDerivation prepared.graph entry.1 order :=
  caches_sound prepared.registry prepared.parentOrders prepared.caches
    prepared.parentDerivations entry member present

/-- Instantiate an admitted registry plan repeatedly with different base data. -/
unsafe def Prepared.instantiate (prepared : Prepared α) (base : α) : Instance α :=
  let combined := prepared.program
  let fields : Layer (MetaRecord α) := fun _ _ => prepared.frozenMetadata
  let cached := prepared.metadata.extend fields
  { value := DelayedProto.instantiate combined (Thunk.pure base)
    metadata := some cached
    baseFunction := fun _ parent => parent.get }

unsafe def instantiateChecked (name : String) (metadata : Meta α) (registry : Registry α)
    (base : α) : Except String (Instance α) := do
  return (← prepareChecked name metadata registry).instantiate base

end LeanPoo.Prototype.MetaPrototype
