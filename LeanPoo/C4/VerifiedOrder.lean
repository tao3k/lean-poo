import LeanPoo.C4.ResolverSoundness

namespace LeanPoo.C4

/-- A reusable successful checked order. Proof fields erase at runtime;
constructing this value does not independently reconstruct shared parents. -/
structure VerifiedOrder (graph : Graph) (root : String) where
  output : List String
  accepted : linearizeChecked graph root = .ok output
  derivation : ∃ tail, GraphTrace graph root output tail

/-- Compile once through the checked resolver and retain its proven contract.
Errors are exactly those of `linearizeChecked`. -/
def linearizeVerified (graph : Graph) (root : String) : Except Error (VerifiedOrder graph root) :=
  match success : linearizeChecked graph root with
  | .error error => .error error
  | .ok output => .ok ⟨output, success, linearizeChecked_graph_sound success⟩

/-- The wrapper preserves both successful outputs and exact error payloads. -/
theorem linearizeVerified_projection :
    (linearizeVerified graph root).map (·.output) = linearizeChecked graph root := by
  unfold linearizeVerified
  split <;> simp_all [Except.map]

namespace VerifiedOrder

theorem compiled (order : VerifiedOrder graph root) : linearize graph root = .ok order.output :=
  LinearizeState.linearizeChecked_ordinary order.accepted

theorem nodup (order : VerifiedOrder graph root) : order.output.Nodup := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.nodup

theorem head (order : VerifiedOrder graph root) : order.output.head? = some root := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.head

theorem length_bound (order : VerifiedOrder graph root) : order.output.length ≤ graph.nodes.length := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.length_bound

theorem unique (first second : VerifiedOrder graph root) : first.output = second.output :=
  Except.ok.inj (first.accepted.symm.trans second.accepted)

theorem covers (order : VerifiedOrder graph root) :
    name ∈ order.output ↔ Ancestor graph name root := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.covers

theorem local_order (order : VerifiedOrder graph root) (found : graph.findNode? root = some node)
    (member : localOrder ∈ node.parentOrders) : localOrder.Sublist order.output := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.local_order found member

theorem ancestor_order (order : VerifiedOrder graph root) (path : Ancestor graph name root) :
    ∃ output tail, GraphTrace graph name output tail ∧ output.Sublist order.output := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.ancestor path

/-- Use a retained order to discharge ordering constraints declared by any
reachable ancestor, without recompiling that ancestor. -/
theorem ancestor_local_order (order : VerifiedOrder graph root)
    (path : Ancestor graph name root) (found : graph.findNode? name = some node)
    (member : constraint ∈ node.parentOrders) : constraint.Sublist order.output := by
  obtain ⟨_, trace⟩ := order.derivation
  exact trace.ancestor_local_order path found member

theorem ancestor_suffix (order : VerifiedOrder graph root) (path : Ancestor graph name root)
    (found : graph.findNode? name = some node) (flag : node.suffix = true) :
    ∃ output tail, GraphTrace graph name output tail ∧ output.IsSuffix order.output := by
  obtain ⟨_, trace⟩ := order.derivation
  obtain ⟨output, tail, ancestorTrace, inherited⟩ := trace.ancestor_tail path
  refine ⟨output, tail, ancestorTrace, ?_⟩
  rw [← ancestorTrace.flagged found flag]
  exact inherited.trans trace.suffix

/-- Answer ancestry from the retained order without another graph traversal.
The root counts as its own ancestor. This is a linear list membership query. -/
def isAncestor (order : VerifiedOrder graph root) (name : String) : Bool :=
  order.output.contains name

theorem isAncestor_iff (order : VerifiedOrder graph root) :
    order.isAncestor name = true ↔ Ancestor graph name root := by
  simpa only [isAncestor, List.contains_iff_mem] using order.covers (name := name)

/-- Bridge the executable query into Lean's `Decidable` interface, so clients
can branch on graph ancestry and receive a proof in either branch. -/
def decideAncestor (order : VerifiedOrder graph root) (name : String) : Decidable (Ancestor graph name root) :=
  if present : name ∈ order.output then .isTrue (order.covers.mp present)
  else .isFalse (fun path => present (order.covers.mpr path))

end VerifiedOrder

/-- A retained verified order with a reusable hash index for ancestry queries. -/
structure AncestryIndex (graph : Graph) (root : String) where
  order : VerifiedOrder graph root
  names : Std.HashSet String
  indexed : ∀ name, names.contains name = true ↔ name ∈ order.output

private theorem inserted_names (names : List String) (seen : Std.HashSet String) (name : String) :
    (names.foldl (fun seen name => seen.insert name) seen).contains name = true ↔
      name ∈ names ∨ seen.contains name = true := by
  induction names generalizing seen with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldl_cons, ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
    simp only [eq_comm (a := first) (b := name)]
    simp only [or_assoc, or_left_comm]

/-- Build the query index once, retaining the same order and all its proofs. -/
def VerifiedOrder.indexAncestors (order : VerifiedOrder graph root) : AncestryIndex graph root :=
  ⟨order, order.output.foldl (fun seen name => seen.insert name) {}, by
    intro name
    simpa using inserted_names order.output ({} : Std.HashSet String) name⟩

namespace AncestryIndex

/-- A hash-set query; neither graph traversal nor list scanning is repeated. -/
def isAncestor (index : AncestryIndex graph root) (name : String) : Bool :=
  index.names.contains name

theorem isAncestor_iff (index : AncestryIndex graph root) :
    index.isAncestor name = true ↔ Ancestor graph name root :=
  (index.indexed name).trans index.order.covers

/-- Reuse the hash query in proof-producing conditionals. -/
def decideAncestor (index : AncestryIndex graph root) (name : String) : Decidable (Ancestor graph name root) :=
  if present : index.isAncestor name = true then .isTrue (index.isAncestor_iff.mp present)
  else .isFalse (fun path => present (index.isAncestor_iff.mpr path))

end AncestryIndex
end LeanPoo.C4
