import LeanPoo.Object.Nested

/-! Explicit identity authority for composing separately derived snapshots.
The caller identifies shared nodes and selects the left declaration owner;
C4 metadata must agree. Opaque Lean functions are never compared. -/

namespace LeanPoo.Object

universe u v w

inductive SharedMergeError where
  | graph (error : C4.Error)
  | repeatedSharedName (name : String)
  | notShared (name : String)
  | undeclaredCollision (name : String)
  | conflictingMetadata (name : String)
  deriving Repr

private def nodeIndex (nodes : List C4.Node) : Std.HashMap String C4.Node :=
  nodes.foldl (fun table node => table.insert node.name node) {}

private theorem index_preserves (nodes : List C4.Node)
    (table : Std.HashMap String C4.Node) (name : String)
    (present : table.contains name = true) :
    (nodes.foldl (fun table node => table.insert node.name node) table).contains name = true := by
  induction nodes generalizing table with
  | nil => exact present
  | cons node rest ih =>
    simp only [List.foldl_cons]
    apply ih
    simp [Std.HashMap.contains_insert, present]

private theorem index_contains (nodes : List C4.Node)
    (table : Std.HashMap String C4.Node) (node : C4.Node)
    (member : node ∈ nodes) :
    (nodes.foldl (fun table node => table.insert node.name node) table).contains node.name = true := by
  induction nodes generalizing table with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp member with same | member
    · subst first
      apply index_preserves
      simp
    · exact ih (table.insert first.name first) member

private def sharedExtra (left right : Schema Key Value)
    (sharedNames : List String) : Except SharedMergeError (List C4.Node) := do
  left.graph.validate.mapError .graph
  right.graph.validate.mapError .graph
  let leftNodes := nodeIndex left.graph.nodes
  let rightNodes := nodeIndex right.graph.nodes
  let shared ← sharedNames.foldlM (fun shared name => do
    if shared.contains name then throw (.repeatedSharedName name)
    let some leftNode := leftNodes.get? name | throw (.notShared name)
    let some rightNode := rightNodes.get? name | throw (.notShared name)
    unless leftNode == rightNode do throw (.conflictingMetadata name)
    return shared.insert name) ({} : Std.HashSet String)
  let extra ← right.graph.nodes.foldlM (fun extra node => do
    if leftNodes.contains node.name then
      unless shared.contains node.name do throw (.undeclaredCollision node.name)
      return extra
    return node :: extra) ([] : List C4.Node)
  return extra.reverse

/-- Merge two schemas under explicit left authority for listed shared
identities. Each listed name must occur in both graphs, with exactly equal
C4 node metadata. Unlisted overlaps fail. A shared declaration comes only
from the left schema, including when its lookup returns `none`.
Declaration functions are retained lazily rather than inspected. -/
def Schema.mergeSharedFromLeft (left right : Schema Key Value)
    (sharedNames : List String) : Except SharedMergeError (Schema Key Value) :=
  let leftNodes := nodeIndex left.graph.nodes
  (sharedExtra left right sharedNames).map fun extra =>
    { graph := { nodes := left.graph.nodes ++ extra }
      declaration := fun name =>
        if leftNodes.contains name then left.declaration name
        else right.declaration name }

/-- Declaration ownership is an explicit guarantee, not an inferred
extensional equality of the two schemas' opaque functions. -/
theorem Schema.mergeSharedFromLeft_leftDeclaration
    (left right merged : Schema Key Value) (sharedNames : List String)
    (result : left.mergeSharedFromLeft right sharedNames = .ok merged)
    (name : String) (present : ∃ node ∈ left.graph.nodes, node.name = name) :
    merged.declaration name = left.declaration name := by
  unfold Schema.mergeSharedFromLeft at result
  dsimp only at result
  cases extra : sharedExtra left right sharedNames with
  | error error => simp [extra, Except.map] at result
  | ok nodes =>
    simp only [extra, Except.map] at result
    cases result
    obtain ⟨node, member, same⟩ := present
    subst name
    have indexed := index_contains left.graph.nodes {} node member
    simp only [nodeIndex, indexed, ↓reduceIte]

private theorem index_absent (nodes : List C4.Node)
    (table : Std.HashMap String C4.Node) (name : String)
    (initial : table.contains name = false)
    (absent : ∀ node ∈ nodes, node.name ≠ name) :
    (nodes.foldl (fun table node => table.insert node.name node) table).contains name = false := by
  induction nodes generalizing table with
  | nil => exact initial
  | cons first rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [Std.HashMap.contains_insert, initial, absent first (by simp)]
    · intro node member
      exact absent node (by simp [member])

/-- Nodes not owned by the left graph retain the right declaration lookup. -/
theorem Schema.mergeSharedFromLeft_rightDeclaration
    (left right merged : Schema Key Value) (sharedNames : List String)
    (result : left.mergeSharedFromLeft right sharedNames = .ok merged)
    (name : String) (absent : ∀ node ∈ left.graph.nodes, node.name ≠ name) :
    merged.declaration name = right.declaration name := by
  unfold Schema.mergeSharedFromLeft at result
  dsimp only at result
  cases extra : sharedExtra left right sharedNames with
  | error error => simp [extra, Except.map] at result
  | ok nodes =>
    simp only [extra, Except.map] at result
    cases result
    have indexed := index_absent left.graph.nodes {} name (by simp) absent
    simp only [nodeIndex, indexed, Bool.false_eq_true, ↓reduceIte]

inductive SharedCombineError where
  | merge (error : SharedMergeError)
  | c4 (error : C4.Error)
  deriving Repr

/-- Mix two snapshots whose shared identities are explicitly owned by the
receiver. Roots are independent parents, preserving both branch identities
and allowing C4 to order them around their shared ancestors. -/
def Memoized.mixSharedWith {Key : Type u} {Value : Key → Type v}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (left right : Memoized Key Value) (sharedNames : List String)
    (name : String) (declaration : Declaration Key Value := Declaration.empty) :
    Except SharedCombineError (Memoized Key Value) := do
  let schema ← (left.plan.schema.mergeSharedFromLeft right.plan.schema
    sharedNames).mapError .merge
  let plan ← (LeanPoo.mixC4 schema
    { name, parentOrders := [[left.plan.root], [right.plan.root]] }
    declaration).mapError .c4
  return left.rebuild plan

/-- Extend an inherited inner object with another snapshot under explicit
left declaration authority for their shared identities. Absence and earlier
composition errors propagate through the ordinary typed slot method. -/
def Nested.mixSharedWith {Outer : Type u} {Key : Type v} {Value : Key → Type w}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (right : Memoized Key Value) (sharedNames : List String) (name : String) :
    Prototype.SlotSpec Outer
      (Option (Except SharedCombineError (Memoized Key Value))) :=
  Nested.mapInherited fun left => left.mixSharedWith right sharedNames name

end LeanPoo.Object
