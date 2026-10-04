import LeanPoo.C4.VerifiedOrder

namespace LeanPoo.C4

/-- A two-element ordered sublist. On a verified duplicate-free order this is
strict precedence; absent names and self comparison cannot satisfy it. -/
def Precedes (items : List String) (left right : String) : Prop :=
  [left, right].Sublist items

theorem Precedes.included (before : Precedes smaller left right)
    (kept : smaller.Sublist larger) : Precedes larger left right := before.trans kept

/-- Inheritance order: a node precedes every distinct ancestor in its own
original graph derivation. -/
theorem GraphTrace.inheritance_precedes (trace : GraphTrace graph name output tail)
    (path : Ancestor graph base name) (different : base ≠ name) : Precedes output name base := by
  have present := trace.covers.mpr path
  cases trace with
  | node found rows names parents certificate =>
    change [name, base].Sublist (name :: certificate.ancestry.output)
    have member : base ∈ certificate.ancestry.output := by
      simpa only [NodeCertified.output, List.mem_cons, different, false_or] using present
    exact List.Sublist.cons_cons _ (List.singleton_sublist.mpr member)

/-- Query relative order from a retained result without compiling or traversing
the graph again. This scans the precedence list; it is not a hash lookup. -/
def VerifiedOrder.precedes (order : VerifiedOrder graph root) (left right : String) : Bool :=
  [left, right].isSublist order.output

theorem VerifiedOrder.precedes_iff (order : VerifiedOrder graph root) :
    order.precedes left right = true ↔ Precedes order.output left right :=
  List.isSublist_iff_sublist

theorem VerifiedOrder.precedes_irrefl (order : VerifiedOrder graph root) :
    order.precedes name name = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have unique := order.nodup.sublist (order.precedes_iff.mp accepted)
  simp at unique

/-- A successful comparison also proves that both names are graph ancestors. -/
theorem VerifiedOrder.precedes_members (order : VerifiedOrder graph root)
    (accepted : order.precedes left right = true) :
    Ancestor graph left root ∧ Ancestor graph right root := by
  have kept := order.precedes_iff.mp accepted
  exact ⟨order.covers.mp (kept.subset (by simp)), order.covers.mp (kept.subset (by simp))⟩

/-- Pairwise local precedence is retained from any reachable declaration. -/
theorem VerifiedOrder.local_precedes (order : VerifiedOrder graph root)
    (path : Ancestor graph node.name root) (found : graph.findNode? node.name = some node)
    (declared : constraint ∈ node.parentOrders) (before : Precedes constraint left right) :
    order.precedes left right = true :=
  order.precedes_iff.mpr (before.included (order.ancestor_local_order path found declared))

/-- Monotonicity as a client query: an ancestor's successful comparison remains
true in every retained descendant order on the same graph. -/
theorem VerifiedOrder.monotone_precedes (order : VerifiedOrder graph root)
    (ancestorOrder : VerifiedOrder graph ancestor) (path : Ancestor graph ancestor root)
    (before : ancestorOrder.precedes left right = true) : order.precedes left right = true := by
  obtain ⟨output, tail, trace, included⟩ := order.ancestor_order path
  obtain ⟨_, ancestorTrace⟩ := ancestorOrder.derivation
  rw [(trace.unique ancestorTrace).1] at included
  exact order.precedes_iff.mpr ((ancestorOrder.precedes_iff.mp before).included included)

/-- A reachable descendant precedes each of its distinct ancestors in the
root order, not merely in a separately compiled descendant order. -/
theorem VerifiedOrder.inheritance_precedes (order : VerifiedOrder graph root)
    (reachable : Ancestor graph node root) (path : Ancestor graph base node)
    (different : base ≠ node) : order.precedes node base = true := by
  obtain ⟨_, _, trace, included⟩ := order.ancestor_order reachable
  exact order.precedes_iff.mpr ((trace.inheritance_precedes path different).included included)

end LeanPoo.C4
