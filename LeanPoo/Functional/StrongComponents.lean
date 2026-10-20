import LeanPoo.Functional.FeedbackCache

/-! Finite checked SCC discovery for future generalized prototypes. Edges point
from consumers to dependencies. Certification checks the computed relation;
accepted output denotes exact graph reachability, not sampled fixed-point values. -/
namespace LeanPoo.Functional.StrongComponents

/-- Finite paths, including the empty path. This relation has no fuel bound. -/
inductive Reach {n : Nat} (edge : Fin n → Fin n → Bool) : Fin n → Fin n → Prop
  | refl (a) : Reach edge a a
  | step {a b c} : edge a b = true → Reach edge b c → Reach edge a c

/-- Search all declared successors to the explicit finite depth. -/
def reachable {n : Nat} (edge : Fin n → Fin n → Bool) : Nat → Fin n → Fin n → Bool
  | 0, a, b => decide (a = b)
  | fuel + 1, a, b => decide (a = b) || (List.finRange n).any
      (fun next => edge a next && reachable edge fuel next b)

/-- Every computed positive has an actual path, regardless of certification. -/
theorem reachable_sound {n : Nat} (edge : Fin n → Fin n → Bool) (fuel : Nat)
    (a b : Fin n) (found : reachable edge fuel a b = true) : Reach edge a b := by
  induction fuel generalizing a with
  | zero => simp [reachable] at found; subst b; exact .refl a
  | succ fuel ih =>
    simp only [reachable, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.and_eq_true] at found
    rcases found with same | ⟨next, _, direct, rest⟩
    · subst b; exact .refl a
    · exact .step direct (ih next rest)

/-- Tabulate each bounded path layer once in ordinary immutable vectors.
Every successor query reads the preceding matrix rather than expanding a fresh
recursive search. The fuel, edge order and Boolean short-circuit rule are intact. -/
def reachableLayers {n : Nat} (edge : Fin n → Fin n → Bool) :
    Nat → Vector (Vector Bool n) n
  | 0 => Vector.ofFn (fun a => Vector.ofFn (fun b => decide (a = b)))
  | fuel + 1 =>
    let previous := reachableLayers edge fuel
    Vector.ofFn (fun a => Vector.ofFn (fun b => decide (a = b) ||
      (List.finRange n).any (fun next => edge a next && previous[next.val][b.val])))

/-- Stored layers equal the original bounded search for every finite graph,
depth and pair, including false answers; certification cannot gain new positives. -/
theorem reachableLayers_get {n : Nat} (edge : Fin n → Fin n → Bool)
    (fuel : Nat) (a b : Fin n) :
    (reachableLayers edge fuel)[a.val][b.val] = reachable edge fuel a b := by
  induction fuel generalizing a b with
  | zero => simp [reachableLayers, reachable]
  | succ fuel ih =>
    simp only [reachableLayers, Vector.getElem_ofFn, reachable]
    congr 1
    apply congrArg ((List.finRange n).any)
    funext next
    rw [ih next b]

/-- Prepare each actual successor list once; rejected edges never allocate work
inside the subsequent bounded search. The declared source order is retained. -/
def successors {n : Nat} (edge : Fin n → Fin n → Bool) : Vector (List (Fin n)) n :=
  Vector.ofFn (fun a => (List.finRange n).filter (edge a))

/-- Search prepared adjacency lists rather than rescanning every possible edge
at every recursive position. This still consumes exactly the supplied depth. -/
def reachableRows {n : Nat} (rows : Vector (List (Fin n)) n) : Nat → Fin n → Fin n → Bool
  | 0, a, b => decide (a = b)
  | fuel + 1, a, b => decide (a = b) || rows[a.val].any
      (fun next => reachableRows rows fuel next b)

/-- Filtering absent edges preserves both positive and negative bounded paths. -/
theorem reachableRows_successors {n : Nat} (edge : Fin n → Fin n → Bool)
    (fuel : Nat) (a b : Fin n) :
    reachableRows (successors edge) fuel a b = reachable edge fuel a b := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
    simp only [reachableRows, successors, Vector.getElem_ofFn, List.any_filter, reachable]
    congr 1
    apply congrArg ((List.finRange n).any)
    funext next
    simpa only [successors] using congrArg (fun found => edge a next && found) (ih next)

/-- Inspect each declared edge once during preparation. Single-successor graphs
use prepared sparse traversal; overlapping branches use shared layers. Both
return a full matrix, with identical fuel and source-order failure semantics. -/
def reachableTable {n : Nat} (edge : Fin n → Fin n → Bool) (fuel : Nat) :
    Vector (Vector Bool n) n :=
  let rows := successors edge
  -- List.any keeps executable by-decide certificates kernel-reducible.
  if (List.finRange n).any (fun a => decide (rows[a.val].length > 1)) then reachableLayers edge fuel
  else Vector.ofFn (fun a => Vector.ofFn (fun b => reachableRows rows fuel a b))

/-- Strategy selection preserves every bounded answer, including negative paths;
selection is an optimization decision, never a new acceptance assumption. -/
theorem reachableTable_get {n : Nat} (edge : Fin n → Fin n → Bool)
    (fuel : Nat) (a b : Fin n) :
    (reachableTable edge fuel)[a.val][b.val] = reachable edge fuel a b := by
  unfold reachableTable
  dsimp only
  split
  · exact reachableLayers_get edge fuel a b
  · simp only [Vector.getElem_ofFn, reachableRows_successors]

/-- Composing declared paths supports a reverse traversal without changing the
forward graph or requiring its strongly connected partition in advance. -/
theorem Reach.trans {n : Nat} {edge : Fin n → Fin n → Bool} {a b c : Fin n}
    (first : Reach edge a b) (second : Reach edge b c) : Reach edge a c := by
  induction first with
  | refl => exact second
  | step direct _ ih => exact .step direct (ih second)

/-- Reverse traversal swaps the endpoints of each actual path. -/
theorem Reach.reverse {n : Nat} {edge : Fin n → Fin n → Bool} {a b : Fin n}
    (path : Reach edge a b) : Reach (fun left right => edge right left) b a := by
  induction path with
  | refl => exact .refl _
  | step direct _ ih => exact ih.trans (.step direct (.refl _))

/-- Forward/reverse intersection is exactly mutual reachability. This permits
one pair of traversals per discovered group rather than one set per vertex. -/
theorem forward_reverse_group {n : Nat} (edge : Fin n → Fin n → Bool) (a b : Fin n) :
    (Reach edge a b ∧ Reach (fun left right => edge right left) a b) ↔
      (Reach edge a b ∧ Reach edge b a) := by
  constructor <;> intro ⟨forward, backward⟩
  · exact ⟨forward, backward.reverse⟩
  · exact ⟨forward, backward.reverse⟩

/-- A nontrivial path enters its destination from a distinct predecessor;
trailing self loops cannot manufacture a second member of a component. -/
theorem Reach.entry {n : Nat} {edge : Fin n → Fin n → Bool} {a b : Fin n}
    (path : Reach edge a b) (different : a ≠ b) :
    ∃ prior, prior ≠ b ∧ Reach edge a prior ∧ edge prior b = true := by
  induction path with
  | refl => exact False.elim (different rfl)
  | @step a next b direct rest ih =>
    by_cases same : next = b
    · subst next; exact ⟨a, different, .refl a, direct⟩
    · obtain ⟨prior, distinct, segment, last⟩ := ih same
      exact ⟨prior, distinct, .step direct segment, last⟩

/-- Once assigned nodes are known to belong to distinct completed components,
all other predecessors being assigned certifies a singleton, even with self loops.
This is the invariant required by the traversal-skipping implementation rule. -/
theorem singleton_of_assigned_predecessors {n : Nat} (edge : Fin n → Fin n → Bool)
    (assigned : Fin n → Bool) (a b : Fin n)
    (incoming : ∀ prior, edge prior a = true → prior ≠ a → assigned prior = true)
    (separate : ∀ prior, assigned prior = true → ¬ (Reach edge a prior ∧ Reach edge prior a))
    (forward : Reach edge a b) (backward : Reach edge b a) : a = b := by
  by_cases same : a = b
  · exact same
  · obtain ⟨prior, distinct, segment, last⟩ := backward.entry (Ne.symm same)
    exact False.elim (separate prior (incoming prior last distinct)
      ⟨forward.trans segment, .step last (.refl a)⟩)

/-- A checked finite relation is reflexive, includes every edge, and is transitive. -/
def Laws {n : Nat} (edge rel : Fin n → Fin n → Bool) : Prop :=
  (∀ a, rel a a = true) ∧ (∀ a b, edge a b = true → rel a b = true) ∧
  (∀ a b c, rel a b = true → rel b c = true → rel a c = true)

/-- Accepted discovery retains its computed relation and executable certificate. -/
structure Checked {n : Nat} (edge : Fin n → Fin n → Bool) where
  rel : Fin n → Fin n → Bool
  laws : Laws edge rel
  sound : ∀ a b, rel a b = true → Reach edge a b

/-- Discover with a finite simple-path budget, then check closure. Failure never
returns a partial partition. Universal acceptance for every finite input is not
claimed here; exactness of every accepted result is proved below. The finite
relation is materialized once in standard immutable vectors so certification
reuses the same computed entries, including on larger cyclic component families. -/
def discover {n : Nat} (edge : Fin n → Fin n → Bool) : Option (Checked edge) :=
  let table := reachableTable edge n
  let rel := fun a b => (table.get a).get b
  letI : Decidable (Laws edge rel) := by unfold Laws; infer_instance
  if valid : Laws edge rel then
    some ⟨rel, valid, fun a b found => reachable_sound edge n a b (by
      change table[a.val][b.val] = true at found
      simpa only [table, reachableTable_get] using found)⟩
  else none

/-- Certification removes the search bound from the meaning of accepted results. -/
theorem Checked.exact {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (a b : Fin n) : graph.rel a b = true ↔ Reach edge a b := by
  constructor
  · exact graph.sound a b
  · intro path
    induction path with
    | refl a => exact graph.laws.1 a
    | @step a b c direct rest ih => exact graph.laws.2.2 a b c (graph.laws.2.1 a b direct) ih

/-- SCC membership is mutual exact reachability, including isolated singletons. -/
def Checked.same {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (a b : Fin n) : Bool := graph.rel a b && graph.rel b a

/-- The automatically selected group of a node; no user partition is supplied. -/
def Checked.members {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (a : Fin n) : List (Fin n) := (List.finRange n).filter (graph.same a)

/-- Returned group members coincide exactly with the graph's SCC definition. -/
theorem Checked.mem_members {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (a b : Fin n) : b ∈ graph.members a ↔ Reach edge a b ∧ Reach edge b a := by
  simp [members, same, graph.exact]

/-- Distinct SCCs cannot have paths both ways: such a pair must be one group. -/
theorem Checked.no_quotient_cycle {n : Nat} {edge : Fin n → Fin n → Bool}
    (graph : Checked edge) (a b : Fin n) (forward : Reach edge a b) (back : Reach edge b a) :
    graph.same a b = true := by
  simp [same, (graph.exact a b).mpr forward, (graph.exact b a).mpr back]

/-- Revision seeds include body edits AND membership/footprint changes. Thus a
surviving representative cannot hide a merge or split of its old feedback group. -/
def revisionSeed {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Checked oldEdge) (next : Checked newEdge) (body : Fin n → Bool) (a : Fin n) : Bool :=
  body a || decide (old.members a ≠ next.members a) ||
    (List.finRange n).any (fun b => decide (oldEdge a b ≠ newEdge a b))

/-- Invalidation follows the NEW graph, so removed edges cannot retain old groups.
Any changed footprint is itself a seed before propagation. -/
def Checked.dirty {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (seed : Fin n → Bool) (a : Fin n) : Bool :=
  (List.finRange n).any (fun b => graph.rel a b && seed b)

/-- Every merge/split participant is dirty, regardless of equal observed values. -/
theorem membership_change_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Checked oldEdge) (next : Checked newEdge) (body : Fin n → Bool) (a : Fin n)
    (changed : old.members a ≠ next.members a) : next.dirty (revisionSeed old next body) a = true := by
  simp only [Checked.dirty, List.any_eq_true, Bool.and_eq_true]
  exact ⟨a, by simp, next.laws.1 a, by simp [revisionSeed, changed]⟩

/-- Dirty shared inputs invalidate every transitive reader, across service groups. -/
theorem Checked.reader_dirty {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (seed : Fin n → Bool) (a b : Fin n) (reads : graph.rel a b = true)
    (dirty : graph.dirty seed b = true) : graph.dirty seed a = true := by
  simp only [Checked.dirty, List.any_eq_true, Bool.and_eq_true] at dirty ⊢
  obtain ⟨c, member, path, changed⟩ := dirty
  exact ⟨c, member, graph.laws.2.2 a b c reads path, changed⟩

/-- Invalidation is atomic inside an SCC: no cyclic member is skipped alone. -/
theorem Checked.same_dirty {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (seed : Fin n → Bool) (a b : Fin n) (same : graph.same a b = true) :
    graph.dirty seed a = graph.dirty seed b := by
  have both : graph.rel a b = true ∧ graph.rel b a = true := by
    simpa only [Checked.same, Bool.and_eq_true] using same
  cases ha : graph.dirty seed a <;> cases hb : graph.dirty seed b
  · rfl
  · have := graph.reader_dirty seed a b both.1 hb; simp [ha] at this
  · have := graph.reader_dirty seed b a both.2 ha; simp [hb] at this
  · rfl

/-- Removing or adding a read seeds the consumer even if its observed value is
unchanged; propagation therefore does not depend on the removed old edge. -/
theorem footprint_change_dirty {n : Nat} {oldEdge newEdge : Fin n → Fin n → Bool}
    (old : Checked oldEdge) (next : Checked newEdge) (body : Fin n → Bool) (a b : Fin n)
    (changed : oldEdge a b ≠ newEdge a b) : next.dirty (revisionSeed old next body) a = true := by
  simp only [Checked.dirty, List.any_eq_true, Bool.and_eq_true]
  refine ⟨a, by simp, next.laws.1 a, ?_⟩
  have footprint : (List.finRange n).any (fun b => decide (oldEdge a b ≠ newEdge a b)) = true :=
    List.any_eq_true.mpr ⟨b, by simp, by simp [changed]⟩
  simp only [revisionSeed, footprint, Bool.or_true]

/-- A clean node has no path to any revision seed. This is the precise graph-side
reuse premise; resolver equality and closure correctness remain separate laws. -/
theorem Checked.clean_no_seed {n : Nat} {edge : Fin n → Fin n → Bool} (graph : Checked edge)
    (seed : Fin n → Bool) (a b : Fin n) (clean : graph.dirty seed a = false)
    (path : Reach edge a b) : seed b = false := by
  cases changed : seed b with
  | false => rfl
  | true =>
    have dirty : graph.dirty seed a = true := List.any_eq_true.mpr
      ⟨b, by simp, by simp [(graph.exact a b).mpr path, changed]⟩
    simp [clean] at dirty

end LeanPoo.Functional.StrongComponents
