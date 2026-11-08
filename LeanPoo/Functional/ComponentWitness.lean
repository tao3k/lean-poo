-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.DependencyOrderRepair
import Std.Data.HashMap.Lemmas

/-! SCC certificates over the existing LeanPoo path relation. Spanning paths
prove within-group connectivity; strictly decreasing quotient ranks exclude
cross-group mutual reachability. No all-pairs reachability matrix is required.
This is a certificate law, not a proof of an arbitrary host DFS implementation. -/
namespace LeanPoo.Functional.ComponentWitness
open LeanPoo.Functional.StrongComponents

structure Witness {n} (edge : Fin n → Fin n → Bool) where
  owner : Fin n → Fin n
  rank : Fin n → Nat
  toOwner : ∀ x, Reach edge x (owner x)
  fromOwner : ∀ x, Reach edge (owner x) x
  lower : ∀ a b, edge a b = true → owner a ≠ owner b → rank (owner b) < rank (owner a)

theorem path_rank_le {n} {edge : Fin n → Fin n → Bool} (w : Witness edge)
    {a b} (path : Reach edge a b) : w.rank (w.owner b) ≤ w.rank (w.owner a) := by
  induction path with
  | refl => exact Nat.le_refl _
  | @step a next b direct _ ih =>
    by_cases eq : w.owner a = w.owner next
    · simpa only [eq] using ih
    · exact Nat.le_trans ih (Nat.le_of_lt (w.lower a next direct eq))

theorem path_rank_strict {n} {edge : Fin n → Fin n → Bool} (w : Witness edge)
    {a b} (path : Reach edge a b) (different : w.owner a ≠ w.owner b) :
    w.rank (w.owner b) < w.rank (w.owner a) := by
  induction path with
  | refl => exact False.elim (different rfl)
  | @step a next b direct rest ih =>
    by_cases eq : w.owner a = w.owner next
    · have ne : w.owner next ≠ w.owner b := fun h => different (eq.trans h)
      simpa only [eq] using ih ne
    · exact Nat.lt_of_le_of_lt (path_rank_le w rest) (w.lower a next direct eq)

theorem exact_components {n} {edge : Fin n → Fin n → Bool} (w : Witness edge) (a b) :
    w.owner a = w.owner b ↔ (Reach edge a b ∧ Reach edge b a) := by
  constructor
  · intro same
    constructor
    · exact (w.toOwner a).trans (same ▸ w.fromOwner b)
    · exact (w.toOwner b).trans (same.symm ▸ w.fromOwner a)
  · rintro ⟨forward, backward⟩
    by_cases same : w.owner a = w.owner b
    · exact same
    have down := path_rank_strict w forward same
    have back := path_rank_le w backward
    omega

-- Canonical source-order representative selection may rename internal SCC IDs
-- through an injective mapping. It neither merges nor splits any component.
theorem representative_renaming {n} {edge : Fin n → Fin n → Bool} (w : Witness edge)
    (rename : Fin n → Fin n) (injective : Function.Injective rename) (a b) :
    rename (w.owner a) = rename (w.owner b) ↔ (Reach edge a b ∧ Reach edge b a) := by
  rw [injective.eq_iff, exact_components w]

-- Cardinality is read from the already-built group index. Membership is
-- checked once per old group, not by re-scanning a new group for every node.
theorem finite_group_membership_exact {α : Type} {old fresh : List α}
    (uniqueOld : old.Nodup) (uniqueFresh : fresh.Nodup) :
    (old.length = fresh.length ∧ old ⊆ fresh) ↔
      (∀ node, node ∈ old ↔ node ∈ fresh) := by
  classical
  constructor
  · rintro ⟨sameLength, included⟩ node
    constructor
    · intro member
      exact included member
    · intro present
      by_cases member : node ∈ old
      · exact member
      have distinct : (node :: old).Nodup := List.nodup_cons.mpr ⟨member, uniqueOld⟩
      have longer : (node :: old).length ≤ fresh.length :=
        distinct.length_le_of_subset (by
          intro other member
          rcases List.mem_cons.mp member with equal | prior
          · simpa only [equal] using present
          · exact included prior)
      simp only [List.length_cons] at longer
      omega
  · intro same
    exact ⟨Nat.le_antisymm
      (uniqueOld.length_le_of_subset (fun _ h => (same _).mp h))
      (uniqueFresh.length_le_of_subset (fun _ h => (same _).mpr h)),
      fun _ h => (same _).mp h⟩

def SameComponent (before after : Nat → Option Nat) (root : Nat) : Prop :=
  before root ≠ none ∧ after root ≠ none ∧
    ∀ node, before node = before root ↔ after node = after root

theorem same_component_shared_by_old_group {before after : Nat → Option Nat}
    {root member : Nat} (sameOld : before member = before root)
    (unchanged : SameComponent before after root) :
    SameComponent before after member := by
  rcases unchanged with ⟨oldPresent, freshPresent, same⟩
  have sameFresh := (same member).mp sameOld
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sameOld] using oldPresent
  · simpa only [sameFresh] using freshPresent
  · intro node
    simpa only [sameOld, sameFresh] using same node

theorem old_group_verdict_uniform {before after : Nat → Option Nat}
    {root member : Nat} (sameOld : before member = before root) :
    SameComponent before after root ↔ SameComponent before after member :=
  ⟨same_component_shared_by_old_group sameOld,
   same_component_shared_by_old_group sameOld.symm⟩

theorem indexed_group_check_exact {before after : Nat → Option Nat}
    {root : Nat} {old fresh : List Nat}
    (oldPresent : before root ≠ none) (freshPresent : after root ≠ none)
    (uniqueOld : old.Nodup) (uniqueFresh : fresh.Nodup)
    (oldIndex : ∀ node, node ∈ old ↔ before node = before root)
    (freshIndex : ∀ node, node ∈ fresh ↔ after node = after root) :
    (old.length = fresh.length ∧ old ⊆ fresh) ↔ SameComponent before after root := by
  rw [finite_group_membership_exact uniqueOld uniqueFresh]
  constructor
  · intro same
    refine ⟨oldPresent, freshPresent, ?_⟩
    intro node
    exact (oldIndex node).symm.trans ((same node).trans (freshIndex node))
  · intro same node
    exact (oldIndex node).trans ((same.2.2 node).trans (freshIndex node).symm)

theorem absent_before_changed {before after : Nat → Option Nat} {root : Nat}
    (absent : before root = none) : ¬ SameComponent before after root := by
  intro same
  exact same.1 absent

theorem absent_after_changed {before after : Nat → Option Nat} {root : Nat}
    (absent : after root = none) : ¬ SameComponent before after root := by
  intro same
  exact same.2.1 absent

theorem representative_rename_keeps_membership (owner rename : Nat → Nat)
    (injective : Function.Injective rename) (root : Nat) :
    SameComponent (fun node => some (owner node))
      (fun node => some (rename (owner node))) root := by
  refine ⟨by simp, by simp, ?_⟩
  intro node
  simp only [Option.some.injEq]
  exact injective.eq_iff.symm

-- Private discovery representation: concrete HashMap/Array laws.
theorem fresh_discovery_has_capacity {α} {keys entered : List α} {owner : α}
    (unique : entered.Nodup) (supported : entered ⊆ keys)
    (present : owner ∈ keys) (fresh : owner ∉ entered) :
    entered.length < keys.length := by
  have distinct : (owner :: entered).Nodup := List.nodup_cons.mpr ⟨fresh, unique⟩
  have room := distinct.length_le_of_subset (by
    intro key member
    rcases List.mem_cons.mp member with equal | prior
    · simpa only [equal] using present
    · exact supported prior)
  simpa only [List.length_cons, Nat.add_one_le_iff] using room

section IndexedCells
variable {α β : Type} [BEq α] [Hashable α]

def indexedCell (index : Std.HashMap α Nat) (cells : Array β) (owner : α) : Option β :=
  index[owner]?.bind (fun slot => cells[slot]?)

theorem unvisited_has_no_cell (index : Std.HashMap α Nat) (cells : Array β)
    (owner : α) (missing : index[owner]? = none) :
    indexedCell index cells owner = none := by
  simp [indexedCell, missing]

theorem discovered_cell_exact (index : Std.HashMap α Nat) (cells : Array β)
    (owner : α) (slot : Nat) (found : index[owner]? = some slot)
    (bounded : slot < cells.size) :
    indexedCell index cells owner = some cells[slot] := by
  simp [indexedCell, found, bounded]

theorem discovered_write_exact (index : Std.HashMap α Nat) (cells : Array β)
    (owner : α) (slot : Nat) (found : index[owner]? = some slot)
    (bounded : slot < cells.size) (value : β) :
    indexedCell index (cells.set slot value) owner = some value := by
  simp [indexedCell, found, bounded]

theorem other_cell_write_preserves (index : Std.HashMap α Nat) (cells : Array β)
    (owner : α) (slot other : Nat) (found : index[owner]? = some other)
    (bounded : slot < cells.size) (different : slot ≠ other) (value : β) :
    indexedCell index (cells.set slot value) owner = indexedCell index cells owner := by
  simp only [indexedCell, found, Option.bind_some]
  exact Array.getElem?_set_ne bounded different

theorem zero_discovery_is_present [LawfulBEq α] [LawfulHashable α]
    (index : Std.HashMap α Nat) (owner : α) :
    indexedCell (index.insert owner 0) #[true] owner = some true := by
  simp [indexedCell]

theorem next_slot_is_unused (index : Std.HashMap α Nat) (next : Nat)
    (bounded : ∀ (owner : α) (slot : Nat), index[owner]? = some slot → slot < next) :
    ∀ owner : α, index[owner]? ≠ some next := by
  intro owner found
  exact Nat.lt_irrefl next (bounded owner next found)

theorem fresh_slot_preserves_separation [LawfulBEq α] [LawfulHashable α]
    (index : Std.HashMap α Nat) (owner : α) (slot : Nat)
    (separate : ∀ (a b : α) (i : Nat), index[a]? = some i → index[b]? = some i → a = b)
    (unused : ∀ key : α, index[key]? ≠ some slot) :
    ∀ (a b : α) (i : Nat), (index.insert owner slot)[a]? = some i →
      (index.insert owner slot)[b]? = some i → a = b := by
  intro a b i left right
  by_cases aOwner : a = owner
  · subst a
    have same : slot = i := by simpa using left
    subst i
    by_cases bOwner : b = owner
    · exact bOwner.symm
    · have old : index[b]? = some slot := by
        simpa [Std.HashMap.getElem?_insert, bOwner, Ne.symm bOwner] using right
      exact False.elim (unused b old)
  · by_cases bOwner : b = owner
    · subst b
      have same : slot = i := by simpa using right
      subst i
      have old : index[a]? = some slot := by
        simpa [Std.HashMap.getElem?_insert, aOwner, Ne.symm aOwner] using left
      exact False.elim (unused a old)
    · apply separate a b i
      · simpa [Std.HashMap.getElem?_insert, aOwner, Ne.symm aOwner] using left
      · simpa [Std.HashMap.getElem?_insert, bOwner, Ne.symm bOwner] using right
end IndexedCells

structure DiscoveryFrame (α : Type) where
  owner : α
  slot : Nat
  pending : List α

-- The SCC stack and DFS stack may share a private frame. Advancing only the
-- pending tail cannot change the owner/slot observed later when an SCC pops.
theorem frame_advance_preserves_stack_view {α} (frame : DiscoveryFrame α)
    (rest : List α) :
    (({frame with pending := rest}).owner, ({frame with pending := rest}).slot) =
      (frame.owner, frame.slot) := rfl

example : indexedCell ((∅ : Std.HashMap Nat Nat).insert 9 0) #[false] 9 = some false := by
  simp [indexedCell]

-- Algorithm-independent canonical output and conditional selection charges.
def canonicalRepresentative {n} (roster : List (Fin n))
    (owner : Fin n → Fin n) (key : Fin n) : Option (Fin n) :=
  roster.find? (fun member => decide (owner member = owner key))

theorem supported_owner_has_representative {n} (roster : List (Fin n))
    (owner : Fin n → Fin n) (key : Fin n) (present : key ∈ roster) :
    ∃ representative, canonicalRepresentative roster owner key = some representative := by
  induction roster with
  | nil => simp at present
  | cons head tail ih =>
    by_cases same : owner head = owner key
    · exact ⟨head, by simp [canonicalRepresentative, same]⟩
    · have inTail : key ∈ tail := by
        rcases List.mem_cons.mp present with equal | member
        · subst key
          exact False.elim (same rfl)
        · exact member
      obtain ⟨representative, found⟩ := ih inTail
      exact ⟨representative, by simpa [canonicalRepresentative, same] using found⟩

theorem certified_engines_same_representative {n} {edge : Fin n → Fin n → Bool}
    (left right : Witness edge) (roster : List (Fin n)) (key : Fin n) :
    canonicalRepresentative roster left.owner key =
      canonicalRepresentative roster right.owner key := by
  have predicates : (fun member => decide (left.owner member = left.owner key)) =
      (fun member => decide (right.owner member = right.owner key)) := by
    funext member
    have same := (exact_components left member key).trans
      (exact_components right member key).symm
    by_cases present : left.owner member = left.owner key
    · have other := same.mp present
      simp [present, other]
    · have other : right.owner member ≠ right.owner key := fun h => present (same.mpr h)
      simp [present, other]
  unfold canonicalRepresentative
  rw [predicates]

structure EngineCharge where
  capture : Nat
  conversion : Nat
  discovery : Nat
  normalization : Nat
  certificate : Nat
  selection : Nat
  switching : Nat
  peakCells : Nat
  applicable : Bool

def EngineCharge.total (cost : EngineCharge) : Nat :=
  cost.capture + cost.conversion + cost.discovery + cost.normalization +
    cost.certificate + cost.selection + cost.switching

def EngineCharge.admitted (cost : EngineCharge) (budget : Nat) : Prop :=
  cost.applicable = true ∧ cost.peakCells ≤ budget

instance (cost : EngineCharge) (budget : Nat) : Decidable (cost.admitted budget) :=
  inferInstanceAs (Decidable (cost.applicable = true ∧ cost.peakCells ≤ budget))

-- Stable preference: retain the first plan on equal total charge. An operation
-- or memory mismatch is not a reason to silently use an inadmissible fallback.
def choosePair (budget : Nat) (left right : EngineCharge) : Option EngineCharge :=
  if left.admitted budget then
    if right.admitted budget ∧ right.total < left.total then some right else some left
  else if right.admitted budget then some right else none

theorem pair_choice_admitted (budget : Nat) (left right selected : EngineCharge)
    (found : choosePair budget left right = some selected) :
    selected.admitted budget := by
  unfold choosePair at found
  split at found
  · split at found <;> simp_all
  · split at found <;> simp_all

theorem pair_choice_is_candidate (budget : Nat) (left right selected : EngineCharge)
    (found : choosePair budget left right = some selected) :
    selected = left ∨ selected = right := by
  unfold choosePair at found
  split at found
  · split at found <;> simp_all
  · split at found <;> simp_all

theorem pair_choice_minimum (budget : Nat) (left right selected : EngineCharge)
    (found : choosePair budget left right = some selected) :
    (left.admitted budget → selected.total ≤ left.total) ∧
    (right.admitted budget → selected.total ≤ right.total) := by
  unfold choosePair at found
  split at found
  · split at found <;> simp_all <;> omega
  · split at found <;> simp_all

theorem both_refused_is_none (budget : Nat) (left right : EngineCharge)
    (leftNo : ¬left.admitted budget) (rightNo : ¬right.admitted budget) :
    choosePair budget left right = none := by
  simp [choosePair, leftNo, rightNo]

theorem conversion_is_not_free (cost : EngineCharge) :
    cost.total = (cost.capture + cost.discovery + cost.normalization +
      cost.certificate + cost.selection + cost.switching) + cost.conversion := by
  unfold EngineCharge.total
  omega

private def referenceCharge : EngineCharge := ⟨0, 0, 8, 0, 1, 1, 0, 5, true⟩
private def conversionCharge : EngineCharge := ⟨0, 10, 1, 0, 1, 1, 0, 5, true⟩

-- Omitting conversion chooses a different, apparently cheaper plan. This is
-- a modeled counterexample, not a timing threshold for any graph size.
example : (choosePair 5 referenceCharge conversionCharge).map EngineCharge.total = some 10 := rfl
example : (choosePair 5 referenceCharge {conversionCharge with conversion := 0}).map
    EngineCharge.total = some 3 := rfl
example : choosePair 4 referenceCharge conversionCharge = none := rfl

end LeanPoo.Functional.ComponentWitness


namespace LeanPoo.Functional.ComponentWitness
open LeanPoo.Functional.StrongComponents

def withinGroupEdge {n} (edge : Fin n → Fin n → Bool)
    (owner : Fin n → Fin n) (a b : Fin n) : Bool :=
  edge a b && decide (owner a = owner b)

theorem within_edge_is_original {n} {edge : Fin n → Fin n → Bool}
    {owner : Fin n → Fin n} {a b : Fin n}
    (present : withinGroupEdge edge owner a b = true) : edge a b = true := by
  simp only [withinGroupEdge, Bool.and_eq_true] at present
  exact present.1

theorem within_path_is_original {n} {edge : Fin n → Fin n → Bool}
    {owner : Fin n → Fin n} {a b : Fin n}
    (path : Reach (withinGroupEdge edge owner) a b) : Reach edge a b := by
  induction path with
  | refl => exact .refl _
  | step direct _ tail => exact .step (within_edge_is_original direct) tail

-- Restricting to the claimed group commutes with reversing an edge. This
-- supplies precisely the reverse rows needed by an intra-group spanning walk.
theorem reverse_within_same_group {n} (edge : Fin n → Fin n → Bool)
    (owner : Fin n → Fin n) (a b : Fin n) :
    withinGroupEdge (fun x y => edge y x) owner a b =
      withinGroupEdge edge owner b a := by
  by_cases same : owner a = owner b
  · simp [withinGroupEdge, same]
  · simp [withinGroupEdge, same, Ne.symm same]

-- A certified singleton owner has both spanning paths without inspecting an
-- adjacency bucket; cross-group edges still need the independent rank check.
theorem singleton_spans_without_edges {n} (edge : Fin n → Fin n → Bool)
    (owner : Fin n → Fin n) (key : Fin n) (self : owner key = key) :
    Reach edge key (owner key) ∧ Reach edge (owner key) key := by
  rw [self]
  exact ⟨.refl key, .refl key⟩

-- The unchanged quotient law completes the SAME certificate. Pruning reverse
-- rows or singleton visits never permits dropping the cross-group obligation.
theorem pruned_spans_keep_certificate {n} {edge : Fin n → Fin n → Bool}
    (owner : Fin n → Fin n) (rank : Fin n → Nat)
    (forward : ∀ x, Reach (withinGroupEdge edge owner) x (owner x))
    (backward : ∀ x, Reach (withinGroupEdge edge owner) (owner x) x)
    (lower : ∀ a b, edge a b = true → owner a ≠ owner b → rank (owner b) < rank (owner a)) :
    ∀ a b, owner a = owner b ↔ (Reach edge a b ∧ Reach edge b a) := by
  let witness : Witness edge := ⟨owner, rank,
    fun x => within_path_is_original (forward x),
    fun x => within_path_is_original (backward x), lower⟩
  exact exact_components witness

-- Rank storage is retired only after the complete quotient pass. Its later
-- coverage markers cannot be mistaken for numeric rank evidence.
def markCovered (state : Std.HashMap Nat (Sum Nat Unit)) (root : Nat) :=
  state.insert root (.inr ())

theorem coverage_replaces_rank (state : Std.HashMap Nat (Sum Nat Unit)) (root : Nat) :
    (markCovered state root)[root]? = some (.inr ()) := by
  simp [markCovered]

theorem coverage_cannot_supply_rank (state : Std.HashMap Nat (Sum Nat Unit))
    (root rank : Nat) : (markCovered state root)[root]? ≠ some (.inl rank) := by
  simp [markCovered]

theorem coverage_other_group_preserved (state : Std.HashMap Nat (Sum Nat Unit))
    (root other : Nat) (different : other ≠ root) :
    (markCovered state root)[other]? = state[other]? := by
  simp [markCovered, Std.HashMap.getElem?_insert, Ne.symm different]

end LeanPoo.Functional.ComponentWitness


namespace LeanPoo.Functional.ComponentWitness
open LeanPoo.Functional.StrongComponents

-- If the captured edge order itself supplies a strict quotient rank, every
-- claimed singleton is certified. Self loops are allowed. No DFS or SCC-based
-- selector is needed to establish applicability.
theorem ranked_singletons_exact {n} (edge : Fin n → Fin n → Bool)
    (rank : Fin n → Nat)
    (lower : ∀ a b, edge a b = true → a ≠ b → rank b < rank a) :
    ∀ a b, a = b ↔ (Reach edge a b ∧ Reach edge b a) := by
  let witness : Witness edge :=
    ⟨id, rank, fun x => .refl x, fun x => .refl x, lower⟩
  exact exact_components witness

theorem decreasing_source_singletons {n} (edge : Fin n → Fin n → Bool)
    (decreasing : ∀ a b, edge a b = true → a ≠ b → b.val < a.val) :
    ∀ a b, a = b ↔ (Reach edge a b ∧ Reach edge b a) :=
  ranked_singletons_exact edge Fin.val decreasing

theorem increasing_source_singletons {n} (edge : Fin n → Fin n → Bool)
    (increasing : ∀ a b, edge a b = true → a ≠ b → a.val < b.val) :
    ∀ a b, a = b ↔ (Reach edge a b ∧ Reach edge b a) := by
  apply ranked_singletons_exact edge (fun x => n - 1 - x.val)
  intro a b direct different
  have greater := increasing a b direct different
  have bounded := b.isLt
  omega

end LeanPoo.Functional.ComponentWitness

-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
namespace LeanPoo.Functional.ComponentWitness
open LeanPoo.Functional.StrongComponents

-- Classification may stop after both possibilities fail. Capture itself must
-- still acquire and validate every remaining author footprint independently.
def orderFlags {α : Type} (down up : α → Bool) (state : Bool × Bool) :
    List α → Bool × Bool
  | [] => state
  | edge :: rest =>
    if state.1 || state.2 then
      orderFlags down up (state.1 && down edge, state.2 && up edge) rest
    else state

theorem order_flags_exact {α : Type} (down up : α → Bool)
    (state : Bool × Bool) (edges : List α) :
    orderFlags down up state edges =
      (state.1 && edges.all down, state.2 && edges.all up) := by
  induction edges generalizing state with
  | nil => simp [orderFlags]
  | cons edge rest ih =>
    rcases state with ⟨d, u⟩
    cases d <;> cases u <;> simp [orderFlags, ih, List.all_cons]

theorem rejected_flags_remain_rejected {α : Type} (down up : α → Bool)
    (rest : List α) : orderFlags down up (false, false) rest = (false, false) := by
  simp [order_flags_exact]

theorem accepted_down_edge {α : Type} {down up : α → Bool}
    {edges : List α} {edge : α} (member : edge ∈ edges)
    (accepted : (orderFlags down up (true, true) edges).1 = true) :
    down edge = true := by
  have all : edges.all down = true := by simpa [order_flags_exact] using accepted
  exact List.all_eq_true.mp all edge member

theorem accepted_up_edge {α : Type} {down up : α → Bool}
    {edges : List α} {edge : α} (member : edge ∈ edges)
    (accepted : (orderFlags down up (true, true) edges).2 = true) :
    up edge = true := by
  have all : edges.all up = true := by simpa [order_flags_exact] using accepted
  exact List.all_eq_true.mp all edge member

def sourceDown {n} (edge : Fin n × Fin n) : Bool :=
  decide (edge.1 = edge.2 ∨ edge.2.val < edge.1.val)

def sourceUp {n} (edge : Fin n × Fin n) : Bool :=
  decide (edge.1 = edge.2 ∨ edge.1.val < edge.2.val)

theorem down_classification_certifies_singletons {n}
    (edge : Fin n → Fin n → Bool) (captured : List (Fin n × Fin n))
    (complete : ∀ a b, edge a b = true → (a, b) ∈ captured)
    (accepted : (orderFlags sourceDown sourceUp (true, true) captured).1 = true) :
    ∀ a b, a = b ↔ (Reach edge a b ∧ Reach edge b a) := by
  apply decreasing_source_singletons edge
  intro a b direct different
  have found := accepted_down_edge (complete a b direct) accepted
  have ordered : a = b ∨ b.val < a.val := of_decide_eq_true found
  exact ordered.resolve_left different

theorem up_classification_certifies_singletons {n}
    (edge : Fin n → Fin n → Bool) (captured : List (Fin n × Fin n))
    (complete : ∀ a b, edge a b = true → (a, b) ∈ captured)
    (accepted : (orderFlags sourceDown sourceUp (true, true) captured).2 = true) :
    ∀ a b, a = b ↔ (Reach edge a b ∧ Reach edge b a) := by
  apply increasing_source_singletons edge
  intro a b direct different
  have found := accepted_up_edge (complete a b direct) accepted
  have ordered : a = b ∨ a.val < b.val := of_decide_eq_true found
  exact ordered.resolve_left different

end LeanPoo.Functional.ComponentWitness

namespace LeanPoo.Functional.ComponentWitness

-- Exact captured rows establish both soundness AND applicability completeness.
-- A conservative roster with extra edges still has the prior soundness law.
theorem down_classification_iff {n} (edge : Fin n → Fin n → Bool)
    (captured : List (Fin n × Fin n))
    (exactRows : ∀ a b, (a, b) ∈ captured ↔ edge a b = true) :
    (orderFlags sourceDown sourceUp (true, true) captured).1 = true ↔
      (∀ a b, edge a b = true → a ≠ b → b.val < a.val) := by
  constructor
  · intro accepted a b direct different
    have found := accepted_down_edge ((exactRows a b).mpr direct) accepted
    have ordered : a = b ∨ b.val < a.val := of_decide_eq_true found
    exact ordered.resolve_left different
  · intro decreasing
    have all : captured.all sourceDown = true := by
      apply List.all_eq_true.mpr
      rintro ⟨a, b⟩ member
      apply decide_eq_true
      by_cases same : a = b
      · exact Or.inl same
      · exact Or.inr (decreasing a b ((exactRows a b).mp member) same)
    simpa [order_flags_exact] using all

theorem up_classification_iff {n} (edge : Fin n → Fin n → Bool)
    (captured : List (Fin n × Fin n))
    (exactRows : ∀ a b, (a, b) ∈ captured ↔ edge a b = true) :
    (orderFlags sourceDown sourceUp (true, true) captured).2 = true ↔
      (∀ a b, edge a b = true → a ≠ b → a.val < b.val) := by
  constructor
  · intro accepted a b direct different
    have found := accepted_up_edge ((exactRows a b).mpr direct) accepted
    have ordered : a = b ∨ a.val < b.val := of_decide_eq_true found
    exact ordered.resolve_left different
  · intro increasing
    have all : captured.all sourceUp = true := by
      apply List.all_eq_true.mpr
      rintro ⟨a, b⟩ member
      apply decide_eq_true
      by_cases same : a = b
      · exact Or.inl same
      · exact Or.inr (increasing a b ((exactRows a b).mp member) same)
    simpa [order_flags_exact] using all

def orderChecks {α : Type} (down up : α → Bool) (state : Bool × Bool) : List α → Nat
  | [] => 0
  | edge :: rest =>
    if state.1 || state.2 then
      1 + orderChecks down up (state.1 && down edge, state.2 && up edge) rest
    else 0

theorem order_checks_bounded {α : Type} (down up : α → Bool)
    (state : Bool × Bool) (edges : List α) :
    orderChecks down up state edges ≤ edges.length := by
  induction edges generalizing state with
  | nil => simp [orderChecks]
  | cons edge rest ih =>
    simp only [orderChecks, List.length_cons]
    split
    · have bound := ih (state.1 && down edge, state.2 && up edge)
      omega
    · omega

theorem rejected_order_checks_zero {α : Type} (down up : α → Bool)
    (rest : List α) : orderChecks down up (false, false) rest = 0 := by
  cases rest <;> simp [orderChecks]

end LeanPoo.Functional.ComponentWitness
