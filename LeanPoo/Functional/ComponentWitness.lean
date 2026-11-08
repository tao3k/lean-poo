-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.DependencyOrderRepair

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

end LeanPoo.Functional.ComponentWitness
