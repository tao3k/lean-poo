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

end LeanPoo.Functional.ComponentWitness
