-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.LocalSccRegion

namespace LeanPoo.Functional.OrderedSccRepair
open LeanPoo.Functional.StrongComponents
open LeanPoo.Functional.LocalSccRegion (Edge Same)

def RankLe {n : Nat} (ascending : Bool) (rank : Fin n → Nat) (a b : Fin n) : Prop :=
  if ascending then rank a ≤ rank b else rank b ≤ rank a

def Ordered {n : Nat} (edge : Edge n) (rank : Fin n → Nat) (ascending : Bool) : Prop :=
  ∀ a b, edge a b = true → RankLe ascending rank a b

theorem path_rank {n : Nat} {edge : Edge n} {rank : Fin n → Nat} {ascending : Bool}
    (ordered : Ordered edge rank ascending) {a b : Fin n} (path : Reach edge a b) :
    RankLe ascending rank a b := by
  cases ascending with
  | false =>
    induction path with
    | refl a => exact Nat.le_refl _
    | step direct _ ih => exact Nat.le_trans ih (ordered _ _ direct)
  | true =>
    induction path with
    | refl a => exact Nat.le_refl _
    | step direct _ ih => exact Nat.le_trans (ordered _ _ direct) ih

theorem same_iff_eq {n : Nat} {edge : Edge n} {rank : Fin n → Nat} {ascending : Bool}
    (ordered : Ordered edge rank ascending) (unique : Function.Injective rank) (a b : Fin n) :
    Same edge a b ↔ a = b := by
  constructor
  · rintro ⟨forward, backward⟩
    apply unique
    have to := path_rank ordered forward
    have backRank := path_rank ordered backward
    cases ascending with
    | false => exact Nat.le_antisymm backRank to
    | true => exact Nat.le_antisymm to backRank
  · intro equal
    subst b
    exact ⟨.refl a, .refl a⟩

/-- Only authored replacement rows need a new rank check. The unchanged-row
    premise comes from an authenticated delta, never from edit counts. -/
theorem ordered_after_edit {n : Nat} {old next : Edge n} {rank : Fin n → Nat}
    {changed : Fin n → Prop} {ascending : Bool} (prior : Ordered old rank ascending)
    (sameRows : ∀ a, ¬ changed a → ∀ b, old a b = next a b)
    (replacement : ∀ a, changed a → ∀ b, next a b = true → RankLe ascending rank a b) :
    Ordered next rank ascending := by
  classical
  intro a b edge
  by_cases edited : changed a
  · exact replacement a edited b edge
  · exact prior a b ((sameRows a edited b).trans edge)

theorem delete_only {n : Nat} {old next : Edge n} {rank : Fin n → Nat}
    {ascending : Bool} (prior : Ordered old rank ascending)
    (subset : ∀ a b, next a b = true → old a b = true) :
    Ordered next rank ascending := fun a b edge => prior a b (subset a b edge)

/-- Reusing old singleton owner/member indices equals cold SCC membership. -/
theorem cold_incremental_same {n : Nat} {old next : Edge n} {rank : Fin n → Nat}
    {changed : Fin n → Prop} {ascending : Bool}
    (prior : Ordered old rank ascending) (unique : Function.Injective rank)
    (sameRows : ∀ a, ¬ changed a → ∀ b, old a b = next a b)
    (replacement : ∀ a, changed a → ∀ b, next a b = true → RankLe ascending rank a b)
    (a b : Fin n) : Same old a b ↔ Same next a b := by
  exact (same_iff_eq prior unique a b).trans
    (same_iff_eq (ordered_after_edit prior sameRows replacement) unique a b).symm

theorem representative_is_self {n : Nat} {edge : Edge n} {rank : Fin n → Nat}
    {ascending : Bool} (ordered : Ordered edge rank ascending) (unique : Function.Injective rank)
    (owner : Fin n → Fin n) (member : ∀ a, Same edge a (owner a)) (a : Fin n) :
    owner a = a := ((same_iff_eq ordered unique a (owner a)).mp (member a)).symm

-- Singleton SCCs alone are NOT an order certificate: a new back edge can merge.
def twoCycle : Edge 2 := fun a b => decide (a ≠ b)
example : ¬ Ordered twoCycle (fun a => a.val) false := by
  intro ordered
  have impossible := ordered ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
  exact Nat.not_succ_le_zero 0 impossible

-- Self edges do not create a non-singleton component and keep either bit.
example (ascending : Bool) : Ordered (fun _ _ : Fin 1 => true) (fun a => a.val) ascending := by
  intro a b _
  have equal : a = b := Subsingleton.elim a b
  subst b
  cases ascending <;> exact Nat.le_refl _

end LeanPoo.Functional.OrderedSccRepair
