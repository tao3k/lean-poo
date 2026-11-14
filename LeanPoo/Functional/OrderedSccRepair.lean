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

/-- Inside one old component, a path can discard self edges. Every other
    edge on it has endpoints in that component and must survive the edit. -/
theorem internal_path_preserved {n : Nat} {old next : Edge n}
    (keep : ∀ a b, old a b = true → a ≠ b → Same old a b → next a b = true)
    {a b : Fin n} (path : Reach old a b) : Reach old b a → Reach next a b := by
  induction path with
  | refl a => intro _; exact .refl a
  | @step a middle b direct tail ih =>
    intro back
    have first : Reach old a middle := .step direct (.refl middle)
    have rest := ih (back.trans first)
    by_cases equal : a = middle
    · subst middle; exact rest
    · exact .step (keep a middle direct equal ⟨first, tail.trans back⟩) rest

theorem added_internal_path {n : Nat} {old next : Edge n}
    (added : ∀ a b, next a b = true → old a b = true ∨ Same old a b)
    {a b : Fin n} (path : Reach next a b) : Reach old a b := by
  induction path with
  | refl a => exact .refl a
  | @step a middle b direct _ ih =>
    rcases added a middle direct with prior | internal
    · exact .step prior ih
    · exact internal.1.trans ih

/-- Insertions internal to old SCCs and deletions only between old SCCs
    (or self edges) preserve exact SCC membership in both directions. -/
theorem component_stable_edit {n : Nat} {old next : Edge n}
    (keep : ∀ a b, old a b = true → a ≠ b → Same old a b → next a b = true)
    (added : ∀ a b, next a b = true → old a b = true ∨ Same old a b)
    (a b : Fin n) : Same old a b ↔ Same next a b := by
  constructor
  · rintro ⟨forward, backward⟩
    exact ⟨internal_path_preserved keep forward backward,
      internal_path_preserved keep backward forward⟩
  · rintro ⟨forward, backward⟩
    exact ⟨added_internal_path added forward, added_internal_path added backward⟩

/-- The native classifier inspects only effective additions/removals against
    the predecessor's already certified owner index. Row capture/authentication
    and complete delta coverage remain independent premises. -/
theorem owner_classified_edit {n : Nat} {old next : Edge n} (owner : Fin n → Fin n)
    (exactOwner : ∀ a b, Same old a b ↔ owner a = owner b)
    (inserted : ∀ a b, next a b = true → old a b ≠ true → owner a = owner b)
    (removed : ∀ a b, old a b = true → next a b ≠ true → a = b ∨ owner a ≠ owner b)
    (a b : Fin n) : Same next a b ↔ owner a = owner b := by
  have keep : ∀ a b, old a b = true → a ≠ b → Same old a b → next a b = true := by
    intro x y direct distinct same
    apply Classical.byContradiction
    intro missing
    rcases removed x y direct missing with equal | separated
    · exact distinct equal
    · exact separated ((exactOwner x y).mp same)
  have added : ∀ a b, next a b = true → old a b = true ∨ Same old a b := by
    intro x y direct
    by_cases prior : old x y = true
    · exact Or.inl prior
    · exact Or.inr ((exactOwner x y).mpr (inserted x y direct prior))
  exact (component_stable_edit keep added a b).symm.trans (exactOwner a b)

-- A retained SCC partition does NOT retain the functional-cycle certificate.
private def cycle3 : Edge 3 := fun a b => decide ((a.val + 1) % 3 = b.val)
private def chord3 : Edge 3 := fun a b => cycle3 a b || decide (a.val = 0 ∧ b.val = 2)
private def SingleSuccessor {n : Nat} (edge : Edge n) : Prop :=
  ∀ a b c, edge a b = true → edge a c = true → b = c
example : SingleSuccessor cycle3 := by unfold SingleSuccessor cycle3; decide
example : ¬ SingleSuccessor chord3 := by unfold SingleSuccessor chord3 cycle3; decide

end LeanPoo.Functional.OrderedSccRepair
