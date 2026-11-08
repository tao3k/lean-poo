-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.KeyIndex
import LeanPoo.Functional.GeneralizedGraph
import LeanPoo.Functional.StrongComponents
import LeanPoo.Functional.HashRankLabels

/-! Local dependency-order certificates over the library's directed paths.
Edges point from consumer to provider; providers have smaller ranks. These
certificates do not authenticate a source, a value or a publication ticket. -/
namespace LeanPoo.Functional.DependencyOrderRepair
open LeanPoo.Functional.StrongComponents

abbrev Ranked {n : Nat} (edge : Fin n → Fin n → Bool) (rank : Fin n → Nat) :=
  ∀ consumer provider, edge consumer provider = true → rank provider < rank consumer

def inserted {n : Nat} (edge : Fin n → Fin n → Bool) (consumer provider : Fin n)
    (left right : Fin n) : Bool :=
  edge left right || (decide (left = consumer) && decide (right = provider))

def Cycle {n : Nat} (edge : Fin n → Fin n → Bool) : Prop :=
  ∃ consumer provider, edge consumer provider = true ∧ Reach edge provider consumer

theorem lift_path {n : Nat} {before after : Fin n → Fin n → Bool}
    (included : ∀ a b, before a b = true → after a b = true)
    {a b : Fin n} (path : Reach before a b) : Reach after a b := by
  induction path with
  | refl => exact .refl _
  | step direct _ ih => exact .step (included _ _ direct) ih

theorem reached_rank_le {n : Nat} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} (ordered : Ranked edge rank)
    {a b : Fin n} (path : Reach edge a b) : rank b ≤ rank a := by
  induction path with
  | refl => exact Nat.le_refl _
  | step direct _ ih => exact Nat.le_trans ih (Nat.le_of_lt (ordered _ _ direct))

theorem ranked_refuses_cycles {n : Nat} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} (ordered : Ranked edge rank) : ¬ Cycle edge := by
  rintro ⟨consumer, provider, direct, path⟩
  have down := ordered consumer provider direct
  have back := reached_rank_le ordered path
  omega

theorem insertion_with_lower_provider_keeps_rank {n : Nat}
    {edge : Fin n → Fin n → Bool} {rank : Fin n → Nat}
    (ordered : Ranked edge rank) (consumer provider : Fin n)
    (lower : rank provider < rank consumer) :
    Ranked (inserted edge consumer provider) rank := by
  intro a b direct
  simp only [inserted, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at direct
  rcases direct with old | ⟨rfl, rfl⟩
  · exact ordered a b old
  · exact lower

-- Even if a path uses the inserted edge repeatedly, retain its old prefix
-- before the first occurrence and its old suffix after the last occurrence.
theorem inserted_path_decomposition {n : Nat} (edge : Fin n → Fin n → Bool)
    (consumer provider : Fin n) {a b : Fin n}
    (path : Reach (inserted edge consumer provider) a b) :
    Reach edge a b ∨ (Reach edge a consumer ∧ Reach edge provider b) := by
  induction path with
  | refl => exact Or.inl (.refl _)
  | @step a next b direct _ ih =>
    simp only [inserted, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at direct
    rcases direct with old | ⟨sameA, sameNext⟩
    · rcases ih with oldTail | ⟨headPath, tailPath⟩
      · exact Or.inl (.step old oldTail)
      · exact Or.inr ⟨.step old headPath, tailPath⟩
    · subst a; subst next
      rcases ih with oldTail | ⟨_, tailPath⟩
      · exact Or.inr ⟨.refl _, oldTail⟩
      · exact Or.inr ⟨.refl _, tailPath⟩

theorem inserted_cycle_exact {n : Nat} (edge : Fin n → Fin n → Bool)
    (acyclic : ¬ Cycle edge) (consumer provider : Fin n) :
    Cycle (inserted edge consumer provider) ↔ Reach edge provider consumer := by
  constructor
  · rintro ⟨a, b, direct, path⟩
    have parts := inserted_path_decomposition edge consumer provider path
    simp only [inserted, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at direct
    rcases direct with old | ⟨rfl, rfl⟩
    · rcases parts with oldTail | ⟨headPath, tailPath⟩
      · exact False.elim (acyclic ⟨a, b, old, oldTail⟩)
      · exact tailPath.trans (.step old headPath)
    · rcases parts with prior | ⟨prior, _⟩ <;> exact prior
  · intro path
    refine ⟨consumer, provider, by simp [inserted], ?_⟩
    exact lift_path (fun a b direct => by simp [inserted, direct]) path

def intervalEdge {n : Nat} (edge : Fin n → Fin n → Bool) (rank : Fin n → Nat)
    (low high : Nat) (a b : Fin n) : Bool :=
  edge a b && decide (low ≤ rank a ∧ rank a ≤ high ∧ low ≤ rank b ∧ rank b ≤ high)

theorem bounded_path_stays_in_interval {n : Nat} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} (ordered : Ranked edge rank) (low high : Nat)
    {a b : Fin n} (path : Reach edge a b) :
    low ≤ rank b → rank a ≤ high → Reach (intervalEdge edge rank low high) a b := by
  induction path with
  | refl => intro _ _; exact .refl _
  | @step a next b direct rest ih =>
    intro lower upper
    have descends := ordered a next direct
    have suffix := reached_rank_le ordered rest
    have lowA : low ≤ rank a := by omega
    have lowNext : low ≤ rank next := by omega
    have highNext : rank next ≤ high := by omega
    exact .step (by simp [intervalEdge, direct, lowA, upper, lowNext, highNext])
      (ih lower highNext)

theorem interval_search_exact {n : Nat} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} (ordered : Ranked edge rank) (consumer provider : Fin n) :
    Reach (intervalEdge edge rank (rank consumer) (rank provider)) provider consumer ↔
      Reach edge provider consumer := by
  constructor
  · apply lift_path
    intro a b direct
    simp only [intervalEdge, Bool.and_eq_true] at direct
    exact direct.1
  · intro path
    exact bounded_path_stays_in_interval ordered _ _ path (Nat.le_refl _) (Nat.le_refl _)

-- A repair need check only actual edges incident to changed rank labels.
-- The exact old/new adjacency indices enumerate that union; they are not a
-- sampled subset of edges. All other edges retain both old endpoint ranks.
theorem local_rank_checks_suffice {n : Nat}
    (before after : Fin n → Fin n → Bool) (oldRank newRank : Fin n → Nat)
    (changed : Fin n → Prop) (oldOrder : Ranked before oldRank)
    (unchanged : ∀ node, ¬ changed node → newRank node = oldRank node)
    (newIncident : ∀ a b, after a b = true → before a b = true ∨ changed a ∨ changed b)
    (checked : ∀ a b, after a b = true → changed a ∨ changed b → newRank b < newRank a) :
    Ranked after newRank := by
  intro a b direct
  by_cases left : changed a
  · exact checked a b direct (Or.inl left)
  by_cases right : changed b
  · exact checked a b direct (Or.inr right)
  have old : before a b = true := by
    rcases newIncident a b direct with previous | modified | modified
    · exact previous
    · exact False.elim (left modified)
    · exact False.elim (right modified)
  rw [unchanged a left, unchanged b right]
  exact oldOrder a b old

-- Batches may also insert already ordered edges outside the relabelled set.
-- Check those explicit additions separately; neither endpoint need move.
theorem delta_rank_checks_suffice {n : Nat}
    (before after : Fin n → Fin n → Bool) (oldRank newRank : Fin n → Nat)
    (changed : Fin n → Prop) (oldOrder : Ranked before oldRank)
    (unchanged : ∀ node, ¬ changed node → newRank node = oldRank node)
    (kept : ∀ a b, before a b = true → after a b = true →
      changed a ∨ changed b → newRank b < newRank a)
    (added : ∀ a b, after a b = true → before a b ≠ true → newRank b < newRank a) :
    Ranked after newRank := by
  intro a b direct
  by_cases old : before a b = true
  · by_cases left : changed a
    · exact kept a b old direct (Or.inl left)
    by_cases right : changed b
    · exact kept a b old direct (Or.inr right)
    rw [unchanged a left, unchanged b right]
    exact oldOrder a b old
  · exact added a b direct old

-- Bind the local check to the actual library schedule, rather than a second
-- declaration identity. This proves only the rank condition, not construction,
-- membership/currentness or atomic publication of that condition.
open LeanPoo.Functional.GeneralizedGraph in
theorem library_local_rank_checks_suffice {n : Nat} {Value : Fin n → Type}
    {before after : Declaration (Fin n) Value} (prior : Scheduled before)
    (newRank : Fin n → Nat) (changed : Fin n → Prop)
    (unchanged : ∀ node, ¬ changed node → newRank node = prior.resolver.rank node)
    (newIncident : ∀ a b, b ∈ after.reads a → b ∈ before.reads a ∨ changed a ∨ changed b)
    (checked : ∀ a b, b ∈ after.reads a → changed a ∨ changed b → newRank b < newRank a) :
    ∀ a b, b ∈ after.reads a → newRank b < newRank a := by
  intro a b direct
  by_cases left : changed a
  · exact checked a b direct (Or.inl left)
  by_cases right : changed b
  · exact checked a b direct (Or.inr right)
  have old : b ∈ before.reads a := by
    rcases newIncident a b direct with previous | modified | modified
    · exact previous
    · exact False.elim (left modified)
    · exact False.elim (right modified)
  rw [unchanged a left, unchanged b right]
  exact prior.edgeLower a b old

theorem rank_violation_need_not_be_a_cycle :
    ¬ (1 : Nat) < 0 ∧
    ¬ Cycle (inserted (fun _ _ : Fin 2 => false) 0 1) := by
  have before : Ranked (fun _ _ : Fin 2 => false) (fun node => 1 - node.val) := by
    intro _ _ direct
    contradiction
  have after := insertion_with_lower_provider_keeps_rank before 0 1 (by decide)
  exact ⟨by decide, ranked_refuses_cycles after⟩

private def incoming (consumer provider : Fin 4) : Bool :=
  decide (consumer = 1 ∧ provider = 0)
private def wrongRank (node : Fin 4) : Nat :=
  if node = 0 then 3 else if node = 3 then 0 else node.val

-- A real permutation can satisfy every changed owner's outgoing check and
-- still break an untouched consumer. The reverse incident index is required.
theorem outgoing_checks_can_miss_a_rank_failure :
    Ranked incoming Fin.val ∧
    (∀ a b, incoming a b = true → (a = 0 ∨ a = 3) → wrongRank b < wrongRank a) ∧
    ¬ Ranked incoming wrongRank := by
  constructor
  · intro a b direct
    simp only [incoming, decide_eq_true_eq] at direct
    rcases direct with ⟨rfl, rfl⟩
    decide
  constructor
  · intro a b direct changed
    simp only [incoming, decide_eq_true_eq] at direct
    rcases direct with ⟨rfl, rfl⟩
    simp at changed
  · intro checked
    have impossible := checked 1 0 (by decide)
    change 3 < 1 at impossible
    omega

-- Candidate construction touches only supplied frontier keys and their old
-- labels. Distinctness and overlap refusal precede any rank patch. A rank
-- proposal still needs the exact incident-edge certificate above.
def proposeRanks (oldRank : Nat → Nat) (forward backward : List Nat) :
    Option (Std.HashMap Nat Nat) :=
  let owners := forward ++ backward
  let labels := owners.map oldRank
  if (Std.HashSet.ofList owners).size != owners.length ||
      (Std.HashSet.ofList labels).size != labels.length then none
  else
    let first := forward.mergeSort (fun a b => decide (oldRank a ≤ oldRank b))
    let last := backward.mergeSort (fun a b => decide (oldRank a ≤ oldRank b))
    let available := RankLabels.slots oldRank first last
    some (Std.HashMap.ofList ((first ++ last).zip available))

def applyRanks {keys : List Nat}
    (owners : LeanPoo.Functional.Requirements.KeyIndex keys)
    (patch : Std.HashMap Nat Nat) (oldRank : Nat → Nat) (node : Nat) : Nat :=
  if owners.contains node then patch.getD node (oldRank node) else oldRank node

theorem unlisted_rank_is_preserved {keys : List Nat}
    (owners : LeanPoo.Functional.Requirements.KeyIndex keys)
    (patch : Std.HashMap Nat Nat) (oldRank : Nat → Nat) (node : Nat)
    (outside : node ∉ keys) : applyRanks owners patch oldRank node = oldRank node := by
  simp [applyRanks, LeanPoo.Functional.Requirements.KeyIndex.contains_iff, outside]


end LeanPoo.Functional.DependencyOrderRepair
