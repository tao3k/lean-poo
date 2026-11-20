-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.DependencyOrderRepair
import Init.Data.List.Sort.Lemmas
import Init.Data.List.Zip
import LeanPoo.Functional.HashRankLabels

/-! The semantic contract of a sparse stable partition. Graph completeness is
separate from the refinement of the concrete sort/zip/HashMap implementation.
Neither theorem authorizes reuse of source or publication evidence. -/
namespace LeanPoo.Functional.DependencyOrderRepair
open LeanPoo.Functional.StrongComponents

def Forward {n} (edge : Fin n → Fin n → Bool) (rank : Fin n → Nat)
    (consumer provider node : Fin n) : Prop :=
  Reach edge provider node ∧ rank consumer ≤ rank node

def Backward {n} (edge : Fin n → Fin n → Bool) (rank : Fin n → Nat)
    (consumer provider node : Fin n) : Prop :=
  Reach edge node consumer ∧ rank node ≤ rank provider

theorem interval_reach_end_bounds {n} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} {low high : Nat} {a b : Fin n}
    (path : Reach (intervalEdge edge rank low high) a b) :
    low ≤ rank a ∧ rank a ≤ high → low ≤ rank b ∧ rank b ≤ high := by
  induction path with
  | refl => exact id
  | step direct _ ih =>
    intro _
    simp only [intervalEdge, Bool.and_eq_true, decide_eq_true_eq] at direct
    exact ih ⟨direct.2.2.2.1, direct.2.2.2.2⟩

theorem interval_reach_start_bounds {n} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} {low high : Nat} {a b : Fin n}
    (path : Reach (intervalEdge edge rank low high) a b)
    (last : low ≤ rank b ∧ rank b ≤ high) : low ≤ rank a ∧ rank a ≤ high := by
  cases path with
  | refl => exact last
  | step direct _ =>
    simp only [intervalEdge, Bool.and_eq_true, decide_eq_true_eq] at direct
    exact ⟨direct.2.1, direct.2.2.1⟩

theorem forward_interval_exact {n} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} {consumer provider node : Fin n}
    (ordered : Ranked edge rank) (inverted : rank consumer ≤ rank provider) :
    Forward edge rank consumer provider node ↔
      Reach (intervalEdge edge rank (rank consumer) (rank provider)) provider node := by
  constructor
  · rintro ⟨path, lower⟩
    exact bounded_path_stays_in_interval ordered _ _ path lower (Nat.le_refl _)
  · intro path
    exact ⟨lift_path (fun _ _ h => by simp only [intervalEdge, Bool.and_eq_true] at h; exact h.1) path,
      (interval_reach_end_bounds path ⟨inverted, Nat.le_refl _⟩).1⟩

theorem backward_interval_exact {n} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} {consumer provider node : Fin n}
    (ordered : Ranked edge rank) (inverted : rank consumer ≤ rank provider) :
    Backward edge rank consumer provider node ↔
      Reach (intervalEdge edge rank (rank consumer) (rank provider)) node consumer := by
  constructor
  · rintro ⟨path, upper⟩
    exact bounded_path_stays_in_interval ordered _ _ path (Nat.le_refl _) upper
  · intro path
    exact ⟨lift_path (fun _ _ h => by simp only [intervalEdge, Bool.and_eq_true] at h; exact h.1) path,
      (interval_reach_start_bounds path ⟨Nat.le_refl _, inverted⟩).2⟩

theorem frontiers_disjoint {n} {edge : Fin n → Fin n → Bool}
    {rank : Fin n → Nat} {consumer provider : Fin n}
    (noCycle : ¬ Reach edge provider consumer) :
    ∀ node, ¬ (Forward edge rank consumer provider node ∧
      Backward edge rank consumer provider node) := by
  rintro node ⟨⟨pf, _⟩, ⟨bc, _⟩⟩
  exact noCycle (pf.trans bc)

-- These are properties of the stable partition of the affected rank labels,
-- not a restatement of the desired per-edge result.
structure StableRelabel {n} (edge : Fin n → Fin n → Bool)
    (old next : Fin n → Nat) (consumer provider : Fin n) : Prop where
  outside : ∀ x, ¬ Forward edge old consumer provider x →
    ¬ Backward edge old consumer provider x → next x = old x
  forwardMoves : ∀ x, Forward edge old consumer provider x → next x ≤ old x
  backwardMoves : ∀ x, Backward edge old consumer provider x → old x ≤ next x
  bounds : ∀ x, Forward edge old consumer provider x ∨
    Backward edge old consumer provider x → old consumer ≤ next x ∧ next x ≤ old provider
  forwardOrder : ∀ x y, Forward edge old consumer provider x →
    Forward edge old consumer provider y → old x < old y → next x < next y
  backwardOrder : ∀ x y, Backward edge old consumer provider x →
    Backward edge old consumer provider y → old x < old y → next x < next y
  separated : ∀ f b, Forward edge old consumer provider f →
    Backward edge old consumer provider b → next f < next b

-- Completeness covers incoming edges of unchanged consumers too. There is no
-- assumption that an edge is inside the rank interval or in the changed set.
theorem stable_relabel_complete {n} {edge : Fin n → Fin n → Bool}
    {old next : Fin n → Nat} {consumer provider : Fin n}
    (ordered : Ranked edge old) (inverted : old consumer ≤ old provider)
    (layout : StableRelabel edge old next consumer provider) :
    Ranked (inserted edge consumer provider) next := by
  have cB : Backward edge old consumer provider consumer := ⟨.refl _, inverted⟩
  have pF : Forward edge old consumer provider provider := ⟨.refl _, inverted⟩
  apply insertion_with_lower_provider_keeps_rank _ consumer provider (layout.separated _ _ pF cB)
  intro a b direct
  have down := ordered a b direct
  by_cases aF : Forward edge old consumer provider a
  · by_cases bF : Forward edge old consumer provider b
    · exact layout.forwardOrder b a bF aF down
    · have lower : old b < old consumer := by
        by_cases h : old consumer ≤ old b
        · exact False.elim (bF ⟨aF.1.trans (.step direct (.refl _)), h⟩)
        · omega
      have notB : ¬ Backward edge old consumer provider b := by
        intro bB
        have := reached_rank_le ordered bB.1
        omega
      rw [layout.outside b bF notB]
      have := (layout.bounds a (Or.inl aF)).1
      omega
  · by_cases bB : Backward edge old consumer provider b
    · by_cases aB : Backward edge old consumer provider a
      · exact layout.backwardOrder b a bB aB down
      · have upper : old provider < old a := by
          by_cases h : old a ≤ old provider
          · exact False.elim (aB ⟨.step direct bB.1, h⟩)
          · omega
        rw [layout.outside a aF aB]
        have := (layout.bounds b (Or.inr bB)).2
        omega
    · by_cases aB : Backward edge old consumer provider a
      · by_cases bF : Forward edge old consumer provider b
        · exact layout.separated b a bF aB
        · rw [layout.outside b bF bB]
          have := layout.backwardMoves a aB
          omega
      · rw [layout.outside a aF aB]
        by_cases bF : Forward edge old consumer provider b
        · have := layout.forwardMoves b bF
          omega
        · rw [layout.outside b bF bB]
          exact down

-- The executable proposal pairs these exact lists. Both projections are full
-- permutations: zip cannot silently discard an owner or a rank label.
def rankRows (old : Nat → Nat) (forward backward : List Nat) : List (Nat × Nat) :=
  let cmp := fun a b => decide (old a ≤ old b)
  ((forward.mergeSort cmp) ++ (backward.mergeSort cmp)).zip
    (((forward ++ backward).map old).mergeSort (fun a b => decide (a ≤ b)))

theorem rankRows_owners (old : Nat → Nat) (forward backward : List Nat) :
    ((rankRows old forward backward).map Prod.fst).Perm (forward ++ backward) := by
  unfold rankRows
  rw [List.map_fst_zip (by simp)]
  exact (List.mergeSort_perm _ _).append (List.mergeSort_perm _ _)

theorem rankRows_labels (old : Nat → Nat) (forward backward : List Nat) :
    ((rankRows old forward backward).map Prod.snd).Perm ((forward ++ backward).map old) := by
  unfold rankRows
  rw [List.map_snd_zip (by simp)]
  exact List.mergeSort_perm _ _

theorem rankRows_distinct (old : Nat → Nat) (forward backward : List Nat)
    (owners : (forward ++ backward).Nodup)
    (labels : ((forward ++ backward).map old).Nodup) :
    ((rankRows old forward backward).map Prod.fst).Nodup ∧
    ((rankRows old forward backward).map Prod.snd).Nodup := by
  exact ⟨(rankRows_owners old forward backward).nodup_iff.mpr owners,
    (rankRows_labels old forward backward).nodup_iff.mpr labels⟩

theorem stable_assignment_complete {n} {edge : Fin n → Fin n → Bool}
    {old : Fin n → Nat} {consumer provider : Fin n}
    (ordered : Ranked edge old) (inverted : old consumer ≤ old provider)
    (first last : List (Fin n))
    (firstExact : ∀ x, x ∈ first ↔ Forward edge old consumer provider x)
    (lastExact : ∀ x, x ∈ last ↔ Backward edge old consumer provider x)
    (firstSorted : first.Pairwise (fun a b => old a ≤ old b))
    (lastSorted : last.Pairwise (fun a b => old a ≤ old b))
    (owners : (first ++ last).Nodup) (labels : ((first ++ last).map old).Nodup) :
    Ranked (inserted edge consumer provider) (RankLabels.assign old first last) := by
  have assigned := RankLabels.assign_slots old first last owners
  apply stable_relabel_complete ordered inverted
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x nf nb
    exact RankLabels.assign_outside old first last x (by
      simp only [List.mem_append]; rintro (f | b)
      · exact nf ((firstExact x).mp f)
      · exact nb ((lastExact x).mp b))
  · intro x f
    exact RankLabels.first_moves_left firstSorted assigned ((firstExact x).mpr f)
  · intro x b
    exact RankLabels.last_moves_right lastSorted assigned ((lastExact x).mpr b)
  · intro x mem
    have mx : x ∈ first ++ last := by
      rcases mem with f | b
      · exact List.mem_append_left _ ((firstExact x).mpr f)
      · exact List.mem_append_right _ ((lastExact x).mpr b)
    have mv : RankLabels.assign old first last x ∈ RankLabels.slots old first last := by
      rw [← assigned]; exact List.mem_map_of_mem mx
    obtain ⟨y, my, eq⟩ := List.mem_map.mp ((RankLabels.slots_perm old first last).mem_iff.mp mv)
    have bounds : old consumer ≤ old y ∧ old y ≤ old provider := by
      rcases List.mem_append.mp my with f | b
      · have fy := (firstExact y).mp f
        exact ⟨fy.2, reached_rank_le ordered fy.1⟩
      · have back := (lastExact y).mp b
        exact ⟨reached_rank_le ordered back.1, back.2⟩
    simpa only [eq] using bounds
  · intro x y fx fy less
    exact RankLabels.first_order firstSorted labels assigned
      ((firstExact x).mpr fx) ((firstExact y).mpr fy) less
  · intro x y bx byy less
    exact RankLabels.last_order lastSorted labels assigned
      ((lastExact x).mpr bx) ((lastExact y).mpr byy) less
  · intro f b hf hb
    exact RankLabels.separated labels assigned ((firstExact f).mpr hf) ((lastExact b).mpr hb)

def repairRanks {α} [BEq α] [Hashable α] (old : α → Nat) (forward backward : List α) : α → Nat :=
  let cmp := fun a b => decide (old a ≤ old b)
  RankLabels.assign old (forward.mergeSort cmp) (backward.mergeSort cmp)

theorem repair_ranks_injective {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (forward backward : List α)
    (unique : Function.Injective old) (distinct : (forward ++ backward).Nodup) :
    Function.Injective (repairRanks old forward backward) := by
  apply RankLabels.assign_injective
  · exact ((List.mergeSort_perm forward _).append (List.mergeSort_perm backward _)).nodup_iff.mpr distinct
  · exact unique

-- All deletions precede additions in Scheme. Thus each insertion prefix is a
-- subgraph of the final graph, rather than an artificial intermediate cycle.
theorem acyclic_final_accepts_every_prefix {n}
    {current final : Fin n → Fin n → Bool} {consumer provider : Fin n}
    (included : ∀ a b, current a b = true → final a b = true)
    (addition : final consumer provider = true) (acyclic : ¬ Cycle final) :
    ¬ Reach current provider consumer := by
  intro path
  exact acyclic ⟨consumer, provider, addition, lift_path included path⟩

-- No incident-edge checker premise: exact finite frontiers, an injective old
-- order and refusal of the exact cycle condition suffice for construction.
theorem sparse_repair_complete {n} {edge : Fin n → Fin n → Bool}
    {old : Fin n → Nat} {consumer provider : Fin n}
    (ordered : Ranked edge old) (unique : Function.Injective old)
    (inverted : old consumer ≤ old provider)
    (noCycle : ¬ Reach edge provider consumer)
    (forward backward : List (Fin n)) (fn : forward.Nodup) (bn : backward.Nodup)
    (fe : ∀ x, x ∈ forward ↔ Forward edge old consumer provider x)
    (be : ∀ x, x ∈ backward ↔ Backward edge old consumer provider x) :
    Ranked (inserted edge consumer provider) (repairRanks old forward backward) ∧
    ((forward ++ backward).map (repairRanks old forward backward)).Perm
      ((forward ++ backward).map old) ∧
    (∀ x, x ∉ forward ++ backward → repairRanks old forward backward x = old x) := by
  let cmp := fun a b => decide (old a ≤ old b)
  let first := forward.mergeSort cmp
  let last := backward.mergeSort cmp
  have fp : first.Perm forward := List.mergeSort_perm _ _
  have bp : last.Perm backward := List.mergeSort_perm _ _
  have ep := fp.append bp
  have owners : (first ++ last).Nodup := by
    apply ep.nodup_iff.mpr
    apply List.nodup_append.mpr
    refine ⟨fn, bn, ?_⟩
    intro x hx y hy eq
    subst y
    exact frontiers_disjoint noCycle x ⟨(fe x).mp hx, (be x).mp hy⟩
  have labels : ((first ++ last).map old).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact owners.imp (fun ne eq => ne (unique eq))
  have sortProof : ∀ xs : List (Fin n), (xs.mergeSort cmp).Pairwise (fun a b => old a ≤ old b) := by
    intro xs
    have sorted := List.pairwise_mergeSort (le := cmp)
      (fun a b c hab hbc => by simp only [cmp, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]; omega) xs
    simpa only [cmp, decide_eq_true_eq] using sorted
  refine ⟨stable_assignment_complete ordered inverted first last
    (fun x => fp.mem_iff.trans (fe x)) (fun x => bp.mem_iff.trans (be x))
    (sortProof forward) (sortProof backward) owners labels, ?_, ?_⟩
  · exact ((ep.map _).symm.trans (RankLabels.assign_labels_permutation old first last owners)).trans (ep.map old)
  · intro x outside
    exact RankLabels.assign_outside old first last x (fun mem => outside (ep.mem_iff.mp mem))

end LeanPoo.Functional.DependencyOrderRepair
