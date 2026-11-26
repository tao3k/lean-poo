-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Init.Data.List.Sort.Lemmas
import Init.Data.List.Zip

/-! Ordered rank slots. No graph, source effects or remembered authentication. -/
namespace LeanPoo.Functional.RankLabels

theorem sublist_prefix_bound {α} {R : α → α → Prop}
    (refl : ∀ a, R a a) (trans : ∀ a b c, R a b → R b c → R a c)
    {xs ys : List α} (sub : xs.Sublist ys) (sorted : ys.Pairwise R) :
    ∀ i (hi : i < xs.length), R (ys[i]'(Nat.lt_of_lt_of_le hi sub.length_le)) xs[i] := by
  induction sub with
  | slnil => simp
  | @cons xs ys y sub ih =>
    intro i hi
    have len := sub.length_le
    have tail := List.pairwise_cons.mp sorted
    have prev := ih tail.2 i hi
    cases i with
    | zero =>
      exact trans _ _ _ (tail.1 _ (List.getElem_mem _)) prev
    | succ i =>
      exact trans _ _ _ (tail.2.rel_getElem_of_lt (by omega) (by omega) (by omega)) prev
  | @cons_cons xs ys x sub ih =>
    intro i hi
    cases i with
    | zero => exact refl _
    | succ i => exact ih (List.pairwise_cons.mp sorted).2 i (by simpa using hi)

theorem sublist_suffix_bound {α} {R : α → α → Prop}
    (refl : ∀ a, R a a) (trans : ∀ a b c, R a b → R b c → R a c)
    {xs ys : List α} (sub : xs.Sublist ys) (sorted : ys.Pairwise R) :
    ∀ i (hi : i < xs.length),
      R xs[i] (ys[ys.length - xs.length + i]'(by have := sub.length_le; omega)) := by
  intro i hi
  have rev := sub.reverse
  have revSort : ys.reverse.Pairwise (fun a b => R b a) := by
    simpa only [List.pairwise_reverse] using sorted
  have h := sublist_prefix_bound (R := fun a b => R b a) refl
    (fun a b c hab hbc => trans c b a hbc hab)
    rev revSort (xs.length - 1 - i) (by simp; omega)
  simp only [List.getElem_reverse] at h
  have len := sub.length_le
  have hx : xs.length - 1 - (xs.length - 1 - i) = i := by omega
  have hy : ys.length - 1 - (xs.length - 1 - i) = ys.length - xs.length + i := by omega
  simpa only [hx, hy] using h

theorem strictly_sorted {xs : List Nat} (sorted : xs.Pairwise (· ≤ ·))
    (distinct : xs.Nodup) : xs.Pairwise (· < ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj ij
  have le := sorted.rel_getElem_of_lt hi hj ij
  have ne : xs[i] ≠ xs[j] := by
    intro same
    have := distinct.eq_of_getElem_eq hi hj same
    omega
  omega

def slots {α} (old : α → Nat) (first last : List α) : List Nat :=
  ((first ++ last).map old).mergeSort (fun a b => decide (a ≤ b))

theorem slots_sorted {α} (old : α → Nat) (first last : List α) :
    (slots old first last).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((first ++ last).map old)
  simpa only [slots, decide_eq_true_eq] using h

theorem slots_length {α} (old : α → Nat) (first last : List α) :
    (slots old first last).length = first.length + last.length := by simp [slots]

theorem slots_perm {α} (old : α → Nat) (first last : List α) :
    (slots old first last).Perm ((first ++ last).map old) := List.mergeSort_perm _ _

theorem first_sublist_slots {α} {old : α → Nat} {first last : List α}
    (sorted : first.Pairwise (fun a b => old a ≤ old b)) :
    (first.map old).Sublist (slots old first last) := by
  apply List.sublist_mergeSort
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
  · exact (sorted.map old (fun _ _ h => h)).imp (fun h => by simpa using h)
  · simpa only [List.map_append] using List.sublist_append_left (first.map old) (last.map old)

theorem last_sublist_slots {α} {old : α → Nat} {first last : List α}
    (sorted : last.Pairwise (fun a b => old a ≤ old b)) :
    (last.map old).Sublist (slots old first last) := by
  apply List.sublist_mergeSort
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
  · exact (sorted.map old (fun _ _ h => h)).imp (fun h => by simpa using h)
  · simpa only [List.map_append] using List.sublist_append_right (first.map old) (last.map old)

theorem assigned_first {α} {next : α → Nat} {first last : List α} {values : List Nat}
    (assigned : (first ++ last).map next = values) (i : Nat) (hi : i < first.length) :
    next first[i] = values[i]'(by rw [← assigned]; simp; omega) := by
  subst values
  simp only [List.getElem_map, List.getElem_append_left hi]

theorem assigned_last {α} {next : α → Nat} {first last : List α} {values : List Nat}
    (assigned : (first ++ last).map next = values) (i : Nat) (hi : i < last.length) :
    next last[i] = values[first.length + i]'(by rw [← assigned]; simp; omega) := by
  subst values
  simp only [List.getElem_map, List.getElem_append_right (show first.length ≤ first.length + i by omega),
    Nat.add_sub_cancel_left]

theorem first_moves_left {α} {old next : α → Nat} {first last : List α}
    (sorted : first.Pairwise (fun a b => old a ≤ old b))
    (assigned : (first ++ last).map next = slots old first last)
    {x : α} (mem : x ∈ first) : next x ≤ old x := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mem
  have h := sublist_prefix_bound Nat.le_refl (fun _ _ _ => Nat.le_trans)
    (first_sublist_slots sorted) (slots_sorted old first last) i (by simpa using hi)
  simpa only [List.getElem_map, ← assigned_first assigned i hi, hx] using h

theorem last_moves_right {α} {old next : α → Nat} {first last : List α}
    (sorted : last.Pairwise (fun a b => old a ≤ old b))
    (assigned : (first ++ last).map next = slots old first last)
    {x : α} (mem : x ∈ last) : old x ≤ next x := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mem
  have h := sublist_suffix_bound Nat.le_refl (fun _ _ _ => Nat.le_trans)
    (last_sublist_slots sorted) (slots_sorted old first last) i (by simpa using hi)
  have len : (slots old first last).length - (last.map old).length + i = first.length + i := by
    simp [slots_length]
  simpa only [List.getElem_map, len, ← assigned_last assigned i hi, hx] using h

theorem index_of_lt {α} {old : α → Nat} {xs : List α}
    (sorted : xs.Pairwise (fun a b => old a ≤ old b))
    {i j} (hi : i < xs.length) (hj : j < xs.length) (less : old xs[i] < old xs[j]) : i < j := by
  by_cases h : i < j
  · exact h
  by_cases eq : i = j
  · subst j; omega
  have := sorted.rel_getElem_of_lt hj hi (by omega)
  omega

theorem first_order {α} {old next : α → Nat} {first last : List α}
    (sorted : first.Pairwise (fun a b => old a ≤ old b))
    (distinct : ((first ++ last).map old).Nodup)
    (assigned : (first ++ last).map next = slots old first last)
    {x y : α} (mx : x ∈ first) (my : y ∈ first) (less : old x < old y) : next x < next y := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mx
  obtain ⟨j, hj, hy⟩ := List.getElem_of_mem my
  have ij := index_of_lt sorted hi hj (by simpa only [hx, hy] using less)
  have ss := strictly_sorted (slots_sorted old first last) ((slots_perm old first last).nodup_iff.mpr distinct)
  have h := ss.rel_getElem_of_lt (by rw [slots_length]; omega) (by rw [slots_length]; omega) ij
  simpa only [← assigned_first assigned i hi, ← assigned_first assigned j hj, hx, hy] using h

theorem last_order {α} {old next : α → Nat} {first last : List α}
    (sorted : last.Pairwise (fun a b => old a ≤ old b))
    (distinct : ((first ++ last).map old).Nodup)
    (assigned : (first ++ last).map next = slots old first last)
    {x y : α} (mx : x ∈ last) (my : y ∈ last) (less : old x < old y) : next x < next y := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mx
  obtain ⟨j, hj, hy⟩ := List.getElem_of_mem my
  have ij := index_of_lt sorted hi hj (by simpa only [hx, hy] using less)
  have ss := strictly_sorted (slots_sorted old first last) ((slots_perm old first last).nodup_iff.mpr distinct)
  have h := ss.rel_getElem_of_lt
    (i := first.length + i) (j := first.length + j)
    (by rw [slots_length]; omega) (by rw [slots_length]; omega) (by omega)
  simpa only [← assigned_last assigned i hi, ← assigned_last assigned j hj, hx, hy] using h

theorem separated {α} {old next : α → Nat} {first last : List α}
    (distinct : ((first ++ last).map old).Nodup)
    (assigned : (first ++ last).map next = slots old first last)
    {x y : α} (mx : x ∈ first) (my : y ∈ last) : next x < next y := by
  obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mx
  obtain ⟨j, hj, hy⟩ := List.getElem_of_mem my
  have ss := strictly_sorted (slots_sorted old first last) ((slots_perm old first last).nodup_iff.mpr distinct)
  have h := ss.rel_getElem_of_lt (i := i) (j := first.length + j)
    (by rw [slots_length]; omega) (by rw [slots_length]; omega) (by omega)
  simpa only [← assigned_first assigned i hi, ← assigned_last assigned j hj, hx, hy] using h

end LeanPoo.Functional.RankLabels
