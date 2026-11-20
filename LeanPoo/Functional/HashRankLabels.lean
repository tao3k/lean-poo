-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.RankLabels
import Std.Data.HashMap.Lemmas

namespace LeanPoo.Functional.RankLabels

def assign {α} [BEq α] [Hashable α] (old : α → Nat) (first last : List α) (x : α) : Nat :=
  (Std.HashMap.ofList ((first ++ last).zip (slots old first last))).getD x (old x)

theorem assign_slots {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (first last : List α) (distinct : (first ++ last).Nodup) :
    (first ++ last).map (assign old first last) = slots old first last := by
  let keys := first ++ last
  let values := slots old first last
  have len : keys.length = values.length := by simp [keys, values, slots_length]
  have fst : ((keys.zip values).map Prod.fst) = keys := List.map_fst_zip (by omega)
  have unique : (keys.zip values).Pairwise (fun a b => (a.1 == b.1) = false) := by
    have h : ((keys.zip values).map Prod.fst).Nodup := by rw [fst]; exact distinct
    simpa only [List.nodup_iff_pairwise_ne, List.pairwise_map, beq_eq_false_iff_ne] using h
  apply List.ext_getElem (by simp [slots_length])
  intro i hi hj
  have hk : i < keys.length := by simpa [keys] using hi
  have hv : i < values.length := by simpa [values] using hj
  have mem : (keys[i], values[i]) ∈ keys.zip values :=
    List.mem_of_getElem? (i := i) (List.getElem?_zip_eq_some.mpr ⟨by simp, by simp⟩)
  simpa only [List.getElem_map, assign, keys, values] using
    (Std.HashMap.getD_ofList_of_mem (by simp : (keys[i] == keys[i]) = true) unique mem
      (fallback := old keys[i]))

theorem assign_outside {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (first last : List α) (x : α) (outside : x ∉ first ++ last) :
    assign old first last x = old x := by
  unfold assign
  apply Std.HashMap.getD_ofList_of_contains_eq_false
  rw [List.map_fst_zip (by simp [slots_length])]
  simpa using outside

theorem assign_labels_permutation {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (first last : List α) (distinct : (first ++ last).Nodup) :
    ((first ++ last).map (assign old first last)).Perm ((first ++ last).map old) := by
  rw [assign_slots old first last distinct]
  exact slots_perm old first last

-- Any complete roster decomposition lifts the sparse permutation. This is a
-- specification theorem; the update does not enumerate that complement.
theorem whole_roster_permutation {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (first last outside roster : List α)
    (distinct : (first ++ last).Nodup)
    (cover : roster.Perm ((first ++ last) ++ outside))
    (disjoint : ∀ x ∈ outside, x ∉ first ++ last) :
    (roster.map (assign old first last)).Perm (roster.map old) := by
  have untouched : outside.map (assign old first last) = outside.map old := by
    apply List.map_congr_left
    intro x hx
    exact assign_outside old first last x (disjoint x hx)
  have perm := (assign_labels_permutation old first last distinct).append
    (List.Perm.of_eq untouched)
  exact ((cover.map _).trans (by simpa only [List.map_append] using perm)).trans (cover.map old).symm

theorem assign_injective {α} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    (old : α → Nat) (first last : List α) (distinct : (first ++ last).Nodup)
    (unique : Function.Injective old) : Function.Injective (assign old first last) := by
  let keys := first ++ last
  let next := assign old first last
  have before : (keys.map old).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact distinct.imp (fun ne eq => ne (unique eq))
  have perm := assign_labels_permutation old first last distinct
  have after : (keys.map next).Nodup := perm.nodup_iff.mpr before
  have image : ∀ x ∈ keys, ∃ y ∈ keys, old y = next x := by
    intro x mx
    exact List.mem_map.mp (perm.mem_iff.mp (List.mem_map_of_mem mx))
  intro x y eq
  by_cases mx : x ∈ keys
  · by_cases my : y ∈ keys
    · obtain ⟨i, hi, hx⟩ := List.getElem_of_mem mx
      obtain ⟨j, hj, hy⟩ := List.getElem_of_mem my
      have ij := after.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
        (by simpa only [List.getElem_map, hx, hy] using eq)
      subst j
      exact hx.symm.trans hy
    · obtain ⟨w, mw, ew⟩ := image x mx
      have ey := assign_outside old first last y my
      have wy : w = y := unique (ew.trans (eq.trans ey))
      exact False.elim (my (wy ▸ mw))
  · have ex := assign_outside old first last x mx
    by_cases my : y ∈ keys
    · obtain ⟨w, mw, ew⟩ := image y my
      have wx : w = x := unique (ew.trans (eq.symm.trans ex))
      exact False.elim (mx (wx ▸ mw))
    · exact unique (ex.symm.trans (eq.trans (assign_outside old first last y my)))

end LeanPoo.Functional.RankLabels
