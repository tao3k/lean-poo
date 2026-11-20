-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.MultimethodSemantics

/-! Stable ranking can be performed before pure, argument-sensitive
selection. Observations which produce the live decisions stay at their
original per-method and per-specializer positions. -/
namespace LeanPoo.Object.ClosAdmission.CandidateOrder

variable {Item : Type u} {order : Item → Item → Bool}

private theorem merge_at_cut (head : Item) (left right : List Item)
    (before : ∀ item ∈ left, order head item = false)
    (after : ∀ item ∈ right, order head item = true) :
    [head].merge (left ++ right) order = left ++ head :: right := by
  induction left with
  | nil =>
    cases right with
    | nil => simp
    | cons first rest =>
      simp [after first (by simp)]
  | cons first rest ih =>
    simp only [List.cons_append, List.cons_merge_cons, before first (by simp), Bool.false_eq_true,
      ite_false]
    rw [ih (fun item member => before item (List.mem_cons_of_mem _ member))]

private theorem sort_cons (trans : ∀ a b c, order a b → order b c → order a c)
    (total : ∀ a b, order a b || order b a) (head : Item) (tail : List Item) :
    (head :: tail).mergeSort order = [head].merge (tail.mergeSort order) order := by
  obtain ⟨left, right, whole, rest, before⟩ := List.mergeSort_cons trans total head tail
  have sorted := List.pairwise_mergeSort trans total (head :: tail)
  rw [whole] at sorted
  have after : ∀ item ∈ right, order head item = true := by
    intro item member
    exact List.rel_of_pairwise_cons (List.pairwise_append.mp sorted).2.1 member
  rw [whole, rest, merge_at_cut head left right _ after]
  intro item member
  simpa using before item member

private theorem merge_first (head : Item) (items : List Item)
    (first : ∀ item ∈ items, order head item = true) :
    [head].merge items order = head :: items := by
  cases items with
  | nil => simp
  | cons item rest => simp [first item (by simp)]

private theorem filter_insert (trans : ∀ a b c, order a b → order b c → order a c)
    (keep : Item → Bool) (head : Item) (items : List Item)
    (sorted : items.Pairwise (fun a b => order a b = true)) :
    ([head].merge items order).filter keep =
      ([head].filter keep).merge (items.filter keep) order := by
  induction items with
  | nil => simp
  | cons item rest ih =>
    rw [List.cons_merge_cons]
    cases h : order head item with
    | false =>
      cases k : keep item <;> cases retain : keep head <;> simp [h, k, retain, ih sorted.tail]
    | true =>
      have first : ∀ candidate ∈ item :: rest, order head candidate = true := by
        intro candidate member
        rcases List.mem_cons.mp member with same | later
        · simpa [same] using h
        · exact trans head item candidate h (List.rel_of_pairwise_cons sorted later)
      cases k : keep head with
      | false => simp [k]
      | true =>
        simp only [ite_true, List.nil_merge, List.filter_cons, k, List.filter_nil]
        have merged := merge_first head ((item :: rest).filter keep)
          (fun candidate member => first candidate (List.mem_filter.mp member).1)
        simpa only [List.filter_cons] using merged.symm

/-- Moving stable sort across a pure filter preserves both lexicographic
specificity and the source-generation order for equal distance vectors. -/
theorem filter_published_order (trans : ∀ a b c, order a b → order b c → order a c)
    (total : ∀ a b, order a b || order b a) (keep : Item → Bool) (rows : List Item) :
    (rows.mergeSort order).filter keep = (rows.filter keep).mergeSort order := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    rw [sort_cons trans total, filter_insert trans keep row _ (List.pairwise_mergeSort trans total rest), ih]
    cases hit : keep row <;> simp [hit, sort_cons trans total]

open LeanPoo.Object

/-- The existing sparse C4 trie is the publication-time lookup. Keeping
guards in the ordered entries allows the normal live selection to run. -/
theorem indexed_candidates_reference (generic : Multimethod Args Method Result)
    (shape : DispatchShape) (args : Args) :
    MethodCandidate.select (generic.candidatesFor shape) args =
      MethodCandidate.select
        (generic.index.reference (shape.map fun keys => keys.map Specializer.prototype ++ [.any])).toArray args := by
  simpa using congrArg (fun methods => MethodCandidate.select methods.toArray args)
    (Multimethod.candidates_reference generic shape)

end LeanPoo.Object.ClosAdmission.CandidateOrder
