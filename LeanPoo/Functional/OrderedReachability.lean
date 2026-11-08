-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std.Data.HashMap.Lemmas

namespace LeanPoo.Functional.OrderedReachability

-- The index contains Unit markers only. It is a private visited set, not a
-- cache of source approvals or business outcomes. Adjacency is captured data.
def Covers (index : Std.HashMap Nat Unit) (seen : List Nat) : Prop :=
  ∀ key, index[key]? = some () ↔ key ∈ seen

theorem empty_covers : Covers (∅ : Std.HashMap Nat Unit) [] := by
  intro key
  simp

theorem insert_covers {index : Std.HashMap Nat Unit} {seen : List Nat}
    (covered : Covers index seen) (key : Nat) :
    Covers (index.insert key ()) (key :: seen) := by
  intro query
  by_cases same : key = query
  · subst query
    simp
  · have read : (index.insert key ())[query]? = index[query]? := by
      simp [Std.HashMap.getElem?_insert, same]
    rw [read]
    simpa [List.mem_cons, Ne.symm same] using covered query

-- Fuel exposes every finite prefix; it is a proof device, not a native timeout.
def listRun (reads : Nat → List Nat) : Nat → List Nat → List Nat → List Nat × List Nat
  | 0, todo, seen => (todo, seen)
  | _ + 1, [], seen => ([], seen)
  | fuel + 1, key :: rest, seen =>
    if key ∈ seen then listRun reads fuel rest seen
    else listRun reads fuel (reads key ++ rest) (key :: seen)

def indexedRun (reads : Nat → List Nat) :
    Nat → List Nat → List Nat → Std.HashMap Nat Unit →
      List Nat × List Nat × Std.HashMap Nat Unit
  | 0, todo, seen, index => (todo, seen, index)
  | _ + 1, [], seen, index => ([], seen, index)
  | fuel + 1, key :: rest, seen, index =>
    if index[key]? = some () then indexedRun reads fuel rest seen index
    else indexedRun reads fuel (reads key ++ rest) (key :: seen) (index.insert key ())

theorem indexed_prefix_exact (reads : Nat → List Nat) (fuel : Nat)
    (todo seen : List Nat) (index : Std.HashMap Nat Unit) (covered : Covers index seen) :
    let result := indexedRun reads fuel todo seen index
    (result.1, result.2.1) = listRun reads fuel todo seen ∧ Covers result.2.2 result.2.1 := by
  induction fuel generalizing todo seen index with
  | zero => exact ⟨rfl, covered⟩
  | succ fuel ih =>
    cases todo with
    | nil => exact ⟨rfl, covered⟩
    | cons key rest =>
      by_cases found : key ∈ seen
      · have present := (covered key).mpr found
        simp only [indexedRun, listRun, ite_eq_left present, ite_eq_left found]
        exact ih rest seen index covered
      · have absent : index[key]? ≠ some () := fun h => found ((covered key).mp h)
        simp only [indexedRun, listRun, ite_eq_right absent, ite_eq_right found]
        exact ih (reads key ++ rest) (key :: seen) (index.insert key ()) (insert_covers covered key)

theorem list_seen_unique (reads : Nat → List Nat) (fuel : Nat)
    (todo seen : List Nat) (unique : seen.Nodup) :
    (listRun reads fuel todo seen).2.Nodup := by
  induction fuel generalizing todo seen with
  | zero => exact unique
  | succ fuel ih =>
    cases todo with
    | nil => exact unique
    | cons key rest =>
      by_cases found : key ∈ seen
      · simpa only [listRun, ite_eq_left found] using ih rest seen unique
      · simpa only [listRun, ite_eq_right found] using
          ih (reads key ++ rest) (key :: seen) (List.nodup_cons.mpr ⟨found, unique⟩)

theorem indexed_seen_unique (reads : Nat → List Nat) (fuel : Nat) (root : Nat) :
    (indexedRun reads fuel [root] [] ∅).2.1.Nodup := by
  have exactPrefix := (indexed_prefix_exact reads fuel [root] [] ∅ empty_covers).1
  have same := congrArg Prod.snd exactPrefix
  change (indexedRun reads fuel [root] [] ∅).2.1 = (listRun reads fuel [root] []).2 at same
  rw [same]
  exact list_seen_unique reads fuel [root] [] (by simp)

end LeanPoo.Functional.OrderedReachability
