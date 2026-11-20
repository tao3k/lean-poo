import Std

namespace InvalidationKeySnapshot
variable {Owner : Type}

def byRank (rank : Owner → Nat) (a b : Owner) : Bool := decide (rank a ≤ rank b)

-- Two hash enumerations can differ in order. Both are complete and unique
-- enumerations of the reached set at the lock's capture point.
theorem same_ranked_keys (rank : Owner → Nat) (copied direct : List Owner)
    (same : copied.Perm direct)
    (unique : ∀ a b, a ∈ copied → b ∈ direct → rank a = rank b → a = b) :
    copied.mergeSort (byRank rank) = direct.mergeSort (byRank rank) := by
  have ordered (keys : List Owner) :
      (keys.mergeSort (byRank rank)).Pairwise (fun a b => byRank rank a b = true) := by
    apply List.pairwise_mergeSort
    · intro a b c ab bc
      simpa [byRank] using Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)
    · intro a b
      cases Nat.le_total (rank a) (rank b) with
      | inl ab => simp [byRank, ab]
      | inr ba => simp [byRank, ba]
  apply List.Perm.eq_of_pairwise _ (ordered copied) (ordered direct)
  · exact (List.mergeSort_perm copied _).trans (same.trans (List.mergeSort_perm direct _).symm)
  · intro a b am bm ab ba
    exact unique a b (List.mem_mergeSort.mp am) (List.mem_mergeSort.mp bm)
      (Nat.le_antisymm (of_decide_eq_true ab) (of_decide_eq_true ba))

-- Model a single completed lock section. The captured owned list is a value
-- independent of the live reached table and its later extensions/restages.
def afterCapture (reached : List Owner) (next : List Owner → List Owner) :
    List Owner × List Owner := (reached, next reached)

theorem captured_keys_stable (reached : List Owner) (next : List Owner → List Owner)
    (key : Owner) : key ∈ (afterCapture reached next).1 ↔ key ∈ reached := Iff.rfl

-- Borrowing a view of the live table instead is observably wrong, even for
-- an append-only extension; an earlier candidate would see the added owner.
example : 2 ∉ (afterCapture [1] (fun keys => keys ++ [2])).1 ∧
    2 ∈ (afterCapture [1] (fun keys => keys ++ [2])).2 := by decide

#print axioms same_ranked_keys
#print axioms captured_keys_stable
end InvalidationKeySnapshot
