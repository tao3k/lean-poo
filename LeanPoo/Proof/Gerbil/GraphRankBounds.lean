import Std

namespace GraphRankBounds

-- Consumer -> provider orientation; all ranks belong to admitted live owners.
theorem forward_bound (low high owner dep : Nat) (edge : dep < owner)
    (ownerWithin : owner ≤ high) :
    (low ≤ dep ∧ dep ≤ high) ↔ low ≤ dep := by
  exact ⟨And.left, fun h => ⟨h, Nat.le_trans (Nat.le_of_lt edge) ownerWithin⟩⟩

theorem reverse_bound (low high owner reader : Nat) (edge : owner < reader)
    (ownerWithin : low ≤ owner) :
    (low ≤ reader ∧ reader ≤ high) ↔ reader ≤ high := by
  exact ⟨And.right, fun h => ⟨Nat.le_trans ownerWithin (Nat.le_of_lt edge), h⟩⟩

theorem forward_floor (high owner dep : Nat) (edge : dep < owner)
    (ownerWithin : owner ≤ high) : 0 ≤ dep ∧ dep ≤ high :=
  (forward_bound 0 high owner dep edge ownerWithin).mpr (Nat.zero_le dep)

theorem reverse_ceiling (low high owner reader frontier : Nat)
    (edge : owner < reader) (ownerWithin : low ≤ owner)
    (readerWithin : reader < frontier) (ceiling : frontier - 1 ≤ high) :
    low ≤ reader ∧ reader ≤ high := by
  apply (reverse_bound low high owner reader edge ownerWithin).mpr
  omega

-- Local relabels keep old labels, insertions append fresh labels, and removals
-- leave holes. Only LIVE ranks need bounds; no dense-roster enumeration occurs.
def patch (old : A → Option Nat) (edits : A → Option (Option Nat)) : A → Option Nat :=
  fun key => match edits key with | none => old key | some value => value

theorem patch_bounded (old : A → Option Nat) (edits : A → Option (Option Nat))
    (before after : Nat) (grows : before ≤ after)
    (oldBound : ∀ key rank, old key = some rank → rank < before)
    (editBound : ∀ key rank, edits key = some (some rank) → rank < after) :
    ∀ key rank, patch old edits key = some rank → rank < after := by
  intro key rank found
  cases h : edits key with
  | none =>
    have previous : old key = some rank := by simpa [patch, h] using found
    exact Nat.lt_of_lt_of_le (oldBound key rank previous) grows
  | some value =>
    have current : value = some rank := by simpa [patch, h] using found
    exact editBound key rank (by simpa [current] using h)

theorem reused_label_bounded (old : A → Option Nat) (before after rank : Nat)
    (grows : before ≤ after) (oldBound : ∀ key r, old key = some r → r < before)
    (reused : ∃ key, old key = some rank) : rank < after := by
  obtain ⟨key, found⟩ := reused
  exact Nat.lt_of_lt_of_le (oldBound key rank found) grows

-- Exact sequence, not merely the reachable set: prune redundant bounds only
-- when EVERY row member has the corresponding admitted edge/rank certificate.
theorem forward_row (row : List A) (rank : A → Nat) (low high owner : Nat)
    (edges : ∀ key ∈ row, rank key < owner) (ownerWithin : owner ≤ high) :
    row.filter (fun key => decide (low ≤ rank key ∧ rank key ≤ high)) =
      row.filter (fun key => decide (low ≤ rank key)) := by
  apply List.filter_congr
  intro key member
  simp only [forward_bound low high owner (rank key) (edges key member) ownerWithin]

theorem reverse_row (row : List A) (rank : A → Nat) (low high owner : Nat)
    (edges : ∀ key ∈ row, owner < rank key) (ownerWithin : low ≤ owner) :
    row.filter (fun key => decide (low ≤ rank key ∧ rank key ≤ high)) =
      row.filter (fun key => decide (rank key ≤ high)) := by
  apply List.filter_congr
  intro key member
  simp only [reverse_bound low high owner (rank key) (edges key member) ownerWithin]

theorem forward_all_row (row : List A) (rank : A → Nat) (high owner : Nat)
    (edges : ∀ key ∈ row, rank key < owner) (ownerWithin : owner ≤ high) :
    row.filter (fun key => decide (0 ≤ rank key ∧ rank key ≤ high)) = row := by
  apply List.filter_eq_self.mpr
  intro key member
  exact decide_eq_true (forward_floor high owner (rank key) (edges key member) ownerWithin)

theorem reverse_all_row (row : List A) (rank : A → Nat) (low high owner frontier : Nat)
    (edges : ∀ key ∈ row, owner < rank key) (ownerWithin : low ≤ owner)
    (bounds : ∀ key ∈ row, rank key < frontier) (ceiling : frontier - 1 ≤ high) :
    row.filter (fun key => decide (low ≤ rank key ∧ rank key ≤ high)) = row := by
  apply List.filter_eq_self.mpr
  intro key member
  exact decide_eq_true (reverse_ceiling low high owner (rank key) frontier
    (edges key member) ownerWithin (bounds key member) ceiling)

#print axioms forward_bound
-- Cardinality is not a substitute for the monotone label frontier after removal.
example : ¬ (∀ rank ∈ ([0, 1, 3, 4, 5] : List Nat),
    rank < ([0, 1, 3, 4, 5] : List Nat).length) := by decide

#print axioms reverse_bound
#print axioms forward_floor
#print axioms reverse_ceiling
#print axioms patch_bounded
#print axioms reused_label_bounded
#print axioms forward_row
#print axioms reverse_row
#print axioms forward_all_row
#print axioms reverse_all_row

-- Sort the two disjoint frontier groups once. Their sorted rank projections
-- can be merged to produce exactly the old sorted label stream.
theorem merge_repair_labels (forward backward : List Nat) :
    List.merge (forward.mergeSort) (backward.mergeSort) =
      (forward ++ backward).mergeSort := by
  have trans : ∀ a b c : Nat, decide (a ≤ b) → decide (b ≤ c) → decide (a ≤ c) := by
    intro a b c ab bc
    simpa using Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)
  have total : ∀ a b : Nat, decide (a ≤ b) || decide (b ≤ a) := by
    intro a b
    simp [Nat.le_total]
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
  · intro a b _ _ ab ba; exact Nat.le_antisymm ab ba
  · simpa using List.pairwise_merge trans total _ _
      (List.pairwise_mergeSort trans total forward)
      (List.pairwise_mergeSort trans total backward)
  · simpa using List.pairwise_mergeSort trans total (forward ++ backward)
  · exact (List.merge_perm_append _).trans
      (((List.mergeSort_perm forward _).append (List.mergeSort_perm backward _)).trans
        (List.mergeSort_perm (forward ++ backward) _).symm)


-- The marked labels are the reached labels. Their ascending scan is
-- therefore the same stream as sorting the reached list.
theorem dense_scan_exact (reached scan : List Nat)
    (same : scan.Perm reached) (ordered : scan.Pairwise (· ≤ ·)) :
    scan = reached.mergeSort := by
  have trans : ∀ a b c : Nat, decide (a ≤ b) → decide (b ≤ c) → decide (a ≤ c) := by
    intro a b c ab bc
    simpa using Nat.le_trans (of_decide_eq_true ab) (of_decide_eq_true bc)
  have total : ∀ a b : Nat, decide (a ≤ b) || decide (b ≤ a) := by
    intro a b
    simp [Nat.le_total]
  apply List.Perm.eq_of_pairwise (le := fun a b : Nat => a ≤ b)
  · intro a b _ _ ab ba
    exact Nat.le_antisymm ab ba
  · exact ordered
  · simpa using List.pairwise_mergeSort trans total reached
  · exact same.trans (List.mergeSort_perm reached _).symm


-- Rebuilding the inverse from successor positions preserves each rank
-- exactly when the completed position mapping is a bijection on live owners.
theorem rebuilt_rank_exact (position : Nat → Option A) (rank : A → Nat)
    (inverse : ∀ key, position (rank key) = some key)
    (unique : ∀ label key, position label = some key → label = rank key)
    (key : A) (label : Nat) : position label = some key ↔ label = rank key :=
  ⟨unique label key, fun equal => equal.symm ▸ inverse key⟩

end GraphRankBounds
