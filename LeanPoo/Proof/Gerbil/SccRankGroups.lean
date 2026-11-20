import LeanPoo.Proof.Gerbil.GraphOrdinalBuckets

namespace LeanPoo.Proof.Gerbil.SccRankGroups

open GraphOrdinalBuckets (bucketOf reverse_scatter_exact)

variable {Owner Rank : Type} [DecidableEq Rank]

def push (rank : Owner → Rank) (wanted : Rank) (row : List Owner)
    (owner : Owner) : List Owner :=
  if rank owner = wanted then owner :: row else row

theorem forward_accumulation (rank : Owner → Rank) (wanted : Rank)
    (owners saved : List Owner) :
    owners.foldl (push rank wanted) saved =
      (bucketOf id rank wanted owners).reverse ++ saved := by
  induction owners generalizing saved with
  | nil => rfl
  | cons owner rest ih =>
    by_cases hit : rank owner = wanted
    · simp [push, bucketOf, hit, List.reverse_cons, List.append_assoc, ih]
    · simp [push, bucketOf, hit, ih]

/-- Fill the final member spines by walking the roster backwards.
This removes the later list reversal for every SCC, including cyclic SCCs. -/
theorem group_members_exact (rank : Owner → Rank) (wanted : Rank)
    (owners : List Owner) :
    owners.reverse.foldl (push rank wanted) [] =
      (owners.foldl (push rank wanted) []).reverse := by
  rw [forward_accumulation rank wanted owners [], List.append_nil, List.reverse_reverse]
  exact reverse_scatter_exact id rank wanted owners

/-- The head of the final group is the first owner of that rank in roster
order. An absent rank remains absent. -/
theorem representative_exact (rank : Owner → Rank) (wanted : Rank)
    (owners : List Owner) :
    (owners.reverse.foldl (push rank wanted) []).head? =
      owners.find? (fun owner => decide (rank owner = wanted)) := by
  rw [show owners.reverse.foldl (push rank wanted) [] = bucketOf id rank wanted owners by
    exact reverse_scatter_exact id rank wanted owners]
  simp [bucketOf]

#print axioms group_members_exact
#print axioms representative_exact

end LeanPoo.Proof.Gerbil.SccRankGroups
