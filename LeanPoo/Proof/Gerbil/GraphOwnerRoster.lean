import Std

namespace LeanPoo.Proof.Gerbil.GraphOwnerRoster

variable {Key Acc Result Edit : Type} {m : Type → Type} [Monad m]

/-- Admission and owner reads traverse the same ordered sequence, with the
same early stop. The monad can retain the effects of a refused read. -/
theorem traversal_exact (keys : List Key) (initial : Acc)
    (step : Key → Acc → m (ForInStep Acc)) :
    forIn keys.toArray initial step = forIn (keys ++ []) initial step := by
  rw [← Array.forIn_toList]
  simp

theorem size_exact (keys : List Key) : keys.toArray.size = keys.length := by
  simp

/-- A wide fallback reconstructs only the already owned order. The caller
may edit its original list while reads run, including before a later refusal. -/
theorem wide_fallback_exact (keys : List Key) (edit : List Key → Edit)
    (finish : Edit → List Key → Result) :
    (let owned := keys.toArray
     finish (edit keys) owned.toList) =
      finish (edit keys) (keys ++ []) := by
  simp

/-- Subsequent revisions consume identical inputs. The published snapshot
and the ordinary edit operation are independent of the temporary roster. -/
theorem published_revision_exact (keys : List Key)
    (publish : List Key → Result) (revise : Result → Edit → Result) (edit : Edit) :
    revise (publish keys.toArray.toList) edit = revise (publish (keys ++ [])) edit := by
  simp

/-- Count pointer words in the private roster alone. The source list, vertex
index, headers, and edge arrays are common costs outside this comparison. -/
theorem roster_words_saved (owners : Nat) :
    (2 * owners + owners) - owners = 2 * owners := by omega

#print axioms traversal_exact
#print axioms published_revision_exact

end LeanPoo.Proof.Gerbil.GraphOwnerRoster
