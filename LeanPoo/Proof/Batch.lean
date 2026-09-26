import LeanPoo.Proof.Reuse

namespace LeanPoo.Proof

universe u v

/-- The identity patch for a typed state. -/
def Patch.empty : Patch Key Value where
  apply := id
  touched := []
  frame := by intros; rfl
  obligations := []

/-- Compose an ordered sequence of patches through the existing `then`. -/
def Patch.composeAll (patches : List (Patch Key Value)) : Patch Key Value :=
  patches.foldl Patch.then Patch.empty

theorem Patch.composeAll_snoc (patches : List (Patch Key Value))
    (last : Patch Key Value) :
    Patch.composeAll (patches ++ [last]) =
      (Patch.composeAll patches).then last := by
  simp [Patch.composeAll]

/-- A typed batch of direct overrides; the last occurrence of a key wins. -/
def Patch.setMany [DecidableEq Key] (updates : List (Sigma Value))
    (obligations : List (Obligation Key Value) := []) : Patch Key Value :=
  let combined := Patch.composeAll (updates.map fun update =>
    Patch.set update.1 update.2)
  { combined with obligations := obligations }

theorem Patch.composeAll_touched (patches : List (Patch Key Value)) :
    (Patch.composeAll patches).touched = patches.flatMap Patch.touched := by
  have go : ∀ (remaining : List (Patch Key Value)) (combined : Patch Key Value),
      (remaining.foldl Patch.then combined).touched =
        combined.touched ++ remaining.flatMap Patch.touched := by
    intro remaining
    induction remaining with
    | nil => intro combined; simp
    | cons next tail inductionHypothesis =>
        intro combined
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        simp [Patch.then, List.append_assoc]
  unfold Patch.composeAll
  simpa [Patch.empty] using go patches Patch.empty

/-- The dependency footprint of a batch is exactly its ordered key list. -/
theorem Patch.setMany_touched [DecidableEq Key]
    (updates : List (Sigma Value))
    (obligations : List (Obligation Key Value) := []) :
    (Patch.setMany updates obligations).touched = updates.map Sigma.fst := by
  simp only [Patch.setMany, Patch.composeAll_touched, List.flatMap_map]
  induction updates with
  | nil => rfl
  | cons update tail inductionHypothesis =>
      have tailKeys : List.flatMap (fun entry => [entry.1]) tail =
          tail.map Sigma.fst := by
        simpa [Patch.set] using inductionHypothesis
      simp [Patch.set, tailKeys]

/-- An ordered batch keeps the final write at a repeated key. -/
theorem Patch.setMany_last [DecidableEq Key]
    (earlier : List (Sigma Value)) (key : Key) (value : Value key)
    (state : State Key Value) :
    (Patch.setMany (earlier ++ [⟨key, value⟩])).apply state key = value := by
  simp only [Patch.setMany, List.map_append, List.map_cons, List.map_nil,
    Patch.composeAll_snoc]
  simp [Patch.then, Patch.set]

theorem append_empty (object : ProofObject Key Value) :
    append object (Patch.empty : Patch Key Value) = object := by
  cases object
  simp [append, Patch.empty]

/-- Batch composition and stepwise append yield the same state and obligations. -/
theorem append_composeAll (object : ProofObject Key Value)
    (patches : List (Patch Key Value)) :
    append object (Patch.composeAll patches) =
      patches.foldl append object := by
  let rec go (remaining : List (Patch Key Value))
      (combined : Patch Key Value) (current : ProofObject Key Value)
      (agreement : append object combined = current) :
      append object (remaining.foldl Patch.then combined) =
        remaining.foldl append current := by
    cases remaining with
    | nil => exact agreement
    | cons next tail =>
        simp only [List.foldl_cons]
        apply go tail (combined.then next) (append current next)
        rw [← append_then, agreement]
  unfold Patch.composeAll
  exact go patches Patch.empty object (append_empty object)

/-- A dependency is safe for a batch step exactly when each component leaves it alone. -/
theorem unaffected_then_iff (obligation : Obligation Key Value)
    (first second : Patch Key Value) :
    unaffected obligation (first.then second) ↔
      unaffected obligation first ∧ unaffected obligation second := by
  constructor
  · intro safe
    constructor
    · intro key dependency touched
      exact safe key dependency (List.mem_append.mpr (Or.inl touched))
    · intro key dependency touched
      exact safe key dependency (List.mem_append.mpr (Or.inr touched))
  · intro ⟨safeFirst, safeSecond⟩ key dependency touched
    rcases List.mem_append.mp touched with inFirst | inSecond
    · exact safeFirst key dependency inFirst
    · exact safeSecond key dependency inSecond

/-- Reuse across a batch requires safety for every constituent patch. -/
theorem unaffected_composeAll_iff (obligation : Obligation Key Value)
    (patches : List (Patch Key Value)) :
    unaffected obligation (Patch.composeAll patches) ↔
      ∀ patch, patch ∈ patches → unaffected obligation patch := by
  simp only [unaffected, Patch.composeAll_touched]
  constructor
  · intro safe patch membership key dependency touched
    exact safe key dependency (List.mem_flatMap.mpr
      ⟨patch, membership, touched⟩)
  · intro safe key dependency touched
    obtain ⟨patch, membership, patchTouched⟩ := List.mem_flatMap.mp touched
    exact safe patch membership key dependency patchTouched

/-- A typed override batch preserves an obligation exactly when none of its
declared dependencies occurs among the updated keys. -/
theorem unaffected_setMany_iff [DecidableEq Key]
    (obligation : Obligation Key Value) (updates : List (Sigma Value))
    (obligations : List (Obligation Key Value) := []) :
    unaffected obligation (Patch.setMany updates obligations) ↔
      ∀ key, key ∈ obligation.dependencies → key ∉ updates.map Sigma.fst := by
  simp only [unaffected, Patch.setMany_touched]

end LeanPoo.Proof
