import LeanPoo.Prototype.Representation

/-! Sparse ordered contribution indices for persistent prototype deletion.
The standard RBTree supplies persistent keyed operations; this finite model proves
the name/ordinal contract, not balancing, pointer sharing or machine-time bounds.
Ordinals identify contributions, while String keys identify symbols injectively.
-/
namespace LeanPoo.Prototype.Representation

/-- Record another contribution while retaining the FIRST replacement ordinal. -/
def rememberPosition (positions : List Nat) (next : Nat) : List Nat :=
  match positions with
  | [] => [next]
  | first :: rest => first :: next :: rest

/-- Every new position is recorded, and no earlier method position disappears. -/
theorem rememberPosition_mem (positions : List Nat) (next index : Nat) :
    index ∈ rememberPosition positions next ↔ index = next ∨ index ∈ positions := by
  cases positions with
  | nil => simp [rememberPosition]
  | cons first rest => simp [rememberPosition, or_left_comm]

/-- Duplicate declarations keep first-method replacement independent of tail order. -/
@[simp] theorem rememberPosition_first (first next : Nat) (rest : List Nat) :
    (rememberPosition (first :: rest) next).head? = some first := rfl

/-- Logical position count grows by one; a singleton needs no physical list. -/
@[simp] theorem rememberPosition_length (positions : List Nat) (next : Nat) :
    (rememberPosition positions next).length = positions.length + 1 := by
  cases positions <;> simp [rememberPosition] <;> omega

/-- Unordered duplicate tails contain exactly the same ordinals as ordered append. -/
theorem rememberPosition_perm (positions : List Nat) (next : Nat) :
    (rememberPosition positions next).Perm (positions ++ [next]) := by
  cases positions with
  | nil => simp [rememberPosition]
  | cons first rest =>
    have swap : ([next] ++ rest).Perm (rest ++ [next]) := List.perm_append_comm
    exact swap.cons first

/-- Observe payloads in contribution order; gaps in private ordinals are invisible. -/
def orderedPayloads (entries : List (Nat × (String × Value))) := entries.map Prod.snd

/-- The private name index must contain exactly the ordinals of this name. -/
def IndexMatches (entries : List (Nat × (String × Value))) (name : String)
    (positions : List Nat) : Prop :=
  ∀ entry ∈ entries, entry.1 ∈ positions ↔ entry.2.1 = name

/-- Semantic effect of delegating every indexed ordinal to persistent removal. -/
def erasePositions (entries : List (Nat × (String × Value))) (positions : List Nat) :=
  entries.filter (fun entry => !positions.contains entry.1)

/-- Complete indexed removal has the same observation as the old full filter. -/
theorem erasePositions_observe (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (indexed : IndexMatches entries name positions) :
    orderedPayloads (erasePositions entries positions) = erase (orderedPayloads entries) name := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    have head := indexed entry (by simp)
    have rest : IndexMatches tail name positions := fun item present => indexed item (by simp [present])
    have step := ih rest
    by_cases same : entry.2.1 = name
    · have present := head.mpr same
      simp [erasePositions, orderedPayloads, erase, present, same] at step ⊢
      exact step
    · have absent : entry.1 ∉ positions := fun present => same (head.mp present)
      simp [erasePositions, orderedPayloads, erase, absent, same] at step ⊢
      exact step

/-- A successful removal forgets every same-name method, not only the first. -/
theorem erasePositions_absent (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (indexed : IndexMatches entries name positions) :
    first (orderedPayloads (erasePositions entries positions)) name = none := by
  rw [erasePositions_observe entries name positions indexed]
  exact first_erase _ name

/-- Indexed deletion refines the existing storage/edit protocol for either policy. -/
theorem erasePositions_storage (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat) (compact : Bool)
    (indexed : IndexMatches entries name positions) :
    orderedPayloads (erasePositions entries positions) =
      (editStorage (packWith compact (orderedPayloads entries)) (.remove name)).entries := by
  rw [erasePositions_observe entries name positions indexed]
  simp [editStorage]

/-- Any untouched name's ordinal index remains valid without reconstruction. -/
theorem erasePositions_preserves_index (entries : List (Nat × (String × Value)))
    (positions other : List Nat) (name : String) (indexed : IndexMatches entries name other) :
    IndexMatches (erasePositions entries positions) name other := by
  intro entry present
  exact indexed entry (List.mem_filter.mp present).1

/-- No positions means no persistent tree work and the exact original observation. -/
@[simp] theorem erasePositions_empty (entries : List (Nat × (String × Value))) :
    erasePositions entries [] = entries := by simp [erasePositions]

/-- New contributions use a high-water ordinal, never the number of live entries. -/
def appendPosition (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) := entries ++ [(next, (name, value))]

/-- Appending after arbitrary gaps retains every surviving contribution in order. -/
@[simp] theorem appendPosition_observe (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) :
    orderedPayloads (appendPosition entries next name value) = orderedPayloads entries ++ [(name, value)] := by
  simp [appendPosition, orderedPayloads]

/-- The next ordinal strictly exceeds every live position. -/
def PositionsBelow (entries : List (Nat × (String × Value))) (next : Nat) : Prop :=
  ∀ entry ∈ entries, entry.1 < next

/-- Deletion retains the high-water certificate even when live count shrinks. -/
theorem positionsBelow_erase (entries : List (Nat × (String × Value)))
    (next : Nat) (positions : List Nat) (bound : PositionsBelow entries next) :
    PositionsBelow (erasePositions entries positions) next := by
  intro entry present
  exact bound entry (List.mem_filter.mp present).1

/-- Advancing the high-water mark makes repeated delete/reinsert append safe. -/
theorem positionsBelow_append (entries : List (Nat × (String × Value)))
    (next : Nat) (name : String) (value : Value) (bound : PositionsBelow entries next) :
    PositionsBelow (appendPosition entries next name value) (next + 1) := by
  intro entry present
  simp only [appendPosition, List.mem_append, List.mem_singleton] at present
  rcases present with old | rfl
  · exact Nat.lt_trans (bound entry old) (by omega)
  · simp

/-- Fresh insertion cannot replace an unrelated survivor with the same ordinal. -/
theorem next_position_fresh (entries : List (Nat × (String × Value)))
    (next : Nat) (bound : PositionsBelow entries next) (entry) (present : entry ∈ entries) :
    entry.1 ≠ next := Nat.ne_of_lt (bound entry present)

/-- The canonical finite index used to state admission and primitive-work counts. -/
def matchingPositions (entries : List (Nat × (String × Value))) (name : String) :=
  (entries.filter (fun entry => entry.2.1 == name)).map Prod.fst

/-- Key uniqueness makes a derived index sound even after ordinal gaps appear. -/
theorem matchingPositions_valid (entries : List (Nat × (String × Value)))
    (name : String)
    (unique : ∀ a ∈ entries, ∀ b ∈ entries, a.1 = b.1 → a.2.1 = b.2.1) :
    IndexMatches entries name (matchingPositions entries name) := by
  intro entry present
  constructor
  · intro indexed
    obtain ⟨other, selected, equal⟩ := List.mem_map.mp indexed
    obtain ⟨old, chosen⟩ := List.mem_filter.mp selected
    have same : other.2.1 = name := by simpa using chosen
    exact (unique entry present other old equal.symm).trans same
  · intro same
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨present, by simp [same]⟩, rfl⟩

/-- Present-name work: one lookup, one deletion per contribution and one index removal.
The standard tree's per-operation cost and bounded compact demotion are separate. -/
def indexedEraseWork (positions : List Nat) := positions.length + 2

/-- Sparse deletion's delegated work depends on matching methods, not unrelated names. -/
theorem indexedEraseWork_exact (entries : List (Nat × (String × Value))) (name : String) :
    indexedEraseWork (matchingPositions entries name) =
      (entries.filter (fun entry => entry.2.1 == name)).length + 2 := by
  simp [indexedEraseWork, matchingPositions]

/-- Cost needs an exact index certificate: semantic membership alone can admit
unused ordinals. Permutation permits the implementation's unordered duplicate tail. -/
theorem indexedEraseWork_permutation (entries : List (Nat × (String × Value)))
    (name : String) (positions : List Nat)
    (complete : positions.Perm (matchingPositions entries name)) :
    indexedEraseWork positions =
      (entries.filter (fun entry => entry.2.1 == name)).length + 2 := by
  rw [indexedEraseWork, complete.length_eq]
  simp [matchingPositions]

end LeanPoo.Prototype.Representation
