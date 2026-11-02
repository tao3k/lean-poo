import Init.Data.List.Erase
import Init.Data.List.Nat.TakeDrop

/-! Ordered association operations used by method declaration inventories and
bounded dispatch caches. Equality of host keys and unique private construction
are explicit premises, not a proof of Gerbil's runtime storage. -/
namespace LeanPoo.Functional.Parameters

/-- Standard association removal deletes only the first matching key. -/
def eraseBinding [DecidableEq Key] (key : Entry → Key) (name : Key) (entries : List Entry) : List Entry :=
  entries.eraseP (fun entry => decide (key entry = name))

/-- With unique keys, standard first removal equals the former remove-all filter.
Without uniqueness this replacement is false, as the executable control shows. -/
theorem eraseBinding_filter [DecidableEq Key] (key : Entry → Key) (name : Key)
    (entries : List Entry) (distinct : (entries.map key).Nodup) :
    eraseBinding key name entries = entries.filter (fun entry => decide (key entry ≠ name)) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    by_cases same : key entry = name
    · have absent : ∀ other ∈ rest, key other ≠ name := by
        intro other member equal
        apply distinct.1
        exact List.mem_map.mpr ⟨other, member, equal.trans same.symm⟩
      have retained : rest.filter (fun other => decide (key other ≠ name)) = rest :=
        List.filter_eq_self.mpr (by intro other member; simp [absent other member])
      simpa [eraseBinding, same] using retained.symm
    · simpa [eraseBinding, same] using congrArg (entry :: ·) (ih distinct.2)


/-- Move/insert a binding without changing any unrelated binding's payload/order. -/
def promoteBinding [DecidableEq Key] (key : Entry → Key) (entry : Entry) (entries : List Entry) : List Entry :=
  entry :: eraseBinding key (key entry) entries

/-- Distinct association keys remain distinct after a promotion or insertion. -/
theorem promoteBinding_distinct [DecidableEq Key] (key : Entry → Key) (entry : Entry)
    (entries : List Entry) (distinct : (entries.map key).Nodup) :
    ((promoteBinding key entry entries).map key).Nodup := by
  rw [promoteBinding, eraseBinding_filter key (key entry) entries distinct]
  apply List.nodup_cons.mpr
  constructor
  · intro member
    obtain ⟨other, retained, same⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp retained).2
    simp only [decide_eq_true_eq] at different
    exact different same
  · exact ((List.filter_sublist (p := fun other => decide (key other ≠ key entry))).map key).nodup distinct

/-- Evicting the suffix cannot introduce duplicate keys into the retained prefix. -/
theorem boundedPromotion_distinct [DecidableEq Key] (key : Entry → Key) (entry : Entry)
    (entries : List Entry) (capacity : Nat) (distinct : (entries.map key).Nodup) :
    (((promoteBinding key entry entries).take capacity).map key).Nodup :=
  ((List.take_sublist capacity (promoteBinding key entry entries)).map key).nodup
    (promoteBinding_distinct key entry entries distinct)

/-- The retained cache never exceeds its existing capacity. -/
theorem boundedPromotion_length [DecidableEq Key] (key : Entry → Key) (entry : Entry)
    (entries : List Entry) (capacity : Nat) :
    ((promoteBinding key entry entries).take capacity).length ≤ capacity := by
  simp only [List.length_take]
  exact Nat.min_le_left _ _
end LeanPoo.Functional.Parameters
