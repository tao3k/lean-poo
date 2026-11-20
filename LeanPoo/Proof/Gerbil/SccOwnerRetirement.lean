import LeanPoo.Proof.Gerbil.SccOrdinalRows

namespace LeanPoo.Proof.Gerbil.SccOwnerRetirement

open SccOrdinalRows (Roster store)

variable {Key Adapter : Type} {n : Nat} [DecidableEq Key]

/-- A singleton owner is its own representative. Borrow its identity from
the already admitted roster, including ordinal zero. -/
def lookup (roster : Roster Key n) (key : Key) : Option Key :=
  (roster.position key).map roster.key

omit [DecidableEq Key] in
theorem present_exact (roster : Roster Key n) (key : Key) (ordinal : Fin n)
    (found : roster.position key = some ordinal) :
    lookup roster key = some key := by
  have same := (roster.exact key ordinal).mp found
  simp [lookup, found, same]

def fill (keys : List Key) (table : Key → Option Key) : Key → Option Key :=
  keys.foldl (fun table key => store table key key) table

theorem fill_query (keys : List Key) (table : Key → Option Key) (key : Key) :
    fill keys table key = if key ∈ keys then some key else table key := by
  induction keys generalizing table with
  | nil => simp [fill]
  | cons first rest ih =>
    change fill rest (store table first first) key = _
    rw [ih]
    by_cases member : key ∈ rest
    · simp [member]
    · by_cases same : first = key
      · subst first
        simp [member, store]
      · simp [member, store, same, Ne.symm same]

/-- Recreate the original hash entries by inserting in roster order. The
public missing-key exception may expose this populated adapter. -/
theorem fill_exact (roster : Roster Key n) :
    fill ((List.finRange n).map roster.key) (fun _ => none) = lookup roster := by
  funext key
  rw [fill_query]
  cases h : roster.position key with
  | none =>
    have absent : key ∉ (List.finRange n).map roster.key := by
      intro member
      obtain ⟨ordinal, _, same⟩ := List.mem_map.mp member
      have present := (roster.exact key ordinal).mpr same
      rw [h] at present
      contradiction
    simp [lookup, h, absent]
  | some ordinal =>
    have same := (roster.exact key ordinal).mp h
    have present : key ∈ (List.finRange n).map roster.key :=
      List.mem_map.mpr ⟨ordinal, List.mem_finRange ordinal, same⟩
    simp [present, present_exact roster key ordinal h]

/-- First miss or a foreign read route installs the complete table before
calling the delegate. The delegate receives the original adapter token and
may change the table. Later reads use that changed table. -/
theorem retire_before_delegate {State Error Result : Type}
    (roster : Roster Key n) (adapter : Adapter)
    (delegate : Adapter → (Key → Option Key) → State → Except Error Result × State) (state : State) :
    delegate adapter (fill ((List.finRange n).map roster.key) (fun _ => none)) state =
      delegate adapter (lookup roster) state := by
  rw [fill_exact]

theorem update_after_retirement (roster : Roster Key n) (key representative : Key) :
    store (fill ((List.finRange n).map roster.key) (fun _ => none)) key representative =
      store (lookup roster) key representative := by
  rw [fill_exact]

#print axioms fill_exact
#print axioms retire_before_delegate
#print axioms update_after_retirement

end LeanPoo.Proof.Gerbil.SccOwnerRetirement
