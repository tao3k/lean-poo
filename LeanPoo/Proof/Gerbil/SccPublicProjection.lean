import LeanPoo.Proof.Gerbil.SccOrdinalRows

namespace LeanPoo.Proof.Gerbil.SccPublicProjection

open SccOrdinalRows (Roster store writeSymbolic capture_commutes)

variable {Key Row Group : Type} {n : Nat}

def projected (decode : Fin n → Row) (cells : Fin n → Option Row) (owner : Fin n) : Row :=
  (cells owner).getD (decode owner)

/-- An empty dependency list is a present value. Read requests fill a cell
only when it is absent, then retain that row's identity. -/
def demand (decode : Fin n → Row) (cells : Fin n → Option Row) (owner : Fin n) :
    Row × (Fin n → Option Row) :=
  match cells owner with
  | some row => (row, cells)
  | none => let row := decode owner; (row, store cells owner row)

theorem demand_same_view (decode : Fin n → Row) (cells : Fin n → Option Row)
    (owner : Fin n) :
    (demand decode cells owner).1 = projected decode cells owner ∧
    projected decode (demand decode cells owner).2 = projected decode cells := by
  cases h : cells owner with
  | some row => simp [demand, projected, h]
  | none =>
    constructor
    · simp [demand, projected, h]
    · funext query
      by_cases same : owner = query
      · subst query
        simp [demand, projected, h, store]
      · simp [demand, projected, h, store, same]

theorem repeated_read_reuses_row (decode : Fin n → Row) (cells : Fin n → Option Row)
    (owner : Fin n) :
    (demand decode (demand decode cells owner).2 owner).1 =
    (demand decode cells owner).1 := by
  rw [(demand_same_view decode (demand decode cells owner).2 owner).1,
    (demand_same_view decode cells owner).2, (demand_same_view decode cells owner).1]

/-- A changed adapter receives the same complete table whether any subset
of its rows was demanded before retirement or all rows were still packed. -/
theorem retire_after_demand [DecidableEq Key]
    (roster : Roster Key n) (decode : Fin n → Row) (cells : Fin n → Option Row)
    (owner : Fin n) (ordered : List (Fin n)) (table : Key → Option Row) :
    writeSymbolic roster (ordered.map (fun pos => (pos, projected decode (demand decode cells owner).2 pos))) table =
    writeSymbolic roster (ordered.map (fun pos => (pos, projected decode cells pos))) table := by
  rw [(demand_same_view decode cells owner).2]

/-- Enumerating all groups after any individual demand produces the same
ordered group objects. The public group spine and member lookup share this
selection, even if an ordinary adapter has since been edited. -/
theorem ordered_view_after_demand (decode : Fin n → Group)
    (cells : Fin n → Option Group) (owner : Fin n) (ordered : List (Fin n)) :
    ordered.map (projected decode (demand decode cells owner).2) =
      ordered.map (projected decode cells) := by
  rw [(demand_same_view decode cells owner).2]

def memberEntry (group : Group) : Nat × Group := (1, group)

theorem group_identity_and_size_exact (groups : List Group) :
    (groups.map memberEntry).map Prod.snd = groups ∧
    (groups.map memberEntry).map Prod.fst = groups.map (fun _ => (1 : Nat)) := by
  induction groups with
  | nil => simp
  | cons group rest ih => simp [memberEntry, ih]

/-- The stock member vector stores group tokens alone. The ordinary table
regains its cardinality pair before any foreign delegate can read or edit it. -/
theorem member_retirement_exact [DecidableEq Key] (roster : Roster Key n)
    (ordered : List (Fin n × Group)) (cells : Fin n → Option (Nat × Group)) :
    let entries := ordered.map (fun item => (item.1, memberEntry item.2))
    SccOrdinalRows.read roster (SccOrdinalRows.writeCells entries cells) =
      writeSymbolic roster entries (SccOrdinalRows.read roster cells) :=
  capture_commutes roster _ cells

/-- Use the publication's existing symbolic table for already demanded
tokens. A cold point read inserts at most the requested owner. -/
def sparseDemand [DecidableEq Key] (roster : Roster Key n)
    (decode : Fin n → Row) (table : Key → Option Row) (owner : Fin n) :
    Row × (Key → Option Row) :=
  match table (roster.key owner) with
  | some row => (row, table)
  | none => let row := decode owner; (row, store table (roster.key owner) row)

theorem sparse_demand_commutes [DecidableEq Key] (roster : Roster Key n)
    (decode : Fin n → Row) (cells : Fin n → Option Row) (owner : Fin n) :
    sparseDemand roster decode (SccOrdinalRows.read roster cells) owner =
      let (row, next) := demand decode cells owner
      (row, SccOrdinalRows.read roster next) := by
  have atOwner : SccOrdinalRows.read roster cells (roster.key owner) = cells owner := by
    simp [SccOrdinalRows.read, (roster.exact _ owner).mpr rfl]
  cases before : cells owner <;>
    simp [sparseDemand, atOwner, demand, before, SccOrdinalRows.store_commutes]

/-- After any finite sequence of point demands, a key absent from the
requested owners has exactly its previous entry. Dense initialization is
unnecessary even when the admitted roster is much larger than the requests. -/
theorem sparse_untouched [DecidableEq Key] (roster : Roster Key n)
    (decode : Fin n → Row) (requested : List (Fin n)) (table : Key → Option Row)
    (key : Key) (unrequested : key ∉ requested.map roster.key) :
    (requested.foldl (fun state owner => (sparseDemand roster decode state owner).2) table) key =
      table key := by
  induction requested generalizing table with
  | nil => rfl
  | cons owner rest ih =>
    have different : roster.key owner ≠ key := fun same =>
      unrequested (List.mem_cons.mpr (.inl same.symm))
    have notLater : key ∉ rest.map roster.key :=
      fun h => unrequested (List.mem_cons_of_mem _ h)
    simp only [List.foldl_cons]
    rw [ih _ notLater]
    cases hit : table (roster.key owner) <;> simp [sparseDemand, hit, store, different]

#print axioms sparse_demand_commutes
#print axioms sparse_untouched

#print axioms repeated_read_reuses_row
#print axioms retire_after_demand
#print axioms member_retirement_exact
#print axioms ordered_view_after_demand

end LeanPoo.Proof.Gerbil.SccPublicProjection
