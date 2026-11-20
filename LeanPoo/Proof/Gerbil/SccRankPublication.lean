import LeanPoo.Proof.Gerbil.SccAdmittedRoster
import LeanPoo.Proof.Gerbil.SccRankGroups

namespace LeanPoo.Proof.Gerbil.SccRankPublication

open SccOrdinalRows (Roster)
open SccAdmittedRoster (lookup_exact rebuilt)
open SccRankGroups (group_members_exact representative_exact)

variable {Key : Type} {n : Nat} [DecidableEq Key]

/-- Keep the solver's rank at each admitted position. Build the final member
lists directly. The first member of each list serves as representative. -/
def groups (rank : Fin n → Nat) (wanted : Nat) : List (Fin n) :=
  (List.finRange n).reverse.foldl (SccRankGroups.push rank wanted) []

def representative (roster : Roster Key n) (rank : Fin n → Nat) (key : Key) : Option Key :=
  (roster.position key).bind (fun ordinal =>
    ((groups rank (rank ordinal)).head?).map roster.key)

def oldRepresentative (roster : Roster Key n) (rank : Fin n → Nat)
    (key : Key) : Option Key :=
  (rebuilt roster key).bind (fun ordinal =>
    ((List.finRange n).find? (fun i => decide (rank i = rank ordinal))).map roster.key)

theorem representative_exact_at (roster : Roster Key n) (rank : Fin n → Nat)
    (key : Key) :
    representative roster rank key = oldRepresentative roster rank key := by
  simp only [representative, oldRepresentative, lookup_exact, groups,
    representative_exact]

/-- A single roster table answers both the strict owner lookup and the
optional group lookup. A foreign key is still missing in both views. -/
theorem unknown_key_absent (roster : Roster Key n) (rank : Fin n → Nat)
    (key : Key) (missing : roster.position key = none) :
    representative roster rank key = none ∧ oldRepresentative roster rank key = none := by
  rw [← representative_exact_at]
  simp [representative, missing]

omit [DecidableEq Key] in
theorem member_order_exact (roster : Roster Key n) (rank : Fin n → Nat) (wanted : Nat) :
    (groups rank wanted).map roster.key =
      ((List.finRange n).foldl (SccRankGroups.push rank wanted) []).reverse.map roster.key := by
  unfold groups
  rw [group_members_exact]

omit [DecidableEq Key] in
/-- The cardinality is saved from the normalized group at publication.
Mutating the publicly returned list cannot change this saved value. -/
theorem stored_cardinality_exact (roster : Roster Key n) (rank : Fin n → Nat) (wanted : Nat) :
    ((groups rank wanted).map roster.key).length =
      ((List.finRange n).foldl (SccRankGroups.push rank wanted) []).length := by
  rw [member_order_exact]
  simp

/-- Run the same independent checker over the recorded rows, and share its
result with publication. A checker may refuse at the first bad edge or group.
The rank projection cannot move, catch, or change that refusal. -/
theorem certification_exact {Row Error Result : Type} (roster : Roster Key n)
    (rank : Fin n → Nat) (rows : Key → Row)
    (certify : (Key → Option Key) → (Key → Row) → Except Error Result) :
    certify (representative roster rank) rows = certify (oldRepresentative roster rank) rows := by
  rw [show representative roster rank = oldRepresentative roster rank from
    funext (representative_exact_at roster rank)]

/-- Delay materializing the shared, mutable owner table until independent
certification succeeds. Publication still gives all public lookup routes
the same table, including an unbound-key error's hash payload. -/
theorem finish_exact {Row Error Certificate Table : Type}
    (roster : Roster Key n) (rank : Fin n → Nat) (rows : Key → Row)
    (certify : (Key → Option Key) → (Key → Row) → Except Error Certificate)
    (makeTable : (Key → Option Key) → Certificate → Table) :
    (certify (representative roster rank) rows).map (makeTable (representative roster rank)) =
      (certify (oldRepresentative roster rank) rows).map (makeTable (oldRepresentative roster rank)) := by
  rw [show representative roster rank = oldRepresentative roster rank from
    funext (representative_exact_at roster rank)]

/-- Once emitted, reflective edits see the materialized owner table. A
per-lookup rank projection cannot provide this mutability contract. -/
theorem reflected_update_exact (roster : Roster Key n) (rank : Fin n → Nat)
    (key : Key) (replacement : Key) (query : Key) :
    SccOrdinalRows.store (representative roster rank) key replacement query =
      SccOrdinalRows.store (oldRepresentative roster rank) key replacement query := by
  rw [show representative roster rank = oldRepresentative roster rank from
    funext (representative_exact_at roster rank)]

/-- Avoid the temporary rank write and rank read per owner. Both successful
paths still write each final public owner entry exactly once. -/
theorem owner_table_accesses (owners : Nat) :
    (owners + owners + owners) - owners = 2 * owners := by omega

#print axioms representative_exact_at
#print axioms member_order_exact
#print axioms certification_exact
#print axioms finish_exact
#print axioms reflected_update_exact

end LeanPoo.Proof.Gerbil.SccRankPublication
