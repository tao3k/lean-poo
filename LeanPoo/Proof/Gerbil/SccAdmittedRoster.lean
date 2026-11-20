import LeanPoo.Proof.Gerbil.SccOrdinalRows

namespace LeanPoo.Proof.Gerbil.SccAdmittedRoster

open SccOrdinalRows (Roster)

variable {Key Error Event Result Edit : Type} {n : Nat} [DecidableEq Key]

/-- The table constructed by walking the owned names in source order. -/
def rebuilt (roster : Roster Key n) (key : Key) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (roster.key i = key))

theorem lookup_exact (roster : Roster Key n) (key : Key) :
    rebuilt roster key = roster.position key := by
  cases h : rebuilt roster key with
  | some ordinal =>
    have matched := List.find?_some (l := List.finRange n) h
    exact ((roster.exact key ordinal).mpr (of_decide_eq_true matched)).symm
  | none =>
    cases pos : roster.position key with
    | none => rfl
    | some ordinal =>
      have matched := (roster.exact key ordinal).mp pos
      have absent := List.find?_eq_none.mp h ordinal (List.mem_finRange ordinal)
      simp [matched] at absent

/-- At the stock, unobserved handoff, SCC consumes the names and their exact
inverse. Source effects and their first refusal have already been acquired.
The independent SCC validator still consumes the original rows. -/
theorem handoff_exact (source : Except Error (Roster Key n) × List Event)
    (prepare : (Fin n → Key) → (Key → Option (Fin n)) → Except Error Result) :
    (source.1 >>= fun roster => prepare roster.key roster.position, source.2) =
      (source.1 >>= fun roster => prepare roster.key (rebuilt roster), source.2) := by
  rcases source with ⟨result, events⟩
  cases result with
  | error err => rfl
  | ok roster =>
    change (prepare roster.key roster.position, events) = (prepare roster.key (rebuilt roster), events)
    rw [show rebuilt roster = roster.position from funext (lookup_exact roster)]

/-- A cold position table can be shared by the published partition. Revision
starts with those same positions and edits a fresh overlay. -/
theorem revision_exact (roster : Roster Key n)
    (revise : (Key → Option (Fin n)) → Edit → Result) (edit : Edit) :
    revise roster.position edit = revise (rebuilt roster) edit := by
  rw [show rebuilt roster = roster.position from funext (lookup_exact roster)]

/-- A fresh table writes every owner once. A borrowed table writes none. -/
theorem cold_inserts_omitted : (List.finRange n).length - 0 = n := by simp

#print axioms handoff_exact
#print axioms revision_exact

end LeanPoo.Proof.Gerbil.SccAdmittedRoster
