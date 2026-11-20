import LeanPoo.Proof.Gerbil.SccOrdinalRows
import LeanPoo.Proof.Gerbil.SccSingletonProjection

namespace LeanPoo.Proof.Gerbil.SccPackedSingletons

open SccOrdinalRows (Roster read writeCells writeSymbolic capture_commutes)
open SccSingletonProjection (Arc rank firstBad backward)

variable {Key Group : Type} {n : Nat}

/-- The certificate checks the captured edges independently of direction
selection. It needs no separate rank map. Self edges are accepted. -/
def badOrdinal (forward : Bool) (arc : Arc n) : Bool :=
  decide (if forward then arc.2.val < arc.1.val else arc.1.val < arc.2.val)

theorem ordinal_predicate_exact (forward : Bool) (arc : Arc n) :
    badOrdinal forward arc = backward (rank forward) arc := by
  rcases arc with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  cases forward <;> apply Bool.eq_iff_iff.mpr <;> simp [badOrdinal, backward, rank] <;> omega

theorem reject_first_exact (forward : Bool) (arcs : List (Arc n)) :
    arcs.find? (badOrdinal forward) = firstBad (rank forward) arcs := by
  unfold firstBad
  rw [show badOrdinal forward = backward (rank forward) from funext (ordinal_predicate_exact forward)]

/-- The one published group object is shared by the ordered group list
and member lookup. Retiring the ordinal representation copies the same
identity into the original adapter, including its stored cardinality. -/
def memberRows (entries : List (Fin n × Group)) : List (Fin n × (Nat × Group)) :=
  entries.map (fun (owner, group) => (owner, 1, group))

theorem members_and_retirement_exact [DecidableEq Key] (roster : Roster Key n)
    (entries : List (Fin n × Group)) (cells : Fin n → Option (Nat × Group)) :
    read roster (writeCells (memberRows entries) cells) =
      writeSymbolic roster (memberRows entries) (read roster cells) :=
  capture_commutes roster (memberRows entries) cells

/-- The ordinary refusal is complete before a partition, its group spines,
or its owner hash can become observable. -/
theorem publish_after_certificate {Error Snapshot : Type} (forward : Bool)
    (arcs : List (Arc n)) (error : Arc n → Error) (publish : Unit → Snapshot) :
    (match arcs.find? (badOrdinal forward) with
     | some arc => Except.error (error arc)
     | none => Except.ok (publish ())) =
    (match firstBad (rank forward) arcs with
     | some arc => Except.error (error arc)
     | none => Except.ok (publish ())) := by
  rw [reject_first_exact]

#print axioms reject_first_exact
#print axioms members_and_retirement_exact

end LeanPoo.Proof.Gerbil.SccPackedSingletons
