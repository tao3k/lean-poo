import LeanPoo.Proof.Gerbil.SccOrdinalRows
import LeanPoo.Functional.OrderedReachability

namespace LeanPoo.Proof.Gerbil.SccPackedCapture

open SccOrdinalRows (Roster writeSymbolic)
open Functional.OrderedReachability (restoreRows restore_completed_prefix)

variable {Key : Type} {n : Nat}

/-- Decode the completed offset intervals. A suffix may already contain
some entries of the current, as yet uncommitted, row. -/
def decode (names : Fin n → Key) (widths : List Nat) (targets : List (Fin n)) : List (List Key) :=
  (restoreRows widths targets).map (List.map names)

theorem decode_completed (names : Fin n → Key) (accepted : List (List (Fin n)))
    (unfinished : List (Fin n)) :
    decode names (accepted.map List.length) (accepted.flatten ++ unfinished) =
      accepted.map (List.map names) := by
  rw [decode, restore_completed_prefix]

def symbolicRows (names : Fin n → Key) (rows : List (Fin n × List (Fin n))) :
    List (Fin n × List Key) :=
  rows.map (fun (owner, targets) => (owner, targets.map names))

/-- The prefix restored to the original adapter is exactly the committed
symbolic prefix. In particular, a changed write delegate sees all prior
rows, including empty ones, before it sees the current write. -/
theorem restore_before_delegate [DecidableEq Key] {State Error Result : Type}
    (roster : Roster Key n) (accepted : List (Fin n × List (Fin n)))
    (unfinished : List (Fin n))
    (adapter : Key → Option (List Key))
    (delegate : (Key → Option (List Key)) → State → Except Error Result × State)
    (state : State) :
    let targets := accepted.map Prod.snd
    delegate (writeSymbolic roster ((accepted.map Prod.fst).zip
      (decode roster.key (targets.map List.length) (targets.flatten ++ unfinished))) adapter) state =
      delegate (writeSymbolic roster (symbolicRows roster.key accepted) adapter) state := by
  dsimp only
  rw [decode_completed]
  have zipped :
      (accepted.map Prod.fst).zip ((accepted.map Prod.snd).map (List.map roster.key)) =
        symbolicRows roster.key accepted := by
    induction accepted with
    | nil => rfl
    | cons entry rest ih =>
      rcases entry with ⟨owner, row⟩
      simp [symbolicRows] at ih ⊢
      exact ih
  rw [zipped]

/-- A refusal at acquisition has no published symbolic row. Successful
publication commits one decoded spine per owner, once, before clients may
borrow a row or see the public table through a lookup failure. -/
theorem publication_exact {Error Event Result : Type}
    (roster : Roster Key n)
    (acquire : Except Error (List (List (Fin n))) × List Event)
    (publish : List (List Key) → Except Error Result) :
    (acquire.1 >>= fun accepted =>
      publish (decode roster.key (accepted.map List.length) accepted.flatten), acquire.2) =
    (acquire.1 >>= fun accepted => publish (accepted.map (List.map roster.key)), acquire.2) := by
  rcases acquire with ⟨result, trace⟩
  cases result with
  | error error => rfl
  | ok accepted =>
    change (publish (decode roster.key (accepted.map List.length) accepted.flatten), trace) =
      (publish (accepted.map (List.map roster.key)), trace)
    simpa only [List.append_nil] using congrArg (fun rows => (publish rows, trace))
      (decode_completed roster.key accepted [])

#print axioms decode_completed
#print axioms restore_before_delegate
#print axioms publication_exact

end LeanPoo.Proof.Gerbil.SccPackedCapture
