import LeanPoo.Examples.JointReceipts

/-! Multiple admitted receipts, shared revision drift and six topology rounds.
Actual sources and closure equations stay inside every candidate head. -/
namespace LeanPoo.Examples.JointReceipts
open Functional.GeneralizedGraph LeanPoo.Examples.ComponentRounds LeanPoo.Examples.JointTopology
/-- Two receipts share an obsolete revision while an independent approved sibling
stays current. All older rounds are replayed after that sibling wins. -/
def round (state : State × List Attempt) (row : Nat × Head × Nat × Nat) : Except String (State × List Attempt) := do
  let (current,history) := state
  let (id,head,ceiling,budget) := row
  let candidate : State := ⟨id,fun _ => head,fun _ => (ceiling,budget)⟩
  let first ← certify current.id candidate (id*10)
  let second ← certify current.id candidate (id*10)
  let independent ← certify current.id candidate (id*10+1)
  let attempts : List Attempt := [⟨first,id*10+1⟩,⟨independent,id*10+1⟩,⟨second,id*10+1⟩,⟨first,id*10+1⟩]
  let winner := Functional.JointPublication.installSequence current (attempts ++ history)
  unless winner.id == id && winner.approvals 0 == (ceiling,budget) do
    throw "drift consumed independent sibling or old receipt overwrote winner"
  pure (winner,history ++ attempts)
/-- Reuse actual merge/delete/split/restore declarations for two full cycles.
Equal-valued support and approval round trips never revive old snapshot identities. -/
def check : Except String Unit := do
  let .ok compact := close source | throw "compact closure refused"
  let .ok merge := SupportRevision.join source (contributions .merge) | throw "merge refused"
  let .ok merged := close merge.apply | throw "merge closure refused"
  let .ok split := SupportRevision.join merge.apply (contributions .replace) | throw "split refused"
  let .ok replaced := close split.apply | throw "split closure refused"
  let .ok restore := SupportRevision.join split.apply (contributions .restore) | throw "restore refused"
  let .ok restored := close restore.apply | throw "restored closure refused"
  let initial : State := ⟨0,fun _ => compact,fun _ => (12,24)⟩
  let rows := [(1,merged,24,48),(2,replaced,16,32),(3,restored,12,24),
               (4,merged,24,48),(5,replaced,16,32),(6,restored,12,24)]
  let result : Except String (State × List Attempt) :=
    rows.foldl (fun prior row => prior.bind (fun state => round state row)) (.ok (initial,[]))
  let .ok (final,history) := result | throw "receipt trace refused"
  let replay := Functional.JointPublication.installSequence final history
  unless replay.id == 6 && (replay.heads 0).graph.members 7 == [] && replay.approvals 0 == (12,24) do
    throw "cross-round replay revived deleted components or old approvals"
#eval match check with
  | .ok () => IO.println "JOINT-RECEIPTS-OK"
  | .error message => throw (IO.userError message)
#print axioms Functional.JointPublication.installSequence_valid
#print axioms Functional.JointPublication.installSequence_stale
#print axioms Functional.JointPublication.installSequence_drift_between
end LeanPoo.Examples.JointReceipts
