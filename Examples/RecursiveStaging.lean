import Examples.Support.RecursiveTopology
import LeanPoo.Functional.RecursiveStaging

/-! The same seven actual graph states as the Scheme staged-request workflow.
Pure requests defer the existing reclosure; logical revisions correspond to exact
host graph identity, and stamps to complete watched versions. Graph installation
and subsequent bound-evidence effects are separate sequential boundaries. -/
namespace LeanPoo.Examples.RecursiveStaging
open Functional

abbrev Current := Functional.RecursiveStaging.State RecursiveTopologies.Snapshot
abbrev Request := Functional.RecursiveStaging.Request RecursiveTopologies.Snapshot Nat String

/-- Stage actual source changes without running closure or changing node epochs. -/
def request (current : Current) (source : RecursiveTopologies.Source) (stamp : Nat := 0) : Request :=
  Functional.RecursiveStaging.stage current stamp (fun old => RecursiveTopologies.step old source)

/-- Successful publication exposes the next graph; failures keep their own phase. -/
def commit (staged : Request) (current : Current) (stamp : Nat := 0) : Except String Current :=
  match Functional.RecursiveStaging.publish staged current stamp with
  | (.ok (),next) => .ok next
  | (.error .stale,_) => .error "stale"
  | (.error (.rejected cause),_) => .error cause

/-- An obsolete request returns the same current identity and canonical root. -/
def stale (staged : Request) (current : Current) (stamp : Nat := 0) : Bool :=
  match Functional.RecursiveStaging.publish staged current stamp with
  | (.error .stale,kept) => kept.revision == current.revision &&
      kept.value.graph.canonical 11 == current.value.graph.canonical 11
  | _ => false

/-- Refine the current checked root, refuse old context, then retry exact evidence. -/
def publishEvidence (current : Current) : Except String Unit := do
  let value := current.value
  unless (ObjectContract.diagnose (RecursiveTopologies.schema 135) value []).isEmpty do throw "refine"
  let root := value.graph.canonical 11
  let bound := RecursiveTopologies.Call.bindEvidence root 7 current.revision (fun evidence => evidence)
  let produce (context : Nat) (_ : RecursiveTopologies.Node × Nat) :
      Except String (((RecursiveTopologies.Node × Nat) × Nat × Nat) × Nat) :=
    .ok ((root,7,context),current.revision+1)
  match bound.publish current.revision (produce (current.revision-1)) root with
  | (.error .logic,kept) => unless kept == current.revision do throw "effect refusal state"
  | _ => throw "stale effect context"
  match bound.publish current.revision (produce current.revision) root with
  | (.ok _,next) => unless next == current.revision+1 do throw "effect retry state"
  | _ => throw "bound evidence retry"

/-- Interleaved requests span two simultaneous merges, splits, a refused crossed
merge/re-stage, restored SCCs, computed-only changes and one local pair revision. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let s0 : Current := ⟨0,first⟩
  let merge := request s0 ⟨1,false⟩
  let loser := request s0 ⟨5,false⟩
  let s1 ← commit merge s0
  unless (s1.value.graph.payload 11).total == 108 && stale loser s1 && stale merge s1 do throw "first competing round"
  let split := request s1 ⟨2,false⟩
  let mergedLoser := request s1 ⟨3,false⟩
  let s2 ← commit split s1
  unless (s2.value.graph.payload 11).total == 128 && stale mergedLoser s2 && stale loser s2 do throw "split competing round"
  let failed := request s2 ⟨3,true⟩
  let sibling := request s2 ⟨4,false⟩
  match Functional.RecursiveStaging.publish failed s2 0 with
  | (.error (.rejected "joint refusal"),kept) =>
    unless kept.revision == s2.revision && kept.value.graph.canonical 11 == s2.value.graph.canonical 11 do throw "failure changed snapshot"
  | _ => throw "failure phase"
  let s3 ← commit (request s2 ⟨3,false⟩) s2
  unless (s3.value.graph.payload 11).total == 132 && stale sibling s3 && stale failed s3 do throw "re-stage crossed merge"
  let s4 ← commit (request s3 ⟨4,false⟩) s3
  unless (s4.value.graph.payload 11).total == 127 && RecursiveTopologies.members s4.value.source 0 == RecursiveTopologies.members s0.value.source 0 &&
      stale loser s4 do throw "restored group revived request"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names s4.value.source) s4.value.epochs 11 (s0.value.graph.canonical 11)) do
    throw "old Reference revived"
  let computed := request s4 ⟨5,false⟩
  let obsolete := request s4 ⟨2,false⟩
  let s5 ← commit computed s4
  unless s5.value.evaluated == [10,11,13] && (s5.value.graph.payload 11).total == 134 && stale obsolete s5 do throw "computed footprint"
  let s6 ← commit (request s5 ⟨6,false⟩) s5
  unless s6.value.evaluated == [0,1,11,13] && (s6.value.graph.payload 11).total == 135 && stale loser s6 do throw "local SCC revision"
  unless s6.value.graph.canonical 12 == s0.value.graph.canonical 12 do throw "independent Reference lost"
  -- Watched-input drift rejects even without a competing graph replacement.
  let watched := request s6 ⟨6,false⟩ 9
  unless stale watched s6 10 do throw "watch drift"
  let refreshed ← commit (request s6 ⟨6,false⟩ 10) s6 10
  unless refreshed.value.evaluated == [] && refreshed.value.graph.canonical 11 == s6.value.graph.canonical 11 &&
      stale watched refreshed 10 do throw "clean nodes authorize old snapshot"
  publishEvidence s6

#print axioms Functional.RecursiveStaging.stale_revision
#print axioms Functional.RecursiveStaging.stale_stamp
#print axioms Functional.RecursiveStaging.closure_failure
#print axioms Functional.RecursiveStaging.restaged_success
#print axioms Functional.RecursiveStaging.success_revision
#print axioms Functional.RecursiveStaging.refusal_preserves
#print axioms Functional.RecursiveStaging.sibling_stale
#print axioms Functional.RecursiveStaging.older_round_stale
#eval match test with
  | .ok () => IO.println "RECURSIVE-STAGING-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveStaging
