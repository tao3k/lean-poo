import Examples.Support.RecursiveTopology
import LeanPoo.Functional.RecursiveRestaging

/-! Eight actual graph revisions with pending old requests across preparation,
late admission refusal, explicit retry and refinement/bound-evidence publication.
Logical identities/stamps and sequential pure callbacks are model premises. -/
namespace LeanPoo.Examples.RecursiveRestaging
open Functional
abbrev Current := RecursiveStaging.State RecursiveTopologies.Snapshot
abbrev Request := RecursiveStaging.Request RecursiveTopologies.Snapshot Nat String

/-- Return the existing selective reclosure action after inspecting current support.
No graph construction occurs until the returned guarded request is published. -/
def prepare (source : RecursiveTopologies.Source) (old : RecursiveTopologies.Snapshot) :
    Except String (RecursiveTopologies.Snapshot → Except String RecursiveTopologies.Snapshot) :=
  if (RecursiveTopologies.names old.source).contains 11 then
    .ok (fun current => RecursiveTopologies.step current source)
  else .error "missing report"

/-- A stale attempt returns the current snapshot identity and canonical report. -/
def stale (request : Request) (current : Current) : Bool :=
  match RecursiveStaging.publish request current 0 with
  | (.error .stale,kept) => kept.revision == current.revision &&
      kept.value.graph.canonical 11 == current.value.graph.canonical 11
  | _ => false

/-- Current refinement and exact evidence compose after graph installation.
Wrong context refuses without changing effect state; fresh exact evidence retries. -/
def evidence (current : Current) : Except String Unit := do
  let snapshot := current.value
  unless (ObjectContract.diagnose
    (RecursiveTopologies.schema (RecursiveTopologies.reportTotal snapshot.source)) snapshot []).isEmpty do
    throw "refine"
  let root := snapshot.graph.canonical 11
  let bound := RecursiveTopologies.Call.bindEvidence root 7 current.revision (fun value => value)
  let produce (context : Nat) (_ : RecursiveTopologies.Node × Nat) :
      Except String (((RecursiveTopologies.Node × Nat) × Nat × Nat) × Nat) :=
    .ok ((root,7,context),current.revision+1)
  match bound.publish current.revision (produce (current.revision-1)) root with
  | (.error .logic,kept) => unless kept == current.revision do throw "effect refusal changed state"
  | _ => throw "old context accepted"
  match bound.publish current.revision (produce current.revision) root with
  | (.ok _,next) => unless next == current.revision+1 do throw "effect retry state"
  | _ => throw "effect retry refused"

/-- Prepare while older work waits, fail closure, re-prepare and interleave attempts.
Provider removal/reintroduction and restored SCCs must not revive old references. -/
def round (state : Current × List Request) (stage : Nat) :
    Except String (Current × List Request) := do
  let (current,history) := state
  let source : RecursiveTopologies.Source := ⟨stage,false⟩
  let fresh ← RecursiveRestaging.restage current 0 (prepare source)
  let failed ← RecursiveRestaging.restage current 0 (prepare ⟨stage,true⟩)
  unless history.all (fun old => stale old current) do throw "older request survived before retry"
  match RecursiveStaging.publish failed current 0 with
  | (.error (.rejected "joint refusal"),kept) =>
    unless kept.revision == current.revision &&
      kept.value.graph.canonical 11 == current.value.graph.canonical 11 do throw "closure refusal changed state"
  | _ => throw "closure refusal phase"
  let retry ← RecursiveRestaging.restage current 0 (prepare source)
  let next ← match RecursiveStaging.publish retry current 0 with
    | (.ok (),next) => pure next
    | _ => throw "fresh retry refused"
  unless (next.value.graph.payload 11).total == RecursiveTopologies.reportTotal source do throw "report"
  unless history.all (fun old => stale old next) && stale fresh next && stale failed next do
    throw "old request revived after retry"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source) next.value.epochs 11
      (current.value.graph.canonical 11)) do throw "old report revived"
  unless next.value.graph.canonical 12 == current.value.graph.canonical 12 do throw "idle rebuilt"
  evidence next
  return (next,fresh :: failed :: history)

/-- Same eight catalogs as Gerbil: return to primary-only support, reintroduce the
secondary provider, split SCCs again, then change computed readers and local bodies. -/
def test : Except String Unit := do
  let initial ← RecursiveTopologies.initial
  let (last,history) ← [1,2,3,0,1,2,5,6].foldlM round (⟨0,initial⟩,[])
  unless last.revision == 8 && history.length == 16 && (last.value.graph.payload 11).total == 135 do
    throw "round count"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names last.value.source) last.value.epochs 11
      (initial.graph.canonical 11)) do throw "historical report revived"

#print axioms Functional.RecursiveRestaging.preparation_failure
#print axioms Functional.RecursiveRestaging.prepared_request
#print axioms Functional.RecursiveRestaging.prepared_publish
#print axioms Functional.RecursiveRestaging.refused_then_retry
#print axioms Functional.RecursiveRestaging.obsolete_attempts
#print axioms Functional.RecursiveRestaging.interleaved_publish
#eval match test with
  | .ok () => IO.println "RECURSIVE-RESTAGING-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveRestaging
