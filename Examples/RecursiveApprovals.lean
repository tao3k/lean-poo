import Examples.Support.RecursiveTopology
import LeanPoo.Functional.RecursiveApprovals

/-! Three entries jointly revise actual SCC graphs and shared approval metadata.
Guard stamps model complete registered versions, including ABA changes. Graph
installation and later entry effects remain separate sequential boundaries. -/
namespace LeanPoo.Examples.RecursiveApprovals
open Functional
abbrev Entry := Fin 3
abbrev Snapshot := RecursiveTopologies.Snapshot

/-- Immutable metadata token represents installed identity; guard versions are
separate. Local ceilings and the shared budget can have different outcomes. -/
structure Policy where
  token : Nat
  expected : Int
  budget : Int

abbrev Bundle := Functional.RecursiveApprovals.Bundle Snapshot Policy
abbrev World := RecursivePublication.World Bundle Entry Nat
abbrev Request := RecursiveStaging.Request Bundle Nat (Functional.RecursiveApprovals.Failure String String)
abbrev Evidence := (RecursiveTopologies.Node × Nat) × Nat × Nat

/-- Actual current refinement checks computed-reader links and all local ceilings. -/
def localAdmit (policy : Policy) (snapshot : Snapshot) : Bool :=
  (ObjectContract.diagnose (RecursiveTopologies.schema policy.expected) snapshot []).isEmpty &&
    decide ((snapshot.graph.payload 11).total ≤ 200)

/-- Joint budget approval is required even after all local checks succeed. -/
def admit (_old proposed : Policy) (snapshot : Snapshot) : Except String Unit :=
  if localAdmit proposed snapshot then
    if (snapshot.graph.payload 11).total ≤ proposed.budget then .ok () else .error "joint refusal"
  else .error "local refusal"

/-- Reuse selective closure inside one guarded whole-pair request, without building
anything during staging. New preparation always captures the actual shared round. -/
def prepare (world : World) (source : RecursiveTopologies.Source) (policy : Policy) (stamp : Nat) : Request :=
  Functional.RecursiveApprovals.stage world.graph stamp policy
    (fun old => RecursiveTopologies.step old source) admit

/-- Entry observation binds current root, metadata-derived descriptor token and
the exact local context. It returns only a proposed new effect context. -/
def effect (bundle : Bundle) (context : Nat) : Except String (Evidence × Nat) := do
  unless localAdmit bundle.metadata bundle.graph do throw "refine"
  let root := bundle.graph.graph.canonical 11
  let bound := RecursiveTopologies.Call.bindEvidence root bundle.metadata.token context (fun value => value)
  match bound.publish context
      (fun _ => (.ok ((root,bundle.metadata.token,context),context+1) : Except String (Evidence × Nat))) root with
  | (.ok result,next) => return (result,next)
  | (.error _,_) => throw "logic"

/-- Late policy refusal follows successful current refinement; it cannot undo the pair. -/
def refusing (bundle : Bundle) (_context : Nat) : Except String (Evidence × Nat) := do
  unless localAdmit bundle.metadata bundle.graph do throw "refine"
  throw "policy"

/-- Historical whole-pair attempts remain stale when old SCCs and names return. -/
def stale (request : Request) (world : World) : Bool :=
  match RecursiveStaging.publish request world.graph 2 with
  | (.error .stale,kept) => kept.revision == world.graph.revision &&
      kept.value.metadata.token == world.graph.value.metadata.token
  | _ => false

/-- Local success/joint failure keeps the predecessor. After proposed metadata
ABA, explicit restaging installs the pair, expires sibling entries and retries effects. -/
def round (state : World × List Request) (stage : Nat) : Except String (World × List Request) := do
  let (world,history) := state
  let source : RecursiveTopologies.Source := ⟨stage,false⟩
  let expected := RecursiveTopologies.reportTotal source
  let policy : Policy := ⟨world.graph.revision+1,expected,200⟩
  let pending := prepare world source policy 0
  let failed := prepare world source {policy with budget := expected-1} 0
  let entry : Entry := ⟨world.graph.revision%3,by omega⟩
  let other : Entry := ⟨(entry.val+1)%3,by omega⟩
  unless history.all (fun old => stale old world) do throw "historical request before retry"
  match RecursivePublication.submit failed world 0 entry effect with
  | (.error (.rejected (.approval "joint refusal")),kept) =>
    unless kept.graph.revision == world.graph.revision &&
        kept.graph.value.metadata.token == world.graph.value.metadata.token &&
        kept.graph.value.graph.graph.canonical 11 == world.graph.value.graph.graph.canonical 11 do
      throw "joint refusal changed pair"
  | _ => throw "joint refusal phase"
  unless stale pending world do throw "metadata ABA revived request"
  let retry := prepare world source policy 2
  let installed ← match RecursivePublication.submit retry world 2 entry refusing with
    | (.ok (.error "policy"),next) => pure next
    | _ => throw "late entry refusal"
  unless installed.graph.value.metadata.token == policy.token && installed.graph.value.metadata.budget == 200 &&
      (installed.graph.value.graph.graph.payload 11).total == expected do throw "mixed installed pair"
  unless (pending :: history).all (fun old => stale old installed) do throw "old entry request revived"
  unless !(RecursiveMigration.recognizes (RecursiveTopologies.names source) installed.graph.value.graph.epochs 11
      (world.graph.value.graph.graph.canonical 11)) do throw "old report revived"
  match RecursivePublication.observe installed entry effect with
  | (.ok _,next) =>
    unless next.contexts entry == world.contexts entry+1 && next.contexts other == world.contexts other do
      throw "entry context isolation"
    return (next,failed :: pending :: history)
  | _ => throw "entry effect retry"

/-- Eight graph rounds plus an approval-only revision reusing every canonical node.
Logical publication identity still advances, so all old whole-snapshot requests expire. -/
def test : Except String Unit := do
  let first ← RecursiveTopologies.initial
  let initial : World := ⟨⟨0,⟨first,⟨0,82,200⟩⟩⟩,fun entry => entry.val*100⟩
  let (last,_) ← [1,2,3,0,1,2,5,6].foldlM round (initial,[])
  unless ((List.finRange 3).map (fun entry => last.contexts entry - entry.val * 100)) == [3,3,2] do
    throw "entry counts"
  let nextPolicy := {last.graph.value.metadata with token := 9,budget := 999}
  let request := prepare last last.graph.value.graph.source nextPolicy 2
  let sibling := prepare last last.graph.value.graph.source last.graph.value.metadata 2
  match RecursiveStaging.publish request last.graph 2 with
  | (.ok (),next) =>
    unless next.revision == 9 && next.value.metadata.budget == 999 && next.value.graph.evaluated == [] &&
        next.value.graph.graph.canonical 11 == last.graph.value.graph.graph.canonical 11 do throw "metadata-only reuse"
    match RecursiveStaging.publish sibling next 2 with
    | (.error .stale,_) => pure ()
    | _ => throw "metadata-only commit revived sibling"
  | _ => throw "metadata-only joint revision"

#print axioms Functional.RecursiveApprovals.build_refused
#print axioms Functional.RecursiveApprovals.joint_refused
#print axioms Functional.RecursiveApprovals.joint_success
#print axioms Functional.RecursiveApprovals.refusal_preserves
#print axioms Functional.RecursiveApprovals.success_pair
#print axioms Functional.RecursiveApprovals.guard_refused
#print axioms Functional.RecursiveApprovals.prior_round_refused
#print axioms Functional.RecursiveApprovals.late_effect_refusal
#eval match test with
  | .ok () => IO.println "RECURSIVE-APPROVALS-OK"
  | .error cause => throw (IO.userError cause)
end LeanPoo.Examples.RecursiveApprovals
