import Examples.Support.RecursiveTopology
import LeanPoo.Functional.RecursiveApprovals

/-! Shared checked service and approval fixture for actual SCC graph workflows.
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

end LeanPoo.Examples.RecursiveApprovals
