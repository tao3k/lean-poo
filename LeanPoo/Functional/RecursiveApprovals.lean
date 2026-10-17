import LeanPoo.Functional.RecursivePublication

/-! Shared approval metadata and the recursive graph form one publication value.
Local reclosure and joint admission are pure here; Scheme installs the resulting
pair only after both gates pass. This advances generalized-prototype future work
under complete guards, identity correspondence and sequential callback premises. -/
namespace LeanPoo.Functional.RecursiveApprovals
open RecursiveStaging

/-- All entries project the graph and approvals from this one installed value. -/
structure Bundle (Graph Metadata : Type) where
  graph : Graph
  metadata : Metadata

/-- Construction and joint policy refusal remain distinct phases. -/
inductive Failure (GraphError ApprovalError : Type) where
  | graph (cause : GraphError)
  | approval (cause : ApprovalError)
  deriving BEq, DecidableEq, Repr

/-- Build one candidate using existing closure, then admit the complete proposed
graph/metadata pair. Neither refusal returns a partially published pair. -/
def revise (old : Bundle Graph Metadata) (proposed : Metadata)
    (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) :
    Except (Failure GraphError ApprovalError) (Bundle Graph Metadata) :=
  match build old.graph with
  | .error cause => .error (.graph cause)
  | .ok next => match admit old.metadata proposed next with
    | .error cause => .error (.approval cause)
    | .ok () => .ok ⟨next,proposed⟩

/-- Stage one whole-snapshot request with complete installed/proposed guard stamps. -/
def stage (current : State (Bundle Graph Metadata)) (stamp : Stamp) (proposed : Metadata)
    (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) :=
  RecursiveStaging.stage current stamp (fun old => revise old proposed build admit)

/-- Failed local closure never reaches the joint admission gate. -/
theorem build_refused (old : Bundle Graph Metadata) (proposed : Metadata)
    (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) (cause : GraphError)
    (failed : build old.graph = .error cause) :
    revise old proposed build admit = .error (.graph cause) := by simp [revise,failed]

/-- Local success cannot publish either projection when joint admission refuses. -/
theorem joint_refused (old : Bundle Graph Metadata) (proposed : Metadata)
    (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) (next : Graph) (cause : ApprovalError)
    (closed : build old.graph = .ok next) (failed : admit old.metadata proposed next = .error cause) :
    revise old proposed build admit = .error (.approval cause) := by simp [revise,closed,failed]

/-- One success contains the new graph and exactly its proposed shared metadata. -/
theorem joint_success (old : Bundle Graph Metadata) (proposed : Metadata)
    (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) (next : Graph)
    (closed : build old.graph = .ok next) (approved : admit old.metadata proposed next = .ok ()) :
    revise old proposed build admit = .ok ⟨next,proposed⟩ := by simp [revise,closed,approved]

/-- Joint refusal preserves the entire installed pair and its logical identity. -/
theorem refusal_preserves [DecidableEq Stamp] (current : State (Bundle Graph Metadata))
    (stamp : Stamp) (proposed : Metadata) (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) (cause : Failure GraphError ApprovalError)
    (failed : revise current.value proposed build admit = .error cause) :
    publish (stage current stamp proposed build admit) current stamp = (.error (.rejected cause),current) :=
  closure_failure current stamp _ cause failed

/-- Successful joint publication changes both projections in the same revision. -/
theorem success_pair [DecidableEq Stamp] (current : State (Bundle Graph Metadata))
    (stamp : Stamp) (proposed : Metadata) (build : Graph → Except GraphError Graph)
    (admit : Metadata → Metadata → Graph → Except ApprovalError Unit) (next : Graph)
    (closed : build current.value.graph = .ok next)
    (approved : admit current.value.metadata proposed next = .ok ()) :
    publish (stage current stamp proposed build admit) current stamp =
      (.ok (),⟨current.revision+1,⟨next,proposed⟩⟩) :=
  restaged_success current stamp _ _ (joint_success current.value proposed build admit next closed approved)

/-- Metadata drift rejects before either construction or admission is invoked. -/
theorem guard_refused [DecidableEq Stamp]
    (request : Request (Bundle Graph Metadata) Stamp Error) (current : State (Bundle Graph Metadata))
    (stamp : Stamp) (drift : request.stamp ≠ stamp) :
    publish request current stamp = (.error .stale,current) := stale_stamp request current stamp drift

/-- Even equal graph payloads cannot revive requests from an old metadata round. -/
theorem prior_round_refused [DecidableEq Stamp]
    (request sibling : Request (Bundle Graph Metadata) Stamp Error)
    (current next : State (Bundle Graph Metadata)) (stamp : Stamp)
    (observed : sibling.expected = current.revision)
    (installed : publish request current stamp = (.ok (),next)) :
    publish sibling next stamp = (.error .stale,next) :=
  RecursiveStaging.sibling_stale request sibling current next stamp observed installed

/-- Once the joint pair is installed, a later entry-effect refusal retains BOTH
new projections and all old contexts, reusing the shared-entry publication law. -/
theorem late_effect_refusal [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request (Bundle Graph Metadata) Stamp GraphError)
    (world : RecursivePublication.World (Bundle Graph Metadata) Entry Context)
    (stamp : Stamp) (entry : Entry)
    (effect : Bundle Graph Metadata → Context → Except Error (Result × Context))
    (next : State (Bundle Graph Metadata)) (cause : Error)
    (closed : publish request world.graph stamp = (.ok (),next))
    (refused : effect next.value (world.contexts entry) = .error cause) :
    RecursivePublication.submit request world stamp entry effect =
      (.ok (.error cause),{world with graph := next}) :=
  RecursivePublication.late_refusal request world stamp entry effect next cause closed refused

end LeanPoo.Functional.RecursiveApprovals
