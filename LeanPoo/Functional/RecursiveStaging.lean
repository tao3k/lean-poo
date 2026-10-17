import LeanPoo.Functional.RecursiveTopology

/-! Deferred recursive revisions. A monotone logical revision stands for the exact
Scheme graph identity; stamps stand for complete registered input versions. These
are correspondence premises, not runtime serialization. The action is pure here;
host callbacks must obey the existing sequential/no-hidden-effects discipline.
This advances generalized MOP future work and provides no concurrent CAS law. -/
namespace LeanPoo.Functional.RecursiveStaging

/-- Installed snapshot identity is independent of surviving node References. -/
structure State (Value : Type) where
  revision : Nat
  value : Value

/-- A request retains its observed identity, watched versions and deferred action. -/
structure Request (Value Stamp Error : Type) where
  expected : Nat
  stamp : Stamp
  action : Value → Except Error Value

/-- Snapshot mismatch and actual closure refusal remain distinct failure phases. -/
inductive Failure (Error : Type) where
  | stale
  | rejected (cause : Error)
  deriving BEq, DecidableEq, Repr

/-- Staging records intent only; it does not evaluate the requested reclosure. -/
def stage (current : State Value) (stamp : Stamp) (action : Value → Except Error Value) :
    Request Value Stamp Error := ⟨current.revision,stamp,action⟩

/-- Guard before construction. Successful closure alone advances identity; refusal
returns the exact current state. Refinement/effect publication is a later boundary. -/
def publish [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current : State Value) (stamp : Stamp) : Except (Failure Error) Unit × State Value :=
  if request.expected = current.revision ∧ request.stamp = stamp then
    match request.action current.value with
    | .error cause => (.error (.rejected cause),current)
    | .ok next => (.ok (),⟨current.revision+1,next⟩)
  else (.error .stale,current)

/-- A competing revision refuses without inspecting or invoking the action. -/
theorem stale_revision [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current : State Value) (stamp : Stamp) (different : request.expected ≠ current.revision) :
    publish request current stamp = (.error .stale,current) := by simp [publish,different]

/-- Proposed inputs may drift even when no graph has yet been replaced. -/
theorem stale_stamp [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current : State Value) (stamp : Stamp) (different : request.stamp ≠ stamp) :
    publish request current stamp = (.error .stale,current) := by simp [publish,different]

/-- Failed all-node admission neither publishes nor changes the snapshot. -/
theorem closure_failure [DecidableEq Stamp] (current : State Value) (stamp : Stamp)
    (action : Value → Except Error Value) (cause : Error) (failed : action current.value = .error cause) :
    publish (stage current stamp action) current stamp = (.error (.rejected cause),current) := by
  simp [publish,stage,failed]

/-- Re-staging against the actual current state admits a successful fresh action. -/
theorem restaged_success [DecidableEq Stamp] (current : State Value) (stamp : Stamp)
    (action : Value → Except Error Value) (next : Value) (good : action current.value = .ok next) :
    publish (stage current stamp action) current stamp = (.ok (),⟨current.revision+1,next⟩) := by
  simp [publish,stage,good]

/-- Every successful publication advances the identity exactly once. -/
theorem success_revision [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current next : State Value) (stamp : Stamp) (good : publish request current stamp = (.ok (),next)) :
    next.revision = current.revision+1 := by
  unfold publish at good
  split at good
  · cases result : request.action current.value <;> simp [result] at good
    subst next; rfl
  · simp at good

/-- Any refusal returns the original state, including its cached payloads. -/
theorem refusal_preserves [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current next : State Value) (stamp : Stamp) (cause : Failure Error)
    (failed : publish request current stamp = (.error cause,next)) : next = current := by
  unfold publish at failed
  split at failed
  · cases result : request.action current.value <;> simp [result] at failed
    exact failed.2.symm
  · exact (Prod.mk.inj failed).2.symm

/-- A successful sibling makes all requests from that observed round stale. -/
theorem sibling_stale [DecidableEq Stamp] (request sibling : Request Value Stamp Error)
    (current next : State Value) (stamp : Stamp) (observed : sibling.expected = current.revision)
    (good : publish request current stamp = (.ok (),next)) :
    publish sibling next stamp = (.error .stale,next) := by
  apply stale_revision
  have advanced := success_revision request current next stamp good
  omega

/-- Logical revisions cannot revive a request just because SCC groups return. -/
theorem older_round_stale [DecidableEq Stamp] (request : Request Value Stamp Error)
    (current : State Value) (stamp : Stamp) (older : request.expected < current.revision) :
    publish request current stamp = (.error .stale,current) :=
  stale_revision request current stamp (by omega)

end LeanPoo.Functional.RecursiveStaging
