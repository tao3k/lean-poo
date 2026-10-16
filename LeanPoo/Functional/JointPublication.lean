import LeanPoo.Functional.ComponentPublication

/-! One authoritative bundle carries heterogeneous endpoint heads and approvals.
Atomicity is modeled by selecting the whole bundle, not updating projections. -/
namespace LeanPoo.Functional.JointPublication
variable {Id Endpoint Policy : Type} {Head : Endpoint → Type} {Metadata : Policy → Type} [DecidableEq Id]
/-- Dependent fields permit different endpoint contracts and policy types. -/
structure Bundle (Id Endpoint Policy : Type) (Head : Endpoint → Type) (Metadata : Policy → Type) where
  id : Id
  heads : (key : Endpoint) → Head key
  approvals : (key : Policy) → Metadata key
/-- Reuse the serialized head decision; successful joint approval selects one
complete candidate, refusal/staleness selects the complete current bundle. -/
def install (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata) (approved : Bool) :=
  if (ComponentPublication.install expected current.id candidate.id approved).accepted then candidate else current
/-- No execution produces mixed old/new approval and endpoint projections. -/
theorem whole (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata) (approved : Bool) :
    install expected current candidate approved = candidate ∨ install expected current candidate approved = current := by
  unfold install; split <;> simp
/-- Any final joint refusal preserves ALL current metadata and heads together. -/
theorem refused (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata) :
    install expected current candidate false = current := by simp [install,ComponentPublication.refused]
/-- A rival installed during preparation wins; late candidates change no field. -/
theorem stale (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata)
    (approved : Bool) (different : current.id ≠ expected) : install expected current candidate approved = current := by
  simp [install,ComponentPublication.stale expected current.id candidate.id approved different]
/-- Current expected identity plus true complete joint approval installs EVERY
endpoint and approval field from the same candidate bundle. -/
theorem commit (current candidate : Bundle Id Endpoint Policy Head Metadata) :
    install current.id current candidate true = candidate := by simp [install,ComponentPublication.install]
/-- Joint validity is preserved if both current and admitted candidate are valid.
Constructors/residual checks and complete approval establish the premise separately. -/
theorem valid (expected : Id) (current candidate : Bundle Id Endpoint Policy Head Metadata) (approved : Bool)
    (Valid : Bundle Id Endpoint Policy Head Metadata → Prop) (old : Valid current)
    (checked : approved = true → Valid candidate) : Valid (install expected current candidate approved) := by
  unfold install
  split
  · rename_i accepted
    exact checked (ComponentPublication.accepted expected current.id candidate.id approved accepted).2.2
  · exact old
/-- Arbitrarily many requests prepared against one old bundle remain stale through
all later submissions. Approval flags and equal-valued round trips cannot revive it. -/
theorem stale_batch (expected : Id) (current : Bundle Id Endpoint Policy Head Metadata)
    (requests : List (Bundle Id Endpoint Policy Head Metadata × Bool)) (different : current.id ≠ expected) :
    requests.foldl (fun state request => install expected state request.1 request.2) current = current := by
  induction requests generalizing current with
  | nil => rfl
  | cons request rest ih =>
    simp only [List.foldl_cons, stale expected current request.1 request.2 different]
    exact ih current different
/-- One explicit prepared request, including its expected whole-snapshot identity. -/
structure Request (Id Endpoint Policy : Type) (Head : Endpoint → Type) (Metadata : Policy → Type) where
  expected : Id
  candidate : Bundle Id Endpoint Policy Head Metadata
  approved : Bool
/-- Serialized competing submissions each apply the existing whole-bundle rule. -/
def run (current : Bundle Id Endpoint Policy Head Metadata)
    (requests : List (Request Id Endpoint Policy Head Metadata)) : Bundle Id Endpoint Policy Head Metadata :=
  requests.foldl (fun state request => install request.expected state request.candidate request.approved) current
/-- Joint validity persists across every finite interleaving, assuming actual
construction and admission validate each submitted candidate when approved. -/
theorem run_valid (current : Bundle Id Endpoint Policy Head Metadata)
    (requests : List (Request Id Endpoint Policy Head Metadata))
    (Valid : Bundle Id Endpoint Policy Head Metadata → Prop) (old : Valid current)
    (checked : ∀ request ∈ requests, request.approved = true → Valid request.candidate) :
    Valid (run current requests) := by
  induction requests generalizing current with
  | nil => exact old
  | cons request rest ih =>
    apply ih (install request.expected current request.candidate request.approved)
    · exact valid request.expected current request.candidate request.approved Valid old
        (checked request (by simp))
    · intro next member
      exact checked next (by simp [member])
end LeanPoo.Functional.JointPublication
