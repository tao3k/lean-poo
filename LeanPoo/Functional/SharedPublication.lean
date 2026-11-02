import LeanPoo.Functional.ComponentPublication

/-! Several independently published endpoints observe shared approval revisions.
A common native lock realizes serialization; these laws model only its decisions. -/
namespace LeanPoo.Functional.ComponentPublication
variable {Endpoint Snapshot Revision : Type} [DecidableEq Endpoint] [DecidableEq Snapshot] [DecidableEq Revision]
/-- One endpoint installation changes only that endpoint's authoritative head.
The captured/live revision can describe shared plus endpoint-local approvals. -/
def installEntry (heads : Endpoint → Snapshot) (endpoint : Endpoint) (expected candidate : Snapshot)
    (staged live : Revision) (approved : Bool) : Endpoint → Snapshot :=
  fun query => if query = endpoint then (installChecked expected (heads endpoint) candidate staged live approved).head
    else heads query
/-- Independent endpoint heads are preserved even if a sibling installs successfully. -/
theorem entry_frame (heads : Endpoint → Snapshot) (endpoint query : Endpoint) (expected candidate : Snapshot)
    (staged live : Revision) (approved : Bool) (other : query ≠ endpoint) :
    installEntry heads endpoint expected candidate staged live approved query = heads query := by
  simp [installEntry,other]
/-- Drift of any observed shared revision prevents an endpoint changing ANY head. -/
theorem entry_stale (heads : Endpoint → Snapshot) (endpoint : Endpoint) (expected candidate : Snapshot)
    (staged live : Revision) (approved : Bool) (drift : staged ≠ live) :
    installEntry heads endpoint expected candidate staged live approved = heads := by
  funext query
  by_cases same : query = endpoint
  · subst query; simp [installEntry,metadata_stale expected (heads endpoint) candidate staged live approved drift]
  · simp [installEntry,same]
/-- Gather exactly registered shared/local approval revisions, in declaration order.
No hidden metadata dependency is inferred from arbitrary approval callbacks. -/
def observed {Policy Version : Type} (policies : List Policy) (versions : Policy → Version) : List Version :=
  policies.map versions
/-- Any changed registered policy changes the complete observed revision vector,
even when several endpoints share only part of their approval dependencies. -/
theorem observed_changed {Policy Version : Type} (policies : List Policy)
    (old live : Policy → Version) (policy : Policy) (member : policy ∈ policies) (changed : old policy ≠ live policy) :
    observed policies old ≠ observed policies live := by
  intro equal
  have equalAt := List.map_inj_left.mp equal
  exact changed (equalAt policy member)
/-- Unchanged registered dependencies preserve the captured revision vector.
A sibling's unrelated local policy may change without invalidating this request. -/
theorem observed_frame {Policy Version : Type} (policies : List Policy)
    (old live : Policy → Version) (unchanged : ∀ policy ∈ policies, old policy = live policy) :
    observed policies old = observed policies live := List.map_inj_left.mpr unchanged
/-- Shared dependency drift propagates to every observing endpoint through its
existing captured guard vector; no global invalidation epoch is introduced. -/
theorem shared_observer_stale {Policy Version : Type} [DecidableEq Version]
    (heads : Endpoint → Snapshot) (endpoint : Endpoint) (expected candidate : Snapshot)
    (policies : List Policy) (old live : Policy → Version) (policy : Policy)
    (member : policy ∈ policies) (changed : old policy ≠ live policy) (approved : Bool) :
    installEntry heads endpoint expected candidate (observed policies old) (observed policies live) approved = heads :=
  entry_stale heads endpoint expected candidate _ _ approved (observed_changed policies old live policy member changed)
end LeanPoo.Functional.ComponentPublication
