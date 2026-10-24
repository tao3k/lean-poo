import LeanPoo.Functional.FeedbackCache
import LeanPoo.Prototype.CappedFeedback

/-! Shared dependency invalidation across whole feedback groups. Existing DAG
materialization really skips a refusing independent builder; approval stays fresh. -/
namespace LeanPoo.Examples.CachedFeedback
open Functional Functional.GeneralizedGraph Functional.ConstructionCache
open Prototype.Generalized
/-- The cache stores complete typed closures and all component residual proofs. -/
abbrev Group := FeedbackCache.Group CappedFeedback.parts CappedFeedback.cook CappedFeedback.base
/-- An input node and feedback groups share one explicitly typed graph value. -/
inductive Value where
  | input (quota : Nat)
  | group (value : Group)
/-- Uniform sum storage keeps quota/group distinction explicit at graph boundaries. -/
abbrev Values := fun _ : String => Value
/-- Dirty-group construction uses the same bounded capped-ring algorithm as native. -/
def build (quota : Nat) : Outcome String Values "left" :=
  match FeedbackCache.closeGroup CappedFeedback.parts CappedFeedback.cook CappedFeedback.base quota CappedFeedback.base (quota+2) with
  | .error message => .error (.source message)
  | .ok group => .ok (.group group)
/-- The first reader depends directly on the shared quota input. -/
def leftCode : Code String Values "left" := .need "quota" fun _ result => do
  match ← result with
  | .input quota => build quota
  | .group _ => .error (.source "quota input required")
/-- A cross-group reader depends on both shared quota and the first closed group. -/
def rightCode : Code String Values "right" :=
  .both (.need "quota" fun _ value => value) (.need "left" fun _ value => value) fun _ quota left => do
    match ← quota, ← left with
    | .input n, .group group => build (1 + max n group.result.closed.raw.1.1)
    | _, _ => .error (.source "quota and closed left group required")
/-- The independent feedback group has no shared-input or sibling dependencies. -/
def stableCode : Code String Values "stable" := .pure fun _ => build 2
/-- Immutable code identities are shared by all revisions; only quota base changes. -/
def source (quota : Nat) : Declaration String Values where
  keys := ["quota","left","right","stable"]
  code := fun key => if key = "left" then some leftCode else if key = "right" then some rightCode
    else if key = "stable" then some stableCode else none
  base := fun key => if key = "quota" then some (.ok (.input quota)) else none
/-- Observe an actual cooked method from a required successful group slot. -/
def charge (state : State String Values) (key : String) : Except String Nat :=
  match state key with
  | some (.ok (.group group)) => group.result.closed.interface.charge 2
  | _ => .error "required closed group unavailable"
/-- Joint commitment reads every required group; error/missing values refuse. -/
def commitment (state : State String Values) : Option Nat := do
  let some (.ok (.group left)) := state "left" | none
  let some (.ok (.group right)) := state "right" | none
  let some (.ok (.group stable)) := state "stable" | none
  return 3 * (left.input + right.input + stable.input)
/-- Current permission and cross-group limit are checked AFTER materialization. -/
def approved {spec : Declaration String Values} (allowed : Bool) (limit : Nat) (cache : Cache spec) : Bool :=
  allowed && match commitment cache.closed.raw with | some total => decide (total ≤ limit) | none => false
/-- Execute existing scheduling/cache refresh with a builder that REFUSES stable.
The selective result must also match a fresh reconstruction's actual observations. -/
def check : Except String Unit := do
  let .ok scheduled := (source 3).schedule | throw "initial schedule refused"
  let .ok old := ConstructionCache.start scheduled (Builder.guarded _ (fun _ => true)) | throw "initial cache refused"
  let next : Declaration String Values := (source 3).setBase "quota" (some (.ok (.input 4)))
  let nextSchedule : Scheduled next := scheduled.rebase (by intro key; rfl) (by intro key; exact scheduled.known key)
  let changed := fun key : String => decide (key = "quota")
  have unchanged : ∀ key, changed key = false → ∀ self, next.resolve key self = (source 3).resolve key self := by
    intro key clean self
    exact Declaration.setBase_resolve_frame _ "quota" key _ (Ne.symm (of_decide_eq_false clean)) self
  let .ok candidate := refresh nextSchedule old changed unchanged
    (Builder.guarded next (fun key => key != "stable")) | throw "retained builder unexpectedly ran"
  unless candidate.evaluated == ["quota","left","right"] && candidate.reused == ["stable"] do
    throw "wrong reconstruction footprint"
  let .ok fresh := ConstructionCache.start nextSchedule (Builder.guarded _ (fun _ => true)) | throw "fresh control refused"
  for key in ["left","right","stable"] do
    unless (← charge candidate.closed.raw key) == (← charge fresh.closed.raw key) do throw "reference observation differs"
  unless (← charge old.closed.raw "left") == 36 && (← charge candidate.closed.raw "left") == 48 do
    throw "old/new group closure observations"
  match FeedbackCache.admitCache candidate (approved true 27) with
  | .ok _ => throw "overcommitted family admitted"
  | .error _ => pure ()
  let .ok _ := FeedbackCache.admitCache candidate (approved true 33) | throw "valid joint commitment refused"
  let retained := candidate.retain nextSchedule.order
  unless retained.evaluated == [] do throw "retained cache reconstructed"
  match FeedbackCache.admitCache retained (approved false 33) with
  | .ok _ => throw "old permission was reused"
  | .error _ => pure ()
#eval match check with
  | .error message => throw (IO.userError message)
  | .ok () => IO.println "CACHED-FEEDBACK-OK shared-invalidation retained-builder-skipped fresh-reference joint-approval"
#print axioms FeedbackCache.Group.fixed
#print axioms FeedbackCache.closeGroup_bound
#print axioms FeedbackCache.shared_invalidates
#print axioms FeedbackCache.retained_slot
#print axioms FeedbackCache.admitCache_approved
#print axioms Partial.step_reused_builder_independent
end LeanPoo.Examples.CachedFeedback
