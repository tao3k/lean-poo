-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Functional.LocalSccRegion

/-!
A plan owns only the pure calculation at one boundary. A source node points
to its dependent owner. A published owner uniquely identifies a stage of an
admitted generic and C4 shape. The observed part always runs against the live
world, and can edit the world before the next plan lookup.
-/
namespace LeanPoo.Object.ClosAdmission.PublishedDispatch
open LeanPoo.Functional.StrongComponents (Reach)
open LeanPoo.Functional.LocalSccRegion (Edge)

def Affected {n : Nat} (union : Edge n) (dirty : Fin n → Prop) (owner : Fin n) : Prop :=
  ∃ source, dirty source ∧ Reach union source owner

structure World (n : Nat) (Value Runtime : Type) where
  input : Fin n → Value
  epoch : Fin n → Nat
  state : Runtime

structure Published (n : Nat) (Recipe : Type) where
  owner : Fin n
  epoch : Nat
  plan : Recipe

structure Outcome (State Event Failure : Type) where
  world : State
  result : Except Failure Unit
  events : List Event

structure Stage (n : Nat) (Value Runtime Recipe Event Failure : Type) where
  owner : Fin n
  support : List (Fin n)
  prepare : List Value → Recipe
  perform : Recipe → World n Value Runtime → Outcome (World n Value Runtime) Event Failure

def cold (stage : Stage n Value Runtime Recipe Event Failure) (world : World n Value Runtime) : Recipe :=
  stage.prepare (stage.support.map world.input)

def current (stage : Stage n Value Runtime Recipe Event Failure) (world : World n Value Runtime)
    (entry : Published n Recipe) : Prop :=
  entry.owner = stage.owner ∧ entry.epoch = world.epoch stage.owner

def publish (stage : Stage n Value Runtime Recipe Event Failure) (world : World n Value Runtime) :
    Published n Recipe :=
  ⟨stage.owner, world.epoch stage.owner, cold stage world⟩

/-- Epochs are the executable guard. The graph and the changed-source
contract explain why the guard can be used without reading the support. -/
noncomputable def advanceEpoch {n : Nat} (union : Edge n) (dirty : Fin n → Prop)
    (epoch : Fin n → Nat) (owner : Fin n) : Nat :=
  @ite Nat (Affected union dirty owner) (Classical.propDecidable _)
    (epoch owner + 1) (epoch owner)

theorem affected_cannot_keep_epoch {n : Nat} (union : Edge n) (dirty : Fin n → Prop)
    (epoch : Fin n → Nat) (owner : Fin n) (affected : Affected union dirty owner) :
    advanceEpoch union dirty epoch owner ≠ epoch owner := by
  classical
  simp [advanceEpoch, affected]

/-- A retained owner's support is unchanged. Graph transport requires a
conservative union of old and admitted new edges and dirt for every
changed input, including an owner whose stage or dependency roster changes. -/
theorem support_unchanged {n : Nat} {union : Edge n} {dirty : Fin n → Prop}
    {before after : Fin n → Value} {owner : Fin n} {support : List (Fin n)}
    (registered : ∀ source ∈ support, Reach union source owner)
    (inputs : ∀ source, ¬ dirty source → after source = before source)
    (retained : ¬ Affected union dirty owner) :
    support.map after = support.map before := by
  apply List.map_congr_left
  intro source present
  exact inputs source (fun changed => retained ⟨source, changed, registered source present⟩)

/-- The invariant is inductive over edits. A receipt may predate the
previous snapshot, but a previously issued epoch cannot be in the future. -/
theorem prior_entry_valid_after_edit {n : Nat} {union : Edge n} {dirty : Fin n → Prop}
    (stage : Stage n Value Runtime Recipe Event Failure) (before after : World n Value Runtime)
    (entry : Published n Recipe)
    (past : entry.epoch ≤ before.epoch stage.owner)
    (valid : current stage before entry → entry.plan = cold stage before)
    (registered : ∀ source ∈ stage.support, Reach union source stage.owner)
    (inputs : ∀ source, ¬ dirty source → after.input source = before.input source)
    (advanced : after.epoch = advanceEpoch union dirty before.epoch)
    (hit : current stage after entry) :
    entry.plan = cold stage after := by
  classical
  have retained : ¬ Affected union dirty stage.owner := by
    intro affected
    have future : entry.epoch = before.epoch stage.owner + 1 := by
      simpa [advanced, advanceEpoch, affected] using hit.2
    omega
  have prior : current stage before entry :=
    ⟨hit.1, by simpa [advanced, advanceEpoch, retained] using hit.2⟩
  calc
    entry.plan = cold stage before := valid prior
    _ = cold stage after := congrArg stage.prepare (support_unchanged registered inputs retained).symm

/-- A lookup uses one owner epoch. The separate cost component counts calls
to the pure preparation function and ignores observations and callbacks. -/
def choose (stage : Stage n Value Runtime Recipe Event Failure) (world : World n Value Runtime)
    (entry : Option (Published n Recipe)) : Recipe × Nat :=
  match entry with
  | none => (cold stage world, 1)
  | some entry =>
    if entry.owner = stage.owner ∧ entry.epoch = world.epoch stage.owner then (entry.plan, 0)
    else (cold stage world, 1)

theorem hit_skips_preparation (stage : Stage n Value Runtime Recipe Event Failure)
    (world : World n Value Runtime) (entry : Published n Recipe) (hit : current stage world entry) :
    choose stage world (some entry) = (entry.plan, 0) := by
  simp [choose, current] at hit ⊢
  simp [hit.1, hit.2]

theorem stale_prepares_at_current_boundary (stage : Stage n Value Runtime Recipe Event Failure)
    (world : World n Value Runtime) (entry : Published n Recipe) (stale : ¬ current stage world entry) :
    choose stage world (some entry) = (cold stage world, 1) := by
  simp only [current] at stale
  simp [choose, stale]

theorem choose_plan_eq_cold (stage : Stage n Value Runtime Recipe Event Failure)
    (world : World n Value Runtime) (entry : Option (Published n Recipe))
    (valid : ∀ saved, entry = some saved → current stage world saved → saved.plan = cold stage world) :
    (choose stage world entry).1 = cold stage world := by
  cases entry with
  | none => rfl
  | some saved =>
    by_cases hit : current stage world saved
    · rw [hit_skips_preparation _ _ _ hit]
      exact valid saved rfl hit
    · rw [stale_prepares_at_current_boundary _ _ _ hit]

/-- A stage's dynamic action is executed exactly once. A failed epoch check
uses the cold preparation at this stage, with the state left by any earlier
callback. Even on failure the trace contains the already-observed prefix. -/
def run (select : Stage n Value Runtime Recipe Event Failure → World n Value Runtime → Recipe)
    (stages : List (Stage n Value Runtime Recipe Event Failure)) (world : World n Value Runtime) :
    Outcome (World n Value Runtime) Event Failure :=
  match stages with
  | [] => ⟨world, .ok (), []⟩
  | stage :: rest =>
    let observed := stage.perform (select stage world) world
    match observed.result with
    | .error _ => observed
    | .ok () =>
      let next := run select rest observed.world
      { next with events := observed.events ++ next.events }

theorem run_eq_cold
    (read : Stage n Value Runtime Recipe Event Failure → World n Value Runtime → Option (Published n Recipe))
    (stages : List (Stage n Value Runtime Recipe Event Failure)) (world : World n Value Runtime)
    (valid : ∀ stage ∈ stages, ∀ w saved, read stage w = some saved →
      current stage w saved → saved.plan = cold stage w) :
    run (fun stage w => (choose stage w (read stage w)).1) stages world =
      run cold stages world := by
  induction stages generalizing world with
  | nil => rfl
  | cons stage rest ih =>
    have selected := choose_plan_eq_cold stage world (read stage world) (valid stage (by simp) world)
    have restValid : ∀ step ∈ rest, ∀ w saved, read step w = some saved →
        current step w saved → saved.plan = cold step w :=
      fun step present => valid step (List.mem_cons_of_mem _ present)
    simp only [run, selected]
    generalize stage.perform (cold stage world) world = observed
    cases observed.result with
    | error cause => rfl
    | ok value => rw [ih observed.world restValid]

/-- Dependency reachability governs invalidation even when a DAG edit leaves
every SCC unchanged. The SCC theorem governs rebuilding component membership. -/
theorem acyclic_dependency_invalidates {n : Nat} {union : Edge n} {dirty : Fin n → Prop}
    {source owner : Fin n} (changed : dirty source)
    (dependency : Reach union source owner) :
    Affected union dirty owner := ⟨source, changed, dependency⟩


private abbrev DemoStage := Stage 2 Nat Unit Nat Nat String

private def demoWorld (revision value : Nat) : World 2 Nat Unit :=
  ⟨fun key => if key = 0 then value else 0,
   fun owner => if owner = 1 then revision else 0, ()⟩

private def editBeforeNextStage : DemoStage where
  owner := 0
  support := []
  prepare := fun _ => 0
  perform := fun _ _ => ⟨demoWorld 1 7, .ok (), [1]⟩

private def byCurrentValue : DemoStage where
  owner := 1
  support := [0]
  prepare := fun values => values.headD 0
  perform := fun value world =>
    ⟨world, if value = 7 then .error "refused" else .ok (), [value]⟩

private def demoStart := demoWorld 0 3
private def demoStages := [editBeforeNextStage, byCurrentValue, editBeforeNextStage]

private def guardedDemo :=
  run (fun stage w => (choose stage w (some (publish stage demoStart))).1)
    demoStages demoStart

private def uncheckedDemo :=
  run (fun stage _ => (publish stage demoStart).plan) demoStages demoStart

-- The callback runs once and the later stage uses the newly published facts.
-- The rejection keeps the earlier event and stops the trailing stage.
#guard guardedDemo.events == [1, 7]
#guard (match guardedDemo.result with
  | .error failure => failure == "refused"
  | .ok _ => false)
#guard (run cold demoStages demoStart).events == guardedDemo.events
#guard uncheckedDemo.events == [1, 3, 1]
#guard (choose byCurrentValue demoStart (some (publish byCurrentValue demoStart))).2 == 0
#guard (choose byCurrentValue demoStart (some (publish editBeforeNextStage demoStart))).2 == 1

end LeanPoo.Object.ClosAdmission.PublishedDispatch
