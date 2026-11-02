import LeanPoo.Functional.RecursiveRecovery

/-! Named incarnation fences compose with existing checked recursive publication.
All transitions are serialized. Complete staging guards, identity correspondence,
immutable-in-use metadata and pure terminating callbacks remain premises. This
extends generalized MOP future work, not distributed leases or concurrent CAS. -/
namespace LeanPoo.Functional.RecursiveCoordination
open RecursiveStaging RecursivePublication RecursiveCompetition

/-- A coordinator identity includes a strictly increasing per-name incarnation. -/
structure Lease (Name : Type) where
  name : Name
  generation : Nat

/-- Names share one whole publication but retain independent incarnation state. -/
structure Fleet (Name Graph Entry Context : Type) where
  world : World Graph Entry Context
  generation : Name → Nat
  live : Name → Bool

/-- Open only an inactive name; recovery allocates a fresh generation. -/
def start [DecidableEq Name] (state : Fleet Name Graph Entry Context) (name : Name) :
    Option (Lease Name × Fleet Name Graph Entry Context) :=
  if state.live name then none else
    let generation := state.generation name + 1
    some (⟨name,generation⟩,{state with
      generation := fun key => if key = name then generation else state.generation key
      live := fun key => if key = name then true else state.live key})

/-- Late cleanup affects only the exact incarnation that exited. -/
def stop [DecidableEq Name] (state : Fleet Name Graph Entry Context) (lease : Lease Name) :=
  if state.generation lease.name = lease.generation then
    {state with live := fun key => if key = lease.name then false else state.live key}
  else state

/-- Fence before running an existing staged request; graph/effect phases are reused. -/
def attempt [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (item : Submission Graph Stamp GraphError Entry Context Error Result) :
    Except (Failure GraphError) (Except Error Result) × Fleet Name Graph Entry Context :=
  if state.live lease.name ∧ state.generation lease.name = lease.generation then
    let (result,next) := submit item.request state.world item.stamp item.entry item.effect
    (result,{state with world := next})
  else (.error .stale,state)

/-- Explicit lifecycle and attempt events may interleave across any finite names. -/
inductive Event (Name Graph Stamp GraphError Entry Context Error Result : Type) where
  | start (name : Name)
  | stop (lease : Lease Name)
  | attempt (lease : Lease Name) (item : Submission Graph Stamp GraphError Entry Context Error Result)

/-- Run one event, retaining the current state when an already-live start refuses. -/
def step [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context)
    (event : Event Name Graph Stamp GraphError Entry Context Error Result) :=
  match event with
  | .start name => match start state name with | none => state | some (_,next) => next
  | .stop lease => stop state lease
  | .attempt lease item => (attempt state lease item).2

/-- A finite lifecycle trace never implicitly prepares or renews a request. -/
def run [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Name Graph Stamp GraphError Entry Context Error Result))
    (state : Fleet Name Graph Entry Context) := events.foldl step state

/-- A live name cannot be replaced while its scope still owns requests. -/
theorem start_busy [DecidableEq Name] (state : Fleet Name Graph Entry Context) (name : Name)
    (busy : state.live name = true) : start state name = none := by simp [start,busy]

/-- Recovery changes only this name's incarnation and liveness, never installation. -/
theorem start_idle [DecidableEq Name] (state : Fleet Name Graph Entry Context) (name : Name)
    (idle : state.live name = false) :
    start state name = some (⟨name,state.generation name+1⟩,{state with
      generation := fun key => if key = name then state.generation name+1 else state.generation key
      live := fun key => if key = name then true else state.live key}) := by simp [start,idle]

/-- Failure cleanup cannot undo an installed prefix. -/
theorem stop_world [DecidableEq Name] (state : Fleet Name Graph Entry Context) (lease : Lease Name) :
    (stop state lease).world = state.world := by unfold stop; split <;> rfl

/-- One coordinator's exit does not change any other name's liveness. -/
theorem stop_other [DecidableEq Name] (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (other : Name) (different : other ≠ lease.name) : (stop state lease).live other = state.live other := by
  unfold stop; split <;> simp [different]

/-- An old cleanup arriving after replacement cannot close the replacement. -/
theorem old_stop [DecidableEq Name] (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (different : state.generation lease.name ≠ lease.generation) : stop state lease = state := by
  simp [stop,different]

/-- Exit fences retained requests even when the graph and approval stamp are unchanged. -/
theorem closed_refused [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (item : Submission Graph Stamp GraphError Entry Context Error Result)
    (closed : state.live lease.name = false) : attempt state lease item = (.error .stale,state) := by
  simp [attempt,closed]

/-- A new same-name incarnation never reactivates an older request. -/
theorem generation_refused [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (item : Submission Graph Stamp GraphError Entry Context Error Result)
    (different : state.generation lease.name ≠ lease.generation) : attempt state lease item = (.error .stale,state) := by
  simp [attempt,different]

/-- Every event keeps all per-name generation counters monotone. -/
theorem step_generation_monotone [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context)
    (event : Event Name Graph Stamp GraphError Entry Context Error Result) (name : Name) :
    state.generation name ≤ (step state event).generation name := by
  cases event with
  | start who =>
    change state.generation name ≤ (match start state who with | none => state | some (_,next) => next).generation name
    by_cases live : state.live who = true
    · simp [start,live]
    · have idle : state.live who = false := by cases h : state.live who <;> simp_all
      rw [start_idle state who idle]
      dsimp
      split <;> simp_all
  | stop lease =>
    change state.generation name ≤ (stop state lease).generation name
    unfold stop
    split <;> exact Nat.le_refl _
  | attempt lease item =>
    change state.generation name ≤ (attempt state lease item).2.generation name
    unfold attempt
    split
    · cases h : submit item.request state.world item.stamp item.entry item.effect
      simp
    · exact Nat.le_refl _

/-- Any finite mixture of failures/rejoins keeps every name's old generations old. -/
theorem run_generation_monotone [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Name Graph Stamp GraphError Entry Context Error Result))
    (state : Fleet Name Graph Entry Context) (name : Name) :
    state.generation name ≤ (run events state).generation name := by
  induction events generalizing state with
  | nil => exact Nat.le_refl _
  | cons event rest ih => exact Nat.le_trans (step_generation_monotone state event name) (ih (step state event))

/-- Lifecycle events and refused attempts cannot lower the installed graph revision. -/
theorem step_revision_monotone [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (state : Fleet Name Graph Entry Context)
    (event : Event Name Graph Stamp GraphError Entry Context Error Result) :
    state.world.graph.revision ≤ (step state event).world.graph.revision := by
  cases event with
  | start name =>
    change state.world.graph.revision ≤ (match start state name with | none => state | some (_,next) => next).world.graph.revision
    by_cases live : state.live name = true
    · simp [start,live]
    · have idle : state.live name = false := by cases h : state.live name <;> simp_all
      rw [start_idle state name idle]
      exact Nat.le_refl _
  | stop lease =>
    change state.world.graph.revision ≤ (stop state lease).world.graph.revision
    rw [stop_world]
    exact Nat.le_refl _
  | attempt lease item =>
    change state.world.graph.revision ≤ (attempt state lease item).2.world.graph.revision
    unfold attempt
    split
    · cases h : submit item.request state.world item.stamp item.entry item.effect with
      | mk result next =>
        have bound := submit_revision_monotone item state.world
        simpa [h] using bound
    · exact Nat.le_refl _

/-- Successful prefixes survive arbitrary subsequent finite lifecycle traces. -/
theorem run_revision_monotone [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Name Graph Stamp GraphError Entry Context Error Result))
    (state : Fleet Name Graph Entry Context) :
    state.world.graph.revision ≤ (run events state).world.graph.revision := by
  induction events generalizing state with
  | nil => exact Nat.le_refl _
  | cons event rest ih => exact Nat.le_trans (step_revision_monotone state event) (ih (step state event))

/-- Once superseded, an incarnation stays refused through all later lifecycle and
publication interleavings, independently of topology/metadata value round trips. -/
theorem historical_refused [DecidableEq Name] [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Name Graph Stamp GraphError Entry Context Error Result))
    (state : Fleet Name Graph Entry Context) (lease : Lease Name)
    (item : Submission Graph Stamp GraphError Entry Context Error Result)
    (older : lease.generation < state.generation lease.name) :
    attempt (run events state) lease item = (.error .stale,run events state) := by
  apply generation_refused
  have monotone := run_generation_monotone events state lease.name
  omega

end LeanPoo.Functional.RecursiveCoordination
