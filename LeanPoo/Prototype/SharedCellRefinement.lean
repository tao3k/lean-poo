import LeanPoo.Prototype.SharedThunkHeap

/-! Sequential primitive refinement for the source-owned shared constructor.
The primitive rules model the pinned Lean runtime's reference value and thunk
closure/value slots. Closure return and completed get are separate: a return
observation does not yet establish native cache publication. Native events are
untrusted data. No theorem unfolds opaque IO primitives or verifies C++/RC. -/
namespace LeanPoo.Prototype.Recursive.Shared.CellRefinement

open SharedCell

/-- Source pin for the runtime rules, not an axiom about installed machine code. -/
def runtimeRevision : String := "293d5d0c0c3f3dded4688b3ccd6a33939ac5102b"

inductive Stage where
  | empty | bottom | cell | self | result | linked | running | returned | ready
  deriving Repr, BEq, DecidableEq

inductive SelfSlot where
  | cold | running | returned | ready
  deriving Repr, BEq, DecidableEq

/-- One private reference and its result/self thunk slots. `returned` retains
the body result until a completed get witnesses cache publication. -/
structure State where
  stage : Stage := .empty
  target : Target := .unavailable
  selfSlot : SelfSlot := .cold
  loaded : Bool := false
  builds : Nat := 0
  reads : Nat := 0
  cellReads : Nat := 0
  deriving Repr, BEq, DecidableEq

def installed (stage : Stage) : Bool :=
  match stage with
  | .linked | .running | .returned | .ready => true
  | _ => false

/-- A completed sequential primitive transition. `none` means that the
operation has no completed transition, including a busy thunk's wait branch.
It does not claim that the native primitive raises an error. -/
def step (state : State) (event : Event) : Option State :=
  match event with
  | .mkUnavailable =>
    if state.stage = .empty then some { state with stage := .bottom } else none
  | .mkRef =>
    if state.stage = .bottom then some { state with stage := .cell } else none
  | .mkSelf =>
    if state.stage = .cell then some { state with stage := .self } else none
  | .mkResult =>
    if state.stage = .self then some { state with stage := .result } else none
  | .setRef target =>
    if state.stage = .result ∧ target = .result then
      some { state with stage := .linked, target := target }
    else none
  | .beginResult =>
    if state.stage = .linked then
      some { state with stage := .running, builds := state.builds + 1 }
    else none
  | .returnResult =>
    if state.stage = .running then some { state with stage := .returned } else none
  | .forceResult =>
    match state.stage with
    | .returned => some { state with stage := .ready }
    | .ready => some { state with reads := state.reads + 1 }
    | _ => none
  | .beginSelf =>
    if installed state.stage ∧ state.selfSlot = .cold then
      some { state with selfSlot := .running }
    else none
  | .getRef target =>
    if installed state.stage ∧ state.selfSlot = .running ∧
        state.loaded = false ∧ target = state.target then
      some { state with loaded := true, cellReads := state.cellReads + 1 }
    else none
  | .returnSelf =>
    if state.stage = .ready ∧ state.selfSlot = .running ∧ state.loaded = true then
      some { state with selfSlot := .returned }
    else none
  | .forceSelf =>
    if state.stage = .ready ∧ (state.selfSlot = .returned ∨ state.selfSlot = .ready) then
      some { state with selfSlot := .ready, reads := state.reads + 1 }
    else none
  | .verify confirmed => if confirmed then some state else none

def phase : Stage → Knot.Phase
  | .empty | .bottom => .unallocated
  | .cell | .self | .result => .placeholder
  | .linked => .linked
  | .running | .returned => .building
  | .ready => .ready

/-- Forget allocation details and the second thunk's cache; preserve the
current body, result construction count and completed shared reads. -/
def project (code : Code) (state : State) : Knot.Heap Code :=
  ⟨phase state.stage, if installed state.stage then some code else none,
    state.builds, state.reads⟩

def effect (state : State) : Event → List Knot.Event
  | .mkRef => [.allocate]
  | .setRef _ => [.link]
  | .beginResult => [.beginBuild]
  | .forceResult => if state.stage = .returned then [.finishBuild] else [.cacheHit]
  | .forceSelf => [.forceSelf]
  | _ => []

/-- Every admitted primitive step is either one protocol step or a stutter.
In particular a closure return alone does not finish the protocol build. -/
theorem step_refines (code : Code) (state next : State) (event : Event)
    (transition : step state event = some next) :
    Knot.replay code (project code state) (effect state event) = some (project code next) := by
  cases state with
  | mk stage target selfSlot loaded builds reads cellReads =>
    cases stage <;> cases event <;>
      simp only [step] at transition <;>
      (try split at transition) <;>
      simp_all [installed, project, phase, effect, Knot.replay, Knot.step] <;>
      subst next <;> simp_all

def replay : State → List Event → Option State
  | state, [] => some state
  | state, event :: rest => do
    let next ← step state event
    replay next rest

def effects : State → List Event → List Knot.Event
  | _, [] => []
  | state, event :: rest =>
    effect state event ++ match step state event with
      | none => []
      | some next => effects next rest

theorem Knot.replay_append (code : Code) (heap : Knot.Heap Code)
    (first second : List Knot.Event) :
    Knot.replay code heap (first ++ second) =
      (Knot.replay code heap first).bind (fun next => Knot.replay code next second) := by
  induction first generalizing heap with
  | nil => rfl
  | cons event rest ih =>
    cases found : Knot.step code heap event <;> simp [Knot.replay, found, ih]

theorem replay_refines (code : Code) (events : List Event) (state next : State)
    (transition : replay state events = some next) :
    Knot.replay code (project code state) (effects state events) = some (project code next) := by
  induction events generalizing state with
  | nil => cases transition; rfl
  | cons event rest ih =>
    cases found : step state event with
    | none => simp [replay, found] at transition
    | some middle =>
      have tail : replay middle rest = some next := by simpa [replay, found] using transition
      simp only [effects, found, Knot.replay_append, step_refines code state middle event found]
      exact ih middle tail

theorem ready_current (code : Code) (events : List Event) (state : State)
    (transition : replay {} events = some state) (ready : state.stage = .ready) :
    (project code state).code = some code ∧ state.builds = 1 := by
  have refined := replay_refines code events {} state transition
  exact Knot.one_build code (effects {} events) (project code state) refined
    (by simp [project, phase, ready])

theorem ready_read (code : Code) (events : List Event) (state : State)
    (transition : replay {} events = some state) (ready : state.stage = .ready) :
    Knot.read (project code state) = some code := by
  have valid := Knot.replay_preserves code (effects {} events) {} (project code state)
    (Knot.invariant_empty code) (replay_refines code events {} state transition)
  exact Knot.read_current code _ valid (by simp [project, phase, ready])

/-- The self forwarding closure reads the private cell at most once.
Subsequent completed gets use its cached value, not another Ref.get. -/
def ForwardInvariant (state : State) : Prop :=
  state.cellReads = (if state.loaded then 1 else 0) ∧
    (state.selfSlot = .cold → state.loaded = false)

theorem forward_empty : ForwardInvariant ({} : State) := by
  simp [ForwardInvariant]

theorem step_forward (state next : State) (event : Event)
    (valid : ForwardInvariant state) (transition : step state event = some next) :
    ForwardInvariant next := by
  cases event <;> simp only [step] at transition <;>
    (try split at transition) <;> simp_all [ForwardInvariant] <;>
    (try subst next) <;> simp_all
  all_goals cases state.stage <;> simp_all

theorem replay_forward (events : List Event) (state next : State)
    (valid : ForwardInvariant state) (transition : replay state events = some next) :
    ForwardInvariant next := by
  induction events generalizing state with
  | nil => cases transition; exact valid
  | cons event rest ih =>
    cases found : step state event with
    | none => simp [replay, found] at transition
    | some middle =>
      exact ih middle (step_forward state middle event valid found)
        (by simpa [replay, found] using transition)

theorem at_most_one_cell_read (events : List Event) (state : State)
    (transition : replay {} events = some state) : state.cellReads ≤ 1 := by
  have valid := (replay_forward events {} state forward_empty transition).left
  rw [valid]
  cases state.loaded <;> decide

/-- Once installed, the private reference retains the result thunk identity.
There is no permitted second store or escape of the cell in this program. -/
def ReferenceInvariant (state : State) : Prop :=
  installed state.stage = true → state.target = .result

theorem step_reference (state next : State) (event : Event)
    (valid : ReferenceInvariant state) (transition : step state event = some next) :
    ReferenceInvariant next := by
  cases state with
  | mk stage target selfSlot loaded builds reads cellReads =>
    cases stage <;> cases event <;>
      simp only [step] at transition <;> (try split at transition) <;>
      simp_all [ReferenceInvariant, installed] <;> subst next <;> simp_all

theorem replay_reference (events : List Event) (state next : State)
    (valid : ReferenceInvariant state) (transition : replay state events = some next) :
    ReferenceInvariant next := by
  induction events generalizing state with
  | nil => cases transition; exact valid
  | cons event rest ih =>
    cases found : step state event with
    | none => simp [replay, found] at transition
    | some middle =>
      exact ih middle (step_reference state middle event valid found)
        (by simpa [replay, found] using transition)

theorem ready_reference (events : List Event) (state : State)
    (transition : replay {} events = some state) (ready : state.stage = .ready) :
    state.target = .result :=
  replay_reference events {} state (by simp [ReferenceInvariant, installed]) transition
    (by simp [installed, ready])

theorem busy_result_waits (state : State) (busy : state.stage = .running) :
    step state .forceResult = none := by simp [step, busy]

theorem result_hit_preserves (state : State) (ready : state.stage = .ready) :
    step state .forceResult = some { state with reads := state.reads + 1 } := by
  simp [step, ready]

inductive Delay where
  | unavailable | self | result
  deriving Repr, BEq, DecidableEq

private def perform (event : Event) : StateT State Option Unit := fun state =>
  (step state event).map fun next => ((), next)

/-- Interpret the exact production constructor with the primitive rules. -/
def operations : SharedCell.Operations (StateT State Option) Unit Delay where
  unavailable := do perform .mkUnavailable; return .unavailable
  mkRef := fun delay => do
    if delay != .unavailable then failure
    perform .mkRef
  mkSelf := fun _ => do perform .mkSelf; return .self
  mkResult := fun delay => do
    if delay != .self then failure
    perform .mkResult
    return .result
  setRef := fun _ delay => do
    if delay != .result then failure
    perform (.setRef .result)

theorem constructor_installs :
    (SharedCell.tie operations).run {} = some (.result, { stage := .linked, target := .result }) := rfl

theorem constructor_is_replay :
    (SharedCell.tie operations).run {} =
      (replay {} SharedCell.construction).map (fun state => (.result, state)) := rfl

/-- Proof-bearing admission reconstructs primitive transitions from data.
Neither this receipt nor its invariant proves that forged data came from IO. -/
structure Receipt (code : Code) (events : List Event) where
  state : State
  transition : replay {} events = some state
  refinement : Knot.replay code {} (effects {} events) = some (project code state)
  invariant : Knot.Invariant code (project code state)
  forwarding : ForwardInvariant state
  reference : ReferenceInvariant state

def check (code : Code) (events : List Event) : Option (Receipt code events) :=
  match found : replay {} events with
  | none => none
  | some state =>
    let refinement := replay_refines code events {} state found
    some ⟨state, found, refinement,
      Knot.replay_preserves code _ {} _ (Knot.invariant_empty code) refinement,
      replay_forward events {} state forward_empty found,
      replay_reference events {} state (by simp [ReferenceInvariant, installed]) found⟩

theorem check_complete (code : Code) (events : List Event) (state : State)
    (transition : replay {} events = some state) : ∃ receipt, check code events = some receipt := by
  unfold check
  split
  · rename_i failed
    rw [transition] at failed
    contradiction
  · exact ⟨_, rfl⟩

/-- Combine the actual operation log with the earlier exact-program candidate
checker. Successful reads retain both proofs; no IO equation is postulated. -/
structure Invocation (program : Generator Input Output) (input : Input)
    (events : List Event) (candidate : Candidate Output) where
  heap : Receipt program events
  ready : heap.state.stage = .ready
  evaluation : Cached.Receipt program (program input)
  reported : evaluation.result.observation = candidate.result

def admitInvocation [DecidableEq Output] (program : Generator Input Output) (input : Input)
    (events : List Event) (candidate : Candidate Output) :
    Option (Invocation program input events candidate) := do
  let heap ← check program events
  if ready : heap.state.stage = .ready then
    match accepted : admit program (program input) candidate with
    | none => none
    | some evaluation =>
      return ⟨heap, ready, evaluation, admit_result _ _ _ _ accepted⟩
  else none

theorem Invocation.current (invocation : Invocation program input events candidate) :
    Knot.read (project program invocation.heap.state) = some program :=
  ready_read program events _ invocation.heap.transition invocation.ready

theorem Invocation.observed (invocation : Invocation program input events candidate) :
    ∃ depth, solve program depth input = candidate.result := by
  obtain ⟨depth, observed⟩ := invocation.evaluation.observed
  exact ⟨depth, observed.trans invocation.reported⟩

theorem Invocation.one_build (invocation : Invocation program input events candidate) :
    invocation.heap.state.builds = 1 :=
  (ready_current program events _ invocation.heap.transition invocation.ready).right

end LeanPoo.Prototype.Recursive.Shared.CellRefinement
