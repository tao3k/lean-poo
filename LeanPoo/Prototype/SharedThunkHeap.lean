import LeanPoo.Prototype.SharedThunk

/-! The sequential private-cell protocol used by the shared function compiler.
Linking precedes construction; a function closure is published before its body
can demand self. Early forcing of a recursive value has no completed transition.
This is an explicit operational model, not an axiom about Lean's native IO. -/
namespace LeanPoo.Prototype.Recursive.Shared.Knot

inductive Phase where
  | unallocated | placeholder | linked | building | ready
  deriving Repr, BEq, DecidableEq

inductive Event where
  | allocate | link | beginBuild | finishBuild | forceSelf | cacheHit
  deriving Repr, BEq, DecidableEq

structure Heap (Code : Type) where
  phase : Phase := .unallocated
  code : Option Code := none
  builds : Nat := 0
  reads : Nat := 0

def step (code : Code) (heap : Heap Code) (event : Event) : Option (Heap Code) :=
  match heap.phase, event with
  | .unallocated, .allocate => some { heap with phase := .placeholder }
  | .placeholder, .link => some { heap with phase := .linked, code := some code }
  | .linked, .beginBuild => some { heap with phase := .building, builds := heap.builds + 1 }
  | .building, .finishBuild => some { heap with phase := .ready }
  | .ready, .forceSelf | .ready, .cacheHit => some { heap with reads := heap.reads + 1 }
  | _, _ => none

/-- The only installed code is the current compiler's body. There is exactly
one constructor start, and a cache hit cannot change code or build count. -/
def Invariant (code : Code) (heap : Heap Code) : Prop :=
  match heap.phase with
  | .unallocated | .placeholder => heap.code = none ∧ heap.builds = 0
  | .linked => heap.code = some code ∧ heap.builds = 0
  | .building | .ready => heap.code = some code ∧ heap.builds = 1

theorem invariant_empty (code : Code) : Invariant code ({} : Heap Code) := ⟨rfl, rfl⟩

theorem step_preserves (code : Code) (heap next : Heap Code) (event : Event)
    (valid : Invariant code heap) (transition : step code heap event = some next) :
    Invariant code next := by
  cases heap with
  | mk phase installed builds reads =>
    cases phase <;> cases event <;>
      simp_all [step, Invariant] <;> subst next <;> simp_all

def replay (code : Code) : Heap Code → List Event → Option (Heap Code)
  | heap, [] => some heap
  | heap, event :: rest => do
    let next ← step code heap event
    replay code next rest

theorem replay_preserves (code : Code) (events : List Event) (heap next : Heap Code)
    (valid : Invariant code heap) (transition : replay code heap events = some next) :
    Invariant code next := by
  induction events generalizing heap with
  | nil => cases transition; exact valid
  | cons event rest ih =>
    cases found : step code heap event with
    | none => simp [replay, found] at transition
    | some middle =>
      exact ih middle (step_preserves code heap middle event valid found)
        (by simpa [replay, found] using transition)

theorem one_build (code : Code) (events : List Event) (heap : Heap Code)
    (transition : replay code {} events = some heap) (ready : heap.phase = .ready) :
    heap.code = some code ∧ heap.builds = 1 := by
  have valid := replay_preserves code events {} heap (invariant_empty code) transition
  simpa [Invariant, ready] using valid

theorem early_self_refused (code : Code) (heap : Heap Code)
    (notReady : heap.phase ≠ .ready) : step code heap .forceSelf = none := by
  cases found : heap.phase <;> simp_all [step]

theorem ready_hit (code : Code) (heap : Heap Code) (ready : heap.phase = .ready) :
    step code heap .cacheHit = some { heap with reads := heap.reads + 1 } := by
  simp [step, ready]

def construction : List Event := [.allocate, .link, .beginBuild, .finishBuild]

theorem construction_ready (code : Code) :
    replay code {} construction = some ⟨.ready, some code, 1, 0⟩ := rfl

/-- Forcing a ready shared closure retrieves its current installed body.
An unavailable or still-building recursive value cannot be read successfully. -/
def read (heap : Heap Code) : Option Code :=
  if heap.phase = .ready then heap.code else none

theorem read_current (code : Code) (heap : Heap Code) (valid : Invariant code heap)
    (ready : heap.phase = .ready) : read heap = some code := by
  simp only [Invariant, ready] at valid
  simp [read, ready, valid.left]

/-- A completed invocation uses the body retrieved from the private cell.
The trace relation specifies recursive calls and continuation/error ordering. -/
structure Invocation (program : Generator Input Output)
    (heap : Heap (Generator Input Output)) (input : Input) (candidate : Candidate Output) : Prop where
  current : read heap = some program
  execution : Runs program (program input) candidate

theorem invocation_evaluates (invocation : Invocation program heap input candidate) :
    Evaluates program (program input) candidate.result := invocation.execution.evaluates

theorem invocation_iff [DecidableEq Output] (program : Generator Input Output)
    (heap : Heap (Generator Input Output)) (input : Input) (candidate : Candidate Output)
    (valid : Invariant program heap) (ready : heap.phase = .ready) :
    Invocation program heap input candidate ↔
      ∃ receipt, admit program (program input) candidate = some receipt := by
  constructor
  · intro invocation
    exact (admit_iff_runs _ _ _).mpr invocation.execution
  · intro accepted
    exact ⟨read_current program heap valid ready, (admit_iff_runs _ _ _).mp accepted⟩

end LeanPoo.Prototype.Recursive.Shared.Knot
