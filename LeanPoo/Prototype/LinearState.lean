import Std.Sync.Mutex

/-! Runtime enforcement of the paper's consume-old/return-new state reference.
This complements persistent snapshots and mutable identities; it is not a
static linear type system or an in-place allocation optimization. -/
namespace LeanPoo.Prototype

structure LinearState (α : Type) where private mk ::
  private cell : Std.Mutex (Option α)

def LinearState.create (value : α) : IO (LinearState α) := do
  return ⟨← Std.Mutex.new (some value)⟩

/-- A pure snapshot may escape; only the state-reference capability is consumed. -/
def LinearState.read (state : LinearState α) : IO (Except String α) :=
  state.cell.atomically do
    match ← get with
    | none => return .error "consumed state reference"
    | some value => return .ok value

/-- A successful transition consumes every alias of the old reference and
returns a new reference. Rejection retains the old reference. The mutex
serializes competing consumers; the callback is a pure checked transition. -/
def LinearState.step (state : LinearState α) (update : α → Except String α) :
    IO (Except String (LinearState α)) :=
  state.cell.atomically do
    let some value ← get | return .error "consumed state reference"
    match update value with
    | .error error => return .error error
    | .ok next =>
      let fresh ← LinearState.create next
      set (none : Option α)
      return .ok fresh

/-- Checked parent-before-child state composition. -/
def LinearState.compose (child parent : α → Except String α) : α → Except String α :=
  fun value => do child (← parent value)

theorem LinearState.compose_assoc (outer middle inner : α → Except String α) (value : α) :
    compose (compose outer middle) inner value = compose outer (compose middle inner) value := by
  cases h : inner value with
  | error error => simp [compose, h]
  | ok next => cases hm : middle next <;> simp [compose, h, hm]

/-- Pure state threading supplies the reference transition's value semantics. -/
def LinearState.runPure (updates : List (α → Except String α)) (base : α) : Except String α :=
  updates.foldlM (fun value update => update value) base

def LinearState.run (updates : List (α → Except String α)) (base : α) :
    IO (Except String (LinearState α)) := do
  let mut state ← LinearState.create base
  for update in updates do
    match ← state.step update with
    | .error error => return .error error
    | .ok next => state := next
  return .ok state

end LeanPoo.Prototype
