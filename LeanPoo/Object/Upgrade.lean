import LeanPoo.Object.Memo
import Std.Sync.Mutex

/-! Cooperative operation boundaries for section 6's quiescent upgrade exercise.
The pure control machine is independent of slot evaluation. The runtime guards
admission and installation with a mutex and releases scoped readers in finally.
-/
namespace LeanPoo.Object.Upgrade

structure Ticket where
  version : Nat
  request : Nat
  deriving Repr, DecidableEq, BEq

inductive Error where
  | paused
  | alreadyPending
  | stale
  | busy (active : Nat)
  deriving Repr, DecidableEq

structure Control where
  version : Nat := 0
  active : Nat := 0
  pending : Option Ticket := none
  nextRequest : Nat := 0
  deriving Repr, DecidableEq

def Control.enter (state : Control) : Except Error Control :=
  if state.pending.isSome then .error .paused
  else .ok { state with active := state.active + 1 }

/-- Used once by the runtime's finally block for each admitted operation. -/
def Control.leave (state : Control) : Control :=
  { state with active := state.active - 1 }

def Control.pause (state : Control) : Except Error (Ticket × Control) :=
  if state.pending.isSome then .error .alreadyPending
  else
    let ticket := { version := state.version, request := state.nextRequest }
    .ok (ticket, { state with pending := some ticket, nextRequest := state.nextRequest + 1 })

def Control.cancel (state : Control) (ticket : Ticket) : Except Error Control :=
  if state.pending = some ticket ∧ ticket.version = state.version then
    .ok { state with pending := none }
  else .error .stale

/-- Only the matching request at a quiescent operation boundary can advance. -/
def Control.commit (state : Control) (ticket : Ticket) : Except Error Control :=
  if state.pending = some ticket ∧ ticket.version = state.version then
    if state.active = 0 then
      .ok { state with version := state.version + 1, pending := none }
    else .error (.busy state.active)
  else .error .stale

theorem Control.commit_quiescent (state next : Control) (ticket : Ticket)
    (success : state.commit ticket = .ok next) :
    state.active = 0 ∧ next.version = state.version + 1 ∧ next.pending = none := by
  unfold commit at success
  split at success
  · split at success
    · rename_i idle
      simp only [Except.ok.injEq] at success
      subst next
      exact ⟨idle, rfl, rfl⟩
    · cases success
  · cases success

theorem Control.commit_authorized (state next : Control) (ticket : Ticket)
    (success : state.commit ticket = .ok next) :
    state.pending = some ticket ∧ ticket.version = state.version := by
  unfold commit at success
  split at success
  · assumption
  · cases success

theorem Control.enter_paused (state : Control) (ticket : Ticket)
    (pending : state.pending = some ticket) : state.enter = .error .paused := by
  simp [enter, pending]

inductive Failure (ε : Type) where
  | control (error : Error)
  | update (error : ε)
  deriving Repr

private structure State (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where
  control : Control := {}
  object : Memoized Key Value

/-- One guarded identity; operations capture a persistent snapshot. -/
structure Runtime (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where private mk ::
  private state : Std.Mutex (State Key Value)

/-- A request is bound to its runtime, rather than a transferable version number. -/
structure Session (Key : Type) (Value : Key → Type)
    [BEq Key] [LawfulBEq Key] [Hashable Key] where private mk ::
  private owner : Runtime Key Value
  private ticket : Ticket

def Runtime.new {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (object : Memoized Key Value) : IO (Runtime Key Value) := do
  return ⟨← Std.Mutex.new { object := object }⟩

def Runtime.status {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) : IO Control :=
  runtime.state.atomically do return (← get).control

/-- The callback runs outside the lock. Its admission remains active until it
returns or throws. A returned snapshot remains an immutable old-version value;
background work must finish before the callback returns to count as active. -/
def Runtime.withSnapshot {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) (operation : Nat → Memoized Key Value → IO α) :
    IO (Except Error α) := do
  let admitted : Except Error (Nat × Memoized Key Value) ← runtime.state.atomically do
    let state ← get
    match state.control.enter with
    | .error error => return .error error
    | .ok control =>
      set { state with control := control }
      return .ok (control.version, state.object)
  match admitted with
  | .error error => return .error error
  | .ok (version, object) =>
    try
      return .ok (← operation version object)
    finally
      runtime.state.atomically do
        modify fun state => { state with control := state.control.leave }

def Runtime.pause {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (runtime : Runtime Key Value) : IO (Except Error (Session Key Value)) :=
  runtime.state.atomically do
    let state ← get
    match state.control.pause with
    | .error error => return .error error
    | .ok (ticket, control) =>
      set { state with control := control }
      return .ok ⟨runtime, ticket⟩

def Session.cancel {Key : Type} {Value : Key → Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (session : Session Key Value) : IO (Except Error Unit) :=
  session.owner.state.atomically do
    let state ← get
    match state.control.cancel session.ticket with
    | .error error => return .error error
    | .ok control =>
      set { state with control := control }
      return .ok ()

/-- Non-waiting attempt: busy or stale requests never run the updater. Update
failure keeps admission paused for retry or cancellation. The pure updater runs
under the lock, and must not reenter this runtime through effects. -/
def Session.commit {Key : Type} {Value : Key → Type} {ε : Type}
    [BEq Key] [LawfulBEq Key] [Hashable Key]
    (session : Session Key Value)
    (update : Memoized Key Value → Except ε (Memoized Key Value)) :
    IO (Except (Failure ε) Nat) :=
  session.owner.state.atomically do
    let state ← get
    match state.control.commit session.ticket with
    | .error error => return .error (.control error)
    | .ok control =>
      match update state.object with
      | .error error => return .error (.update error)
      | .ok object =>
        set ({ object := object, control := control } : State Key Value)
        return .ok control.version

end LeanPoo.Object.Upgrade
