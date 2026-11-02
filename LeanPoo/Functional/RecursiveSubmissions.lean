import LeanPoo.Functional.RecursiveCompetition

/-! Open-ended, caller-serialized admission of requests between publication steps.
This generalized MOP future work assumes complete version observations and pure,
locally terminating callbacks. Scope/exception discipline is tested in Gerbil;
these laws describe finite FIFO transitions, not host concurrency or rollback. -/
namespace LeanPoo.Functional.RecursiveSubmissions
open RecursiveStaging RecursivePublication RecursiveCompetition

/-- Pending requests and receipts retain their original order and separate worlds. -/
structure Session (Graph Stamp GraphError Entry Context Error Result : Type) where
  world : World Graph Entry Context
  pending : List (Submission Graph Stamp GraphError Entry Context Error Result) := []
  receipts : List (Receipt Graph Stamp GraphError Entry Context Error Result) := []

/-- Admit fresh work prepared from the current world while preserving older requests.
Enqueue does not construct or install a graph and does not refresh pending work. -/
def enqueue (state : Session Graph Stamp GraphError Entry Context Error Result)
    (prepare : World Graph Entry Context → Submission Graph Stamp GraphError Entry Context Error Result) :=
  {state with pending := state.pending ++ [prepare state.world]}

/-- Attempt only the FIFO head with the versions observed now. Preserve the original
request and all previous receipts even when graph or effect admission refuses. -/
def advance [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (observed : Stamp) :
    Session Graph Stamp GraphError Entry Context Error Result :=
  match state.pending with
  | [] => state
  | first :: rest =>
    let item := {first with stamp := observed}
    let (outcome,next) := submit item.request state.world observed item.entry item.effect
    {world := next, pending := rest, receipts := state.receipts ++ [⟨item,outcome,next⟩]}

/-- A coordinator can explicitly prepare fresh work or attempt one existing head. -/
inductive Event (Graph Stamp GraphError Entry Context Error Result : Type) where
  | enqueue (prepare : World Graph Entry Context → Submission Graph Stamp GraphError Entry Context Error Result)
  | advance (observed : Stamp)

/-- Execute a finite interleaving without automatic retries or implicit restaging. -/
def run [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Graph Stamp GraphError Entry Context Error Result))
    (state : Session Graph Stamp GraphError Entry Context Error Result) :=
  events.foldl (fun current event => match event with
    | .enqueue prepare => enqueue current prepare
    | .advance observed => advance current observed) state

/-- Fresh preparation sees the installed world and cannot rebase older requests. -/
theorem enqueue_pending (state : Session Graph Stamp GraphError Entry Context Error Result) (prepare) :
    (enqueue state prepare).pending = state.pending ++ [prepare state.world] := rfl

/-- Admission alone changes neither installation nor historical receipts. -/
theorem enqueue_preserves (state : Session Graph Stamp GraphError Entry Context Error Result) (prepare) :
    (enqueue state prepare).world = state.world ∧ (enqueue state prepare).receipts = state.receipts := ⟨rfl,rfl⟩

/-- An empty advance is exactly the identity transition. -/
theorem empty_advance [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (observed : Stamp)
    (empty : state.pending = []) : advance state observed = state := by simp [advance,empty]

/-- A nonempty advance consumes precisely one head, retaining the pending suffix. -/
theorem advance_pending [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (observed : Stamp) (first rest)
    (pending : state.pending = first :: rest) : (advance state observed).pending = rest := by
  simp [advance,pending]

/-- Every consumed head appends one receipt; old receipts remain an exact prefix. -/
theorem advance_receipts [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (observed : Stamp) (first rest)
    (pending : state.pending = first :: rest) :
    ∃ receipt, (advance state observed).receipts = state.receipts ++ [receipt] := by
  simp [advance,pending]

/-- Both approval phases and arbitrary entry effects preserve revision monotonicity. -/
theorem advance_monotone [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (observed : Stamp) :
    state.world.graph.revision ≤ (advance state observed).world.graph.revision := by
  cases pending : state.pending with
  | nil => simp [advance,pending]
  | cons first rest =>
    simpa [advance,pending] using submit_revision_monotone {first with stamp := observed} state.world

/-- New arrivals interleaved with failed or successful attempts cannot lower a round. -/
theorem run_monotone [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Graph Stamp GraphError Entry Context Error Result))
    (state : Session Graph Stamp GraphError Entry Context Error Result) :
    state.world.graph.revision ≤ (run events state).world.graph.revision := by
  induction events generalizing state with
  | nil => exact Nat.le_refl _
  | cons event rest ih =>
    cases event with
    | enqueue prepare => exact ih (enqueue state prepare)
    | advance observed => exact Nat.le_trans (advance_monotone state observed) (ih (advance state observed))

/-- A historical request remains stale after every finite continuing arrival/retry
script, even if names, topology or metadata values return to an earlier shape. -/
theorem historical_stale [DecidableEq Stamp] [DecidableEq Entry]
    (events : List (Event Graph Stamp GraphError Entry Context Error Result))
    (state : Session Graph Stamp GraphError Entry Context Error Result)
    (old : Request Graph Stamp GraphError) (observed : Stamp)
    (older : old.expected < state.world.graph.revision) :
    publish old (run events state).world.graph observed = (.error .stale,(run events state).world.graph) := by
  apply older_round_stale
  have monotone := run_monotone events state
  omega

end LeanPoo.Functional.RecursiveSubmissions
