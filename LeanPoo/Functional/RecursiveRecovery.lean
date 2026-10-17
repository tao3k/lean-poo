import LeanPoo.Functional.RecursiveSubmissions

/-! Serialized coordinator exit and explicit recovery of recursive publications.
An exit retains the installed prefix and historical observations, not a live queue.
Original outcome propagation and scope cleanup are executable Gerbil controls;
these finite pure laws extend generalized MOP future work under complete guards. -/
namespace LeanPoo.Functional.RecursiveRecovery
open RecursiveStaging RecursivePublication RecursiveCompetition RecursiveSubmissions

/-- An observed exit carries the original result and exact installed prefix.
Pending capabilities belong to the closed scope and are deliberately absent. -/
structure Exit (Graph Stamp GraphError Entry Context Error Result ExitError ExitResult : Type) where
  world : World Graph Entry Context
  receipts : List (Receipt Graph Stamp GraphError Entry Context Error Result)
  outcome : Except ExitError ExitResult

/-- Observe an already completed scope, without rolling back any publication.
The host checks that normal return drained its queue; this operation models the
post-cleanup observation, including exceptions and rejected unconsumed returns. -/
def finish (state : Session Graph Stamp GraphError Entry Context Error Result)
    (outcome : Except ExitError ExitResult) :
    Exit Graph Stamp GraphError Entry Context Error Result ExitError ExitResult :=
  ⟨state.world,state.receipts,outcome⟩

/-- Start an independent scope against the actual currently installed world.
Previously returned receipts remain in their exit record; no old queue is revived. -/
def restart (world : World Graph Entry Context) : Session Graph Stamp GraphError Entry Context Error Result :=
  ⟨world,[],[]⟩

/-- Recovery explicitly prepares one new request against the current whole pair.
This does not publish or validate an old request, even if its intent is reused. -/
def recover (world : World Graph Entry Context)
    (prepare : World Graph Entry Context → Submission Graph Stamp GraphError Entry Context Error Result) :=
  enqueue (restart world) prepare

/-- Coordinator failure or normal exit cannot undo a previously installed prefix. -/
theorem finish_world (state : Session Graph Stamp GraphError Entry Context Error Result)
    (outcome : Except ExitError ExitResult) : (finish state outcome).world = state.world := rfl

/-- Historical receipts are retained exactly and cannot become current approvals. -/
theorem finish_receipts (state : Session Graph Stamp GraphError Entry Context Error Result)
    (outcome : Except ExitError ExitResult) : (finish state outcome).receipts = state.receipts := rfl

/-- Finite outcome observation preserves the original error or returned value. -/
theorem finish_outcome (state : Session Graph Stamp GraphError Entry Context Error Result)
    (outcome : Except ExitError ExitResult) : (finish state outcome).outcome = outcome := rfl

/-- A restarted scope has no queued requests or receipts from the exited scope. -/
theorem restart_empty (world : World Graph Entry Context) :
    (restart (GraphError := GraphError) (Stamp := Stamp) (Error := Error) (Result := Result) world).pending = [] ∧
    (restart (GraphError := GraphError) (Stamp := Stamp) (Error := Error) (Result := Result) world).receipts = [] := ⟨rfl,rfl⟩

/-- Fresh recovery sees THIS world; it cannot retain the closed queue by alias. -/
theorem recover_current (world : World Graph Entry Context) (prepare) :
    (recover (GraphError := GraphError) (Stamp := Stamp) (Error := Error) (Result := Result) world prepare).pending = [prepare world] ∧
    (recover world prepare).world = world := ⟨rfl,rfl⟩

/-- Surviving coordinators can continue while another has exited; their finite
attempt/arrival script keeps the actual installed prefix monotone. -/
theorem survivors_monotone [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (outcome : Except ExitError ExitResult)
    (events : List (Event Graph Stamp GraphError Entry Context Error Result)) :
    state.world.graph.revision ≤ (run events (restart (finish state outcome).world)).world.graph.revision :=
  run_monotone events (restart state.world)

/-- Rejoining after survivor publications prepares from their actual current head,
not the failed coordinator's historical exit snapshot. Installation remains separate. -/
theorem recover_after_survivors [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (outcome : Except ExitError ExitResult)
    (events : List (Event Graph Stamp GraphError Entry Context Error Result))
    (prepare : World Graph Entry Context → Submission Graph Stamp GraphError Entry Context Error Result) :
    let current := (run events (restart (finish state outcome).world)).world
    (recover current prepare).pending = [prepare current] ∧ (recover current prepare).receipts = [] := by
  exact ⟨rfl,rfl⟩

/-- Neither exit, survivor progress nor recovery admits an older-round request.
Complete guard stamps additionally reject same-round approval ABA in the base model. -/
theorem historical_after_exit [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result) (outcome : Except ExitError ExitResult)
    (events : List (Event Graph Stamp GraphError Entry Context Error Result))
    (old : Request Graph Stamp GraphError) (observed : Stamp) (older : old.expected < state.world.graph.revision) :
    publish old (run events (restart (finish state outcome).world)).world.graph observed =
      (.error .stale,(run events (restart (finish state outcome).world)).world.graph) :=
  RecursiveSubmissions.historical_stale events (restart state.world) old observed older

/-- Failure after a winning installation retains the new graph even when its
entry effect has refused. Closing the scope does not roll it back to the old world. -/
theorem exit_after_late_refusal [DecidableEq Stamp] [DecidableEq Entry]
    (state : Session Graph Stamp GraphError Entry Context Error Result)
    (item : Submission Graph Stamp GraphError Entry Context Error Result) (rest) (observed : Stamp)
    (next : State Graph) (cause : Error) (outcome : Except ExitError ExitResult)
    (pending : state.pending = item :: rest)
    (closed : publish item.request state.world.graph observed = (.ok (),next))
    (refused : item.effect next.value (state.world.contexts item.entry) = .error cause) :
    (finish (advance state observed) outcome).world = {state.world with graph := next} := by
  simp only [finish,advance,pending]
  rw [late_refusal item.request state.world observed item.entry item.effect next cause closed refused]

end LeanPoo.Functional.RecursiveRecovery
