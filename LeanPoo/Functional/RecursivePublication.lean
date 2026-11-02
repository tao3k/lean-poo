import LeanPoo.Functional.RecursiveRestaging

/-! Multiple entry points share one graph head and have separate effect contexts.
Graph installation precedes entry refinement/evidence. Effects are pure callbacks
in this model; Scheme's sequential handle and explicit read/watch discipline are
correspondence premises. This advances generalized-prototype future work. -/
namespace LeanPoo.Functional.RecursivePublication
open RecursiveStaging

/-- The graph is shared; entry contexts are independently threaded by callers. -/
structure World (Graph Entry Context : Type) where
  graph : State Graph
  contexts : Entry → Context

/-- Observe an installed graph without rebuilding. Only successful effect admission
updates the selected context; refusal retains the exact graph and contexts. -/
def observe [DecidableEq Entry] (world : World Graph Entry Context) (entry : Entry)
    (effect : Graph → Context → Except Error (Result × Context)) :
    Except Error Result × World Graph Entry Context :=
  match effect world.graph.value (world.contexts entry) with
  | .error cause => (.error cause,world)
  | .ok (result,next) => (.ok result,{world with contexts := fun key => if key = entry then next else world.contexts key})

/-- Graph refusal prevents the effect. Successful reclosure installs the shared
head before the selected entry's effect, even when that later effect refuses. -/
def submit [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry : Entry)
    (effect : Graph → Context → Except Error (Result × Context)) :
    Except (Failure GraphError) (Except Error Result) × World Graph Entry Context :=
  let (outcome,next) := publish request world.graph stamp
  let installed := {world with graph := next}
  match outcome with
  | .error cause => (.error cause,installed)
  | .ok () => let (result,last) := observe installed entry effect; (.ok result,last)

/-- An effect-only retry never changes the shared graph, whether it succeeds or fails. -/
theorem observe_graph [DecidableEq Entry] (world : World Graph Entry Context) (entry : Entry)
    (effect : Graph → Context → Except Error (Result × Context)) :
    (observe world entry effect).2.graph = world.graph := by
  unfold observe
  split <;> rfl

/-- Refused evidence leaves every entry's context and the installed graph intact. -/
theorem observe_refused [DecidableEq Entry] (world : World Graph Entry Context) (entry : Entry)
    (effect : Graph → Context → Except Error (Result × Context)) (cause : Error)
    (refused : effect world.graph.value (world.contexts entry) = .error cause) :
    observe world entry effect = (.error cause,world) := by simp [observe,refused]

/-- Publishing at one entry cannot change the other entry's effect context. -/
theorem observe_other [DecidableEq Entry] (world : World Graph Entry Context) (entry other : Entry)
    (effect : Graph → Context → Except Error (Result × Context)) (different : other ≠ entry) :
    (observe world entry effect).2.contexts other = world.contexts other := by
  unfold observe
  split
  · rfl
  · simp [different]

/-- A graph refusal leaves the whole world intact and never invokes an effect. -/
theorem graph_refused [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry : Entry) (effect : Graph → Context → Except Error (Result × Context))
    (cause : Failure GraphError) (refused : publish request world.graph stamp = (.error cause,world.graph)) :
    submit request world stamp entry effect = (.error cause,world) := by simp [submit,refused]

/-- Late effect refusal preserves its context but keeps the newly installed graph. -/
theorem late_refusal [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry : Entry) (effect : Graph → Context → Except Error (Result × Context))
    (next : State Graph) (cause : Error)
    (closed : publish request world.graph stamp = (.ok (),next))
    (refused : effect next.value (world.contexts entry) = .error cause) :
    submit request world stamp entry effect = (.ok (.error cause),{world with graph := next}) := by
  simp [submit,closed,observe,refused]

/-- Entry policies cannot undo successful graph installation. -/
theorem installed_graph [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry : Entry) (effect : Graph → Context → Except Error (Result × Context))
    (next : State Graph) (closed : publish request world.graph stamp = (.ok (),next)) :
    (submit request world stamp entry effect).2.graph = next := by
  simp only [submit,closed]
  exact observe_graph {world with graph := next} entry effect

/-- Across either failure phase or success, the submitting entry cannot update
another entry's context, even though both entries share the newly installed graph. -/
theorem submit_other [DecidableEq Stamp] [DecidableEq Entry]
    (request : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry other : Entry) (effect : Graph → Context → Except Error (Result × Context))
    (different : other ≠ entry) :
    (submit request world stamp entry effect).2.contexts other = world.contexts other := by
  unfold submit
  generalize publish request world.graph stamp = attempt
  rcases attempt with ⟨outcome,next⟩
  cases outcome with
  | error cause => rfl
  | ok acknowledged =>
    cases acknowledged
    exact observe_other {world with graph := next} entry other effect different

/-- A successful graph submission expires sibling requests from EVERY entry,
including when the winning entry's later evidence/policy refuses. -/
theorem sibling_stale [DecidableEq Stamp] [DecidableEq Entry]
    (request sibling : Request Graph Stamp GraphError) (world : World Graph Entry Context)
    (stamp : Stamp) (entry : Entry) (effect : Graph → Context → Except Error (Result × Context))
    (next : State Graph) (closed : publish request world.graph stamp = (.ok (),next))
    (observed : sibling.expected = world.graph.revision) :
    publish sibling (submit request world stamp entry effect).2.graph stamp = (.error .stale,next) := by
  rw [installed_graph request world stamp entry effect next closed]
  exact RecursiveStaging.sibling_stale request sibling world.graph next stamp observed closed

end LeanPoo.Functional.RecursivePublication
