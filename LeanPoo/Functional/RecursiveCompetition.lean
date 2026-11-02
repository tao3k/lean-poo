import LeanPoo.Functional.RecursiveApprovals

/-! Ordered joint revision attempts retain each observed result and world. Stamps
can differ per attempt; no request is refreshed. Pure locally terminating callbacks
and serialized host operations remain premises of this generalized MOP future work. -/
namespace LeanPoo.Functional.RecursiveCompetition
open RecursiveStaging RecursivePublication

/-- One entry's original request, current guard observation and effect observer. -/
structure Submission (Graph Stamp GraphError Entry Context Error Result : Type) where
  request : Request Graph Stamp GraphError
  stamp : Stamp
  entry : Entry
  effect : Graph → Context → Except Error (Result × Context)

/-- A receipt keeps its original submission and its own post-attempt world. -/
structure Receipt (Graph Stamp GraphError Entry Context Error Result : Type) where
  submission : Submission Graph Stamp GraphError Entry Context Error Result
  outcome : Except (Failure GraphError) (Except Error Result)
  world : World Graph Entry Context

/-- Continue after either refusal phase, preserving every observation in order.
The whole sequence is not a transaction; successful prefixes remain installed. -/
def run [DecidableEq Stamp] [DecidableEq Entry]
    (submissions : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context) :
    List (Receipt Graph Stamp GraphError Entry Context Error Result) × World Graph Entry Context :=
  match submissions with
  | [] => ([],world)
  | first :: rest =>
    let (outcome,next) := submit first.request world first.stamp first.entry first.effect
    let (trace,last) := run rest next
    (⟨first,outcome,next⟩ :: trace,last)

/-- Exactly one receipt is retained per submitted request, including all failures. -/
theorem trace_length [DecidableEq Stamp] [DecidableEq Entry]
    (submissions : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context) : (run submissions world).1.length = submissions.length := by
  induction submissions generalizing world with
  | nil => rfl
  | cons first rest ih =>
    cases h : submit first.request world first.stamp first.entry first.effect with
    | mk outcome next => simp [run,h,ih]

/-- A graph/guard refusal preserves the world and leaves later attempts untouched. -/
theorem refused_prefix [DecidableEq Stamp] [DecidableEq Entry]
    (first : Submission Graph Stamp GraphError Entry Context Error Result) (rest)
    (world : World Graph Entry Context) (cause : Failure GraphError)
    (refused : publish first.request world.graph first.stamp = (.error cause,world.graph)) :
    run (first :: rest) world =
      let (trace,last) := run rest world
      (⟨first,.error cause,world⟩ :: trace,last) := by
  simp only [run,graph_refused first.request world first.stamp first.entry first.effect cause refused]

/-- A late effect refusal records the newly installed graph before later attempts. -/
theorem late_refusal_prefix [DecidableEq Stamp] [DecidableEq Entry]
    (first : Submission Graph Stamp GraphError Entry Context Error Result) (rest)
    (world : World Graph Entry Context) (next : State Graph) (cause : Error)
    (closed : publish first.request world.graph first.stamp = (.ok (),next))
    (refused : first.effect next.value (world.contexts first.entry) = .error cause) :
    run (first :: rest) world =
      let installed := {world with graph := next}
      let (trace,last) := run rest installed
      (⟨first,.ok (.error cause),installed⟩ :: trace,last) := by
  simp only [run,late_refusal first.request world first.stamp first.entry first.effect next cause closed refused]

/-- All obsolete attempts, with any observed guard stamps or entry observers,
preserve the current world and record stale refusals without invoking effects. -/
theorem obsolete_batch [DecidableEq Stamp] [DecidableEq Entry]
    (submissions : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context)
    (older : ∀ item ∈ submissions, item.request.expected < world.graph.revision) :
    run submissions world = (submissions.map (fun item => ⟨item,.error .stale,world⟩),world) := by
  induction submissions with
  | nil => rfl
  | cons first rest ih =>
    have refused := older_round_stale first.request world.graph first.stamp (older first (by simp))
    have tail := ih (fun item member => older item (by simp [member]))
    simp [run,graph_refused first.request world first.stamp first.entry first.effect .stale refused,tail]

/-- Neither failure phase can decrease the installed revision; success advances it. -/
theorem submit_revision_monotone [DecidableEq Stamp] [DecidableEq Entry]
    (item : Submission Graph Stamp GraphError Entry Context Error Result) (world : World Graph Entry Context) :
    world.graph.revision ≤ (submit item.request world item.stamp item.entry item.effect).2.graph.revision := by
  cases h : publish item.request world.graph item.stamp with
  | mk outcome next =>
    cases outcome with
    | error cause =>
      have same := refusal_preserves item.request world.graph next item.stamp cause h
      subst next
      simp [graph_refused item.request world item.stamp item.entry item.effect cause h]
    | ok acknowledged =>
      cases acknowledged
      rw [installed_graph item.request world item.stamp item.entry item.effect next h]
      have advanced := success_revision item.request world.graph next item.stamp h
      omega

/-- Every finite interleaving keeps the logical shared publication identity monotone. -/
theorem run_revision_monotone [DecidableEq Stamp] [DecidableEq Entry]
    (submissions : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context) : world.graph.revision ≤ (run submissions world).2.graph.revision := by
  induction submissions generalizing world with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
    cases h : submit first.request world first.stamp first.entry first.effect with
    | mk outcome next =>
      have one := submit_revision_monotone first world
      rw [h] at one
      have many := ih next
      cases tail : run rest next with
      | mk trace last =>
        simp only [run,h,tail]
        rw [tail] at many
        exact Nat.le_trans one many

/-- No later finite mix of successful and failed attempts revives a historical request. -/
theorem historical_stale [DecidableEq Stamp] [DecidableEq Entry]
    (submissions : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context) (old : Request Graph Stamp GraphError) (stamp : Stamp)
    (older : old.expected < world.graph.revision) :
    publish old (run submissions world).2.graph stamp = (.error .stale,(run submissions world).2.graph) := by
  apply older_round_stale
  have monotone := run_revision_monotone submissions world
  omega

/-- One winning graph invalidates every same-or-earlier round challenger, even when
its own effect refuses. Each remaining receipt retains that installed world. -/
theorem after_winner_obsolete [DecidableEq Stamp] [DecidableEq Entry]
    (winner : Submission Graph Stamp GraphError Entry Context Error Result)
    (rest : List (Submission Graph Stamp GraphError Entry Context Error Result))
    (world : World Graph Entry Context) (next : State Graph)
    (closed : publish winner.request world.graph winner.stamp = (.ok (),next))
    (old : ∀ item ∈ rest, item.request.expected ≤ world.graph.revision) :
    let installed := (submit winner.request world winner.stamp winner.entry winner.effect).2
    run rest installed = (rest.map (fun item => ⟨item,.error .stale,installed⟩),installed) := by
  dsimp only
  apply obsolete_batch
  intro item member
  rw [installed_graph winner.request world winner.stamp winner.entry winner.effect next closed]
  have advanced := success_revision winner.request world.graph next winner.stamp closed
  have bound := old item member
  omega

end LeanPoo.Functional.RecursiveCompetition
