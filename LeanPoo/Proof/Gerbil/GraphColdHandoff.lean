/- Pure projection before a cold Graph handoff. Native GC is measured separately. -/
namespace GraphColdHandoff

structure Capture (Positions Direction Payload : Type) where
  positions : Positions
  direction : Direction
  payload : Payload

structure View (Positions Direction : Type) where
  positions : Positions
  direction : Direction

def project (capture : Capture P D B) : View P D :=
  ⟨capture.positions, capture.direction⟩

theorem projection_ignores_payload (positions : P) (direction : D) (a b : B) :
    project (Capture.mk positions direction a) =
      project (Capture.mk positions direction b) := rfl

-- State can include the complete observable trace, including failure effects.
abbrev Action (State Error Value : Type) := State → Except Error Value × State

def bind (first : Action S E A) (next : A → Action S E B) : Action S E B :=
  fun state => match first state with
    | (.error error, state') => (.error error, state')
    | (.ok value, state') => next value state'

def before (capture : Capture P D Storage)
    (discover : Capture P D Storage → Action S E Result)
    (certify : Result → Action S E Partition)
    (own : View P D → Partition → Action S E Snapshot) : Action S E Snapshot :=
  bind (discover capture) (fun result =>
    bind (certify result) (fun part => own (project capture) part))

def after (capture : Capture P D Storage)
    (discover : Capture P D Storage → Action S E Result)
    (certify : Result → Action S E Partition)
    (own : View P D → Partition → Action S E Snapshot) : Action S E Snapshot :=
  let view := project capture
  let complete := fun part => own view part
  bind (discover capture) (fun result => bind (certify result) complete)

-- No success-only hypothesis: errors, their order and final state are equal.
theorem handoff_exact (capture : Capture P D Storage)
    (discover : Capture P D Storage → Action S E Result)
    (certify : Result → Action S E Partition)
    (own : View P D → Partition → Action S E Snapshot) :
    before capture discover certify own = after capture discover certify own := rfl

#print axioms handoff_exact
#print axioms projection_ignores_payload
end GraphColdHandoff
