import LeanPoo.Functional.RecursiveStaging

/-! Explicit preparation against the observed current catalog. Preparation returns
the pure reconfiguration action corresponding to Scheme's three edit lists. It
can fail, and does not reserve a head or rebase any previously returned request.
This advances generalized-prototype future work under the staging premises. -/
namespace LeanPoo.Functional.RecursiveRestaging
open RecursiveStaging

/-- Prepare edits from the actual current value, then capture its identity/stamp.
Neither the prepared closure nor any old pending request runs during preparation. -/
def restage (current : State Value) (stamp : Stamp)
    (prepare : Value → Except Error (Value → Except Error Value)) :
    Except Error (Request Value Stamp Error) := do
  let action ← prepare current.value
  return stage current stamp action

/-- Failed edit preparation produces no request or new installed state. -/
theorem preparation_failure (current : State Value) (stamp : Stamp)
    (prepare : Value → Except Error (Value → Except Error Value)) (cause : Error)
    (failed : prepare current.value = .error cause) :
    restage current stamp prepare = .error cause := by
  simp only [restage,failed]
  rfl

/-- Preparation binds the new request to the observed snapshot and watched stamp. -/
theorem prepared_request (current : State Value) (stamp : Stamp)
    (prepare : Value → Except Error (Value → Except Error Value))
    (action : Value → Except Error Value) (ready : prepare current.value = .ok action) :
    restage current stamp prepare = .ok (stage current stamp action) := by
  simp only [restage,ready]
  rfl

/-- Publishing successful preparation uses the current value, not an earlier base. -/
theorem prepared_publish [DecidableEq Stamp] (current : State Value) (stamp : Stamp)
    (prepare : Value → Except Error (Value → Except Error Value))
    (request : Request Value Stamp Error) (action : Value → Except Error Value)
    (next : Value) (ready : prepare current.value = .ok action)
    (captured : restage current stamp prepare = .ok request)
    (closed : action current.value = .ok next) :
    publish request current stamp = (.ok (),⟨current.revision+1,next⟩) := by
  rw [prepared_request current stamp prepare action ready] at captured
  cases captured
  exact restaged_success current stamp action next closed

/-- Serially observed attempts preserve their individual refusal/success outcomes.
This describes an order of attempts, not concurrent host installation. -/
def attempts [DecidableEq Stamp] (requests : List (Request Value Stamp Error))
    (current : State Value) (stamp : Stamp) :
    List (Except (Failure Error) Unit) × State Value :=
  match requests with
  | [] => ([],current)
  | request :: rest =>
    let (outcome,next) := publish request current stamp
    let (outcomes,last) := attempts rest next stamp
    (outcome :: outcomes,last)

/-- Late admission failure leaves a freshly prepared sibling usable. Neither
request needs to consume or mutate the observed state to report its result. -/
theorem refused_then_retry [DecidableEq Stamp] (current : State Value) (stamp : Stamp)
    (failed action : Value → Except Error Value) (cause : Error) (next : Value)
    (refused : failed current.value = .error cause) (closed : action current.value = .ok next) :
    attempts [stage current stamp failed,stage current stamp action] current stamp =
      ([.error (.rejected cause),.ok ()],⟨current.revision+1,next⟩) := by
  simp [attempts,closure_failure current stamp failed cause refused,
    restaged_success current stamp action next closed]

/-- Any number of obsolete attempts leaves the exact current graph untouched. -/
theorem obsolete_attempts [DecidableEq Stamp] (requests : List (Request Value Stamp Error))
    (current : State Value) (stamp : Stamp)
    (older : ∀ request ∈ requests, request.expected < current.revision) :
    attempts requests current stamp = (requests.map (fun _ => .error .stale),current) := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
    have first := older request (by simp)
    have tail := ih (fun item member => older item (by simp [member]))
    simp [attempts,older_round_stale request current stamp first,tail]

/-- Old requests may remain pending on BOTH sides of a fresh successful commit.
Their attempts cannot consume or invalidate the newly prepared request. -/
theorem interleaved_publish [DecidableEq Stamp]
    (before after : List (Request Value Stamp Error)) (current : State Value)
    (stamp : Stamp) (action : Value → Except Error Value) (next : Value)
    (oldBefore : ∀ request ∈ before, request.expected < current.revision)
    (oldAfter : ∀ request ∈ after, request.expected ≤ current.revision)
    (closed : action current.value = .ok next) :
    attempts (before ++ stage current stamp action :: after) current stamp =
      (before.map (fun _ => .error .stale) ++ .ok () :: after.map (fun _ => .error .stale),
       ⟨current.revision+1,next⟩) := by
  induction before with
  | nil =>
    have tail := obsolete_attempts after (⟨current.revision+1,next⟩ : State Value) stamp
      (fun request member => by
        have := oldAfter request member
        dsimp
        omega)
    simp [attempts,restaged_success current stamp action next closed,tail]
  | cons request rest ih =>
    have first := older_round_stale request current stamp (oldBefore request (by simp))
    have tail := ih (fun item member => oldBefore item (by simp [member]))
    simp [attempts,first,tail]

end LeanPoo.Functional.RecursiveRestaging
