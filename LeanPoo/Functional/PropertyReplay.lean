import LeanPoo.Functional.PropertySequences

/-! Portable-copy preparation after the container root has spent its node.
Child costs include their own root and any nested/compact payload units. Accurate
cost profiles and host vector/port behavior are premises, not verified here. -/
namespace LeanPoo.Functional.PropertyTesting

/-- A vector needs room for every child root and, unless empty, a child depth. -/
def replayVectorReady (remaining depth width : Nat) : Bool :=
  decide (width ≤ remaining ∧ (width = 0 ∨ 0 < depth))

/-- Admission precedes destination allocation and child inspection. The action
models those host operations; rejected preparation does not evaluate it. -/
def admitReplayVector (remaining depth width : Nat) (allocate : Nat → Except Cause Value) :
    Except (Option Cause) Value :=
  if replayVectorReady remaining depth width then (allocate width).mapError some else .error none

/-- A single remaining allowance is threaded through successive child copies. -/
def replayCopyCosts : List Nat → Nat → Option Nat
  | [], remaining => some remaining
  | cost :: rest, remaining =>
    if cost ≤ remaining then replayCopyCosts rest (remaining - cost) else none

/-- Successful copying accounts for every compact/nested payload unit exactly. -/
theorem replayCopyCosts_accounting (costs : List Nat) (remaining after : Nat)
    (success : replayCopyCosts costs remaining = some after) :
    after + costs.sum = remaining := by
  induction costs generalizing remaining with
  | nil => simpa [replayCopyCosts] using success.symm
  | cons cost rest ih =>
    by_cases fits : cost ≤ remaining
    · simp [replayCopyCosts, fits] at success
      have charged := ih (remaining - cost) success
      simp only [List.sum_cons]
      omega
    · simp [replayCopyCosts, fits] at success

/-- Every child has at least its own root: width is a necessary lower bound. -/
theorem replayCopyCosts_minimum (costs : List Nat) :
    (∀ cost ∈ costs, 0 < cost) → costs.length ≤ costs.sum := by
  induction costs with
  | nil => simp
  | cons cost rest ih =>
    intro positive
    have head := positive cost (by simp)
    have tail := ih (fun value member => positive value (by simp [member]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- Width preflight cannot exclude a feasible positive-cost child profile. -/
theorem replayVectorReady_necessary (costs : List Nat) (remaining after depth : Nat)
    (positive : ∀ cost ∈ costs, 0 < cost)
    (success : replayCopyCosts costs remaining = some after) :
    replayVectorReady remaining (depth + 1) costs.length = true := by
  have charged := replayCopyCosts_accounting costs remaining after success
  have minimum := replayCopyCosts_minimum costs positive
  have width : costs.length ≤ remaining := by omega
  simp [replayVectorReady, width]

/-- Oversized vectors refuse before allocating or visiting even their first child. -/
theorem admitReplayVector_wide (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (oversized : remaining < width) :
    admitReplayVector remaining depth width allocate = .error none := by
  simp [admitReplayVector, replayVectorReady, Nat.not_le.mpr oversized]

/-- A nonempty vector cannot allocate a destination at exhausted child depth. -/
theorem admitReplayVector_depth (remaining width : Nat)
    (allocate : Nat → Except Cause Value) (nonempty : width ≠ 0) :
    admitReplayVector remaining 0 width allocate = .error none := by
  simp [admitReplayVector, replayVectorReady, nonempty]

/-- Empty vectors remain data at depth zero and require no child-node credits. -/
theorem admitReplayVector_empty (remaining : Nat) (allocate : Nat → Except Cause Value) :
    admitReplayVector remaining 0 0 allocate = (allocate 0).mapError some := by
  simp [admitReplayVector, replayVectorReady]

/-- Feasible preparation preserves the exact action, including its exception. -/
theorem admitReplayVector_preserves (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (ready : replayVectorReady remaining depth width = true) :
    admitReplayVector remaining depth width allocate = (allocate width).mapError some := by
  simp [admitReplayVector, ready]

/-- Any admitted vector destination has width bounded by the remaining credits. -/
theorem admitReplayVector_width (remaining depth width : Nat)
    (allocate : Nat → Except Cause Value) (value : Value)
    (success : admitReplayVector remaining depth width allocate = .ok value) :
    width ≤ remaining := by
  by_cases ready : replayVectorReady remaining depth width = true
  · have bounds : width ≤ remaining ∧ (width = 0 ∨ 0 < depth) := by
      simpa [replayVectorReady] using ready
    exact bounds.1
  · simp [admitReplayVector, ready] at success

end LeanPoo.Functional.PropertyTesting
