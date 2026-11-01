import LeanPoo.Object.SlotObservation
import LeanPoo.Object.Instantiation

/-! Finite observation-scope controls for collection preparation. Host dynamic
binding, callback termination and physical GC remain executable obligations. -/
open LeanPoo.Object

/-- Owned public cells can change without erasing an active receiver/slot key. -/
example : guardSlot
    (guardKeys (fun id => if id = 10 then (0, "edited") else ((7 : Nat), "value")) [0])
    (7, "value") (fun _ => .ok (99 : Nat)) = .error "cyclic slot" := by simp [guardSlot, guardKeys]

/-- Without pair separation, changing a reported cell can bypass cycle refusal. -/
example : guardSlot (guardKeys (fun _ => (0, "edited")) [0]) ((7 : Nat), "value")
    (fun _ => .ok (99 : Nat)) = .ok 99 := by simp [guardSlot, guardKeys]

/-- The public report keeps the original occurrence order, including repetition. -/
example : cycleDiagnostic ([(7, "b"), (7, "a")] : List (Nat × String)) (7, "a") =
    [(7, "a"), (7, "b"), (7, "a")] := rfl

/-- Depth two copies three diagnostic pairs and three outer cells, only on error. -/
example : cycleDiagnosticCells true 2 = 6 ∧ cycleDiagnosticCells false 2 = 0 := by decide

/-- A shared capture frame and ordered prechecks survive nested observers. -/
example :
    let initial : ReadScope Nat String String := ⟨some 17, ["approval"], ["current"]⟩
    let nested := observeReadScope (observeReadScope initial "source" (some "source-current"))
      "converter" (some "converter-current")
    unpackReadScope (packReadScope nested) =
      ⟨some 17, ["converter", "source", "approval"],
        ["converter-current", "source-current", "current"]⟩ := by
  dsimp only
  rw [unpackReadScope_pack]
  rfl

/-- A refusal keeps its original payload and the caller's entire lexical scope. -/
example (caller scope : ReadScope Nat (Nat → Nat) String) (cause : List String) :
    ((fun (_ : ReadScope Nat (Nat → Nat) String) =>
        (Except.error cause : Except (List String) Nat))
      (unpackReadScope (packReadScope scope)), caller) =
      (Except.error cause, caller) := by
  exact readScope_consumer caller scope (fun _ => Except.error cause)

/-- The capture-only representation contains the same frame, without a scope
record allocation; allocation of that original frame is still required. -/
example (frame : Nat) :
    packReadScope (captureReadScope (emptyReadScope : ReadScope Nat String String) frame) =
      some (.inl frame) := captureReadScope_frameOnly frame

/-- The universal bound charges every capture premium under explicit prices. -/
example : 100 * 4 + 30 * (4 + 1 + 2 * 1) + 5 * (4 + 1 + 2 * 1 + 2) ≤
    3 * (100 * 3) + 2 * (30 * 4) + 5 * (4 + 1 + 2 * 1 + 2) :=
  readScope_cost_bound 100 30 5 4 3 1 1 2 (by decide) (by decide)

/-- In this finite trace the removed operations also pay the capture premium. -/
example : 100 * 4 + 30 * (4 + 1 + 2 * 1) + 5 * (4 + 1 + 2 * 1 + 2) ≤
    3 * (100 * 3) + 2 * (30 * 4) := by decide

/-- Expensive context preparation defeats an unconditional gain, even when
both primitive-price hypotheses of the universal bound hold. -/
example : ¬ (1 * 4 + 0 * (4 + 1 + 2 * 1) + 100 * (4 + 1 + 2 * 1 + 50) ≤
    3 * (1 * 3) + 2 * (0 * 4)) := by decide
