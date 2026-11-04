import LeanPoo.Object.CacheInvalidation
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

/-- Nested recording retains duplicate parent roots without changing callbacks. -/
example : (recordCapturedReads (⟨some [1], [7], [8]⟩ : ReadScope (List Nat) Nat Nat)
    [2, 2] (· ++ ·)).frame = some [1, 2, 2] := rfl

/-- An existing unique-root collector retains its own identity policy. -/
example : (recordCapturedReads (⟨some [1], [7], [8]⟩ : ReadScope (List Nat) Nat Nat)
    [2, 2] (fun before roots => (before ++ roots).eraseDups)).frame = some [1, 2] := by decide

/-- A diamond joins at shared, then a late edge closes a cycle back to root. -/
def currentInvalidationChildren (owner : String) : List (String × Nat) :=
  if owner = "root" then [("left", 10), ("right", 20)] else
  if owner = "left" ∨ owner = "right" then [("shared", 30)] else
  if owner = "shared" then [("late", 40)] else
  if owner = "late" then [("root", 0)] else []

/-- Identity stamps distinguish live states even when revision counters agree. -/
def preparedInvalidationState (includeLate : Bool) (owner : String) : Option Nat :=
  if owner = "root" then some 0 else
  if owner = "left" then some 10 else
  if owner = "right" then some 20 else
  if owner = "shared" then some 30 else
  if owner = "late" ∧ includeLate then some 40 else none

/-- A completed earlier subtree cannot silently omit its new descendant. -/
example : invalidationClosureReady ["shared", "right", "left", "root"]
    (preparedInvalidationState false) currentInvalidationChildren = false := by
  simp [invalidationClosureReady, preparedInvalidationState, currentInvalidationChildren]

/-- Fresh traversal includes the late shared dependency and accepts the cycle. -/
example : checkedInvalidationClosure
    (.ok (["late", "shared", "right", "left", "root"], preparedInvalidationState true))
    currentInvalidationChildren false = .ok ["late", "shared", "right", "left", "root"] := by
  simp [checkedInvalidationClosure, invalidationClosureReady, preparedInvalidationState,
    currentInvalidationChildren, bind, Except.bind]

/-- The same owner with a replacement state is not covered by an older visit. -/
example : invalidationClosureReady ["late", "shared", "right", "left", "root"]
    (preparedInvalidationState true)
    (fun owner => if owner = "shared" then [("late", 41)] else currentInvalidationChildren owner) = false := by
  simp [invalidationClosureReady, preparedInvalidationState, currentInvalidationChildren]

/-- Original false refusal outranks an unclosed current graph. -/
example : checkedInvalidationClosure
    (.error false : Except Bool (List String × (String → Option Nat)))
    currentInvalidationChildren true = .error false := rfl

/-- Closure refusal cannot invoke a clear or replace a retained Function cache. -/
example (old : Nat → Nat) : publishEdit old
    ((checkedInvalidationClosure
      (.ok (["shared", "right", "left", "root"], preparedInvalidationState false))
      currentInvalidationChildren "changed").map (fun _ => fun value => value + 1)) = old := by
  simp [checkedInvalidationClosure, invalidationClosureReady, preparedInvalidationState,
    currentInvalidationChildren, publishEdit, Except.map, bind, Except.bind]

/-- Five owners and six current edges require eleven logical validation visits. -/
example : invalidationClosureWork ["late", "shared", "right", "left", "root"]
    currentInvalidationChildren = 11 := by
  simp [invalidationClosureWork, currentInvalidationChildren]

/-- An inner observer retains an edited key while the outer observer and the
structural query both keep the original name. -/
example : checkDemand ["presence", "port"]
    ([fun _ trace => .ok (trace ++ [["presence", "missing"]]),
      fun key trace => .ok (trace ++ [key])] :
      List (List String → List (List String) → Except String (List (List String))))
    [] = .ok (["presence", "port"], [["presence", "missing"], ["presence", "port"]]) := rfl

/-- A retained service presence record is replayed twice. The first consumer
renames its copy, while the second still receives the originally issued name. -/
example :
    let read : IssuedReadKey String := ⟨["presence", "port"], ["presence", "port"], 7⟩
    let first := read.deliver (fun _ _ => [["presence", "missing"]]) []
    let second := first.1.deliver (fun key trace => trace ++ [key]) first.2
    second.2 = [["presence", "missing"], ["presence", "port"]] ∧
      second.1.current 7 ∧ ¬ second.1.current 8 := by
  simp [IssuedReadKey.deliver, IssuedReadKey.current]
