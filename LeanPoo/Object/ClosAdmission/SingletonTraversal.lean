-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ClosAdmission.SingletonApplicability

namespace LeanPoo.Object.ClosAdmission.SingletonTraversal

open IndexedRank (Attempt)
open SingletonApplicability (Result check collect)

inductive TailTiming where
  | beforeRead
  | afterRead

variable {Row Rank State Error Event : Type}

/-- A read may change which row is reachable from the current pair.
    Once the cursor is exhausted, the remaining budget contributes only
    neutral successes and produces no reads. -/
def visit (timing : TailTiming) (neutral : Rank) (step : Row → Attempt State Error Event Rank)
    (next : Row → State → Option Row) (_ : Unit) :
    Attempt (Option Row × State) Error Event Rank :=
  fun (cursor, state) =>
    match cursor with
    | none => (.ok (some neutral), (none, state), [])
    | some row =>
      match step row state with
      | (.error refusal, after, reads) => (.error refusal, (none, after), reads)
      | (.ok distance, after, reads) =>
        let following := next row (match timing with
          | .beforeRead => state
          | .afterRead => after)
        (.ok distance, (following, after), reads)

private def selected (result : Result (List (Option Rank)) State Error Event) :
    Result Bool State Error Event :=
  let (outcome, after, reads) := result
  (outcome.map (List.all · Option.isSome), after, reads)

/-- For proper equal-length lists the pinned AOT map reads tails after each
    effect. The unequal-length library path saves them before the effect.
    Fuse only the former case and retain the complete legacy fallback. -/
theorem guard_preserves_live_traversal
    (step : Row → Attempt State Error Event Rank) (next : Row → State → Option Row)
    (neutral : Rank) (rows : List Unit) (cursor : Option Row × State)
    (sameProperLength : Bool) :
    (if sameProperLength then
       check (visit .afterRead neutral step next) rows cursor true
     else
       selected (collect (visit .beforeRead neutral step next) rows cursor)) =
    selected (collect (visit
      (if sameProperLength then .afterRead else .beforeRead) neutral step next) rows cursor) := by
  cases sameProperLength
  · rfl
  · simpa [selected] using
      (SingletonApplicability.one_pass_preserves_applicability
        (visit .afterRead neutral step next) rows cursor true)

/-- Fusion can also cross the library path if a successful read preserves
    each pending tail, including across callbacks. -/
theorem stable_tails_permit_fusion
    (step : Row → Attempt State Error Event Rank) (next : Row → State → Option Row)
    (neutral : Rank) (rows : List Unit) (cursor : Option Row × State)
    (stable : ∀ row state distance after reads,
      step row state = (.ok distance, after, reads) → next row state = next row after) :
    check (visit .afterRead neutral step next) rows cursor true =
      selected (collect (visit .beforeRead neutral step next) rows cursor) := by
  have sameVisit : visit .beforeRead neutral step next = visit .afterRead neutral step next := by
    funext token pair
    obtain ⟨row, state⟩ := pair
    cases row with
    | none => rfl
    | some row =>
      rcases observed : step row state with ⟨outcome, after, reads⟩
      cases outcome with
      | error _ => simp [visit, observed]
      | ok distance => simp [visit, observed, stable row state distance after reads observed]
  rw [sameVisit]
  simpa [selected] using
    (SingletonApplicability.one_pass_preserves_applicability
      (visit .afterRead neutral step next) rows cursor true)

private def rewire (row : Nat) : Attempt Bool Unit Nat Unit :=
  fun _ => (.ok (some ()), true, [row])

private def tailAfterRewire (row : Nat) (rewired : Bool) : Option Nat :=
  if row == 0 && !rewired then some 1 else none

/-- An effect can shorten the exposed argument spine. The saved tail still
    requires the second read on the original unequal-length path. -/
example :
    (check (visit .beforeRead () rewire tailAfterRewire)
      [(), ()] (some 0, false) true).2.2 = [0, 1] ∧
    (check (visit .afterRead () rewire tailAfterRewire)
      [(), ()] (some 0, false) true).2.2 = [0] := by decide

/-- The compiler first scans for two proper lists of equal length. In its
    inline row loop a later non-pair ends traversal, even when an earlier
    callback rewired the cursor. The library's saved-tail loop is distinct. -/
theorem inline_exhaustion_reads_no_more
    (step : Row → Attempt State Error Event Rank)
    (next : Row → State → Option Row) (neutral : Rank)
    (budget : List Unit) (state : State) (applicable : Bool) :
    check (visit .afterRead neutral step next) budget (none, state) applicable =
      (.ok applicable, (none, state), []) := by
  induction budget with
  | nil => rfl
  | cons row later ih =>
    simp [check, visit, ih]

/-- Stock arm64 Gambit map with two nonempty lists. The rest list and its
    wrapper contribute two pairs. Each row contributes two next-list pairs,
    two apply-argument pairs and one distance pair. If the right list is
    longer, its last tail probe allocates one more pair. -/
def fallbackPairs (visited : Nat) (longerArguments : Bool) : Nat :=
  2 + 5 * visited + (if longerArguments then 1 else 0)

/-- No-GC batch endpoints with a common stack depth. The pinned counter
    charges two semispace words per movable word. One pair occupies three
    arm64 words and the fused flag box occupies two. -/
theorem stock_shared_initialize_counter :
    ((fallbackPairs 2 true * 3 - 2) * 8 * 2 : Nat) = 592 := by decide

/-- A stock width update ranks reinitialize-instance and shared-initialize.
    Both argument lists have extras. This accounts for the library map
    allocations eliminated by saved tails, prior to rank materialization. -/
theorem stock_reinitialize_map_counter :
    ((fallbackPairs 1 true + fallbackPairs 2 true) * 3 * 8 * 2 : Nat) = 1008 := by decide

end LeanPoo.Object.ClosAdmission.SingletonTraversal
