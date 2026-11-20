-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.ReadRouteRuns

namespace LeanPoo.Object.PublishedReadPreorder
open ReadRouteRuns

abbrev Dependencies := Nat → List Nat

/-- Reads are identified by issued record identity. The worklist visits roots
and their signed parents in preorder and keeps each identity's first visit. -/
def preorder (parents : Dependencies) : Nat → List Nat → List Nat → Option (List Nat)
  | _, _, [] => some []
  | 0, _, _ :: _ => none
  | fuel + 1, seen, read :: rest =>
    if read ∈ seen then preorder parents fuel seen rest
    else (preorder parents fuel (read :: seen) (parents read ++ rest)).map (read :: ·)

def rediscover (parents : Dependencies) (check : Nat → Except Error Unit)
    (incomplete : Error) : Nat → List Nat → List Nat → Except Error Unit
  | _, _, [] => .ok ()
  | 0, _, _ :: _ => .error incomplete
  | fuel + 1, seen, read :: rest =>
    if read ∈ seen then rediscover parents check incomplete fuel seen rest
    else (check read).bind fun _ =>
      rediscover parents check incomplete fuel (read :: seen) (parents read ++ rest)

def replay (check : Nat → Except Error Unit) : List Nat → Except Error Unit
  | [] => .ok ()
  | read :: rest => (check read).bind fun _ => replay check rest

/-- Issuance validates the exact signed dependency sequence of every record
that passes a check. A previously issued preorder fixes membership and order
only. Each check still executes, and a refusal prevents any later check. -/
theorem replay_eq_rediscover
    (signed live : Dependencies) (check : Nat → Except Error Unit) (incomplete : Error)
    (coherent : ∀ read, check read = .ok () → live read = signed read)
    (fuel : Nat) (seen roots rows : List Nat)
    (published : preorder signed fuel seen roots = some rows) :
    replay check rows = rediscover live check incomplete fuel seen roots := by
  induction fuel generalizing seen roots rows with
  | zero =>
    cases roots with
    | nil =>
      simp [preorder] at published
      subst rows
      rfl
    | cons head tail => simp [preorder] at published
  | succ fuel ih =>
    cases roots with
    | nil =>
      simp [preorder] at published
      subst rows
      rfl
    | cons read rest =>
      by_cases present : read ∈ seen
      · simp only [preorder, ite_eq_left present] at published
        simpa only [rediscover, ite_eq_left present] using ih seen rest rows published
      · simp only [preorder, ite_eq_right present] at published
        cases finished : preorder signed fuel (read :: seen) (signed read ++ rest) with
        | none => simp [finished] at published
        | some tail =>
          have same : read :: tail = rows := by simpa [finished] using published
          subst rows
          simp only [replay, rediscover, ite_eq_right present]
          cases admitted : check read with
          | error refusal => rfl
          | ok value =>
            cases value
            rw [coherent read admitted]
            exact ih (read :: seen) (signed read ++ rest) tail finished

theorem replay_as_serial (window : Window) (identity : Nat → Read) (rows : List Nat) :
    replay (fun id => current window (identity id)) rows = serial window (rows.map identity) := by
  induction rows with
  | nil => rfl
  | cons id rest ih => simp [replay, serial, ih]

/-- Receiver-route markers also depend only on the published order. Each
window supplies its own issuance, routing and live checks. The marks carry
no previous route verdict and do not share an admission across a callback. -/
theorem marked_replay_eq_rediscover
    (window : Window) (identity : Nat → Read) (signed live : Dependencies)
    (coherent : ∀ id, current window (identity id) = .ok () → live id = signed id)
    (fuel : Nat) (roots rows : List Nat) (published : preorder signed fuel [] roots = some rows) :
    marked window (markRoutes (rows.map identity) []) =
      rediscover live (fun id => current window (identity id)) .issuance fuel [] roots := by
  rw [marked_eq_serial window _ [] (by simp), ← replay_as_serial]
  exact replay_eq_rediscover signed live _ .issuance coherent fuel [] roots rows published

/-- The same schedule may be read after an effect. Each check uses the
window and dependency presentations at its own boundary. -/
theorem before_and_after_eq_rediscover
    (before after : Window) (identity : Nat → Read)
    (signed beforeLive afterLive : Dependencies)
    (beforeCoherent : ∀ id, current before (identity id) = .ok () → beforeLive id = signed id)
    (afterCoherent : ∀ id, current after (identity id) = .ok () → afterLive id = signed id)
    (fuel : Nat) (roots rows : List Nat) (published : preorder signed fuel [] roots = some rows) :
    let schedule := markRoutes (rows.map identity) []
    (marked before schedule, marked after schedule) =
      (rediscover beforeLive (fun id => current before (identity id)) .issuance fuel [] roots,
       rediscover afterLive (fun id => current after (identity id)) .issuance fuel [] roots) := by
  dsimp only
  rw [marked_replay_eq_rediscover before identity signed beforeLive beforeCoherent fuel roots rows published,
      marked_replay_eq_rediscover after identity signed afterLive afterCoherent fuel roots rows published]

private def parents : Dependencies
  | 1 => [3, 2]
  | 2 => [3]
  | _ => []

#guard preorder parents 8 [] [1, 2] == some [1, 3, 2]

private def liveParents : Dependencies
  | 3 => [4]
  | read => parents read

private def authenticate (read : Nat) : Except Refusal Unit :=
  if liveParents read = parents read then .ok () else .error .issuance

-- A change in an admitted parent's dependency spine is rejected even if
-- the caller still holds the published traversal.
#guard match replay authenticate [1, 3, 2] with
  | .error .issuance => true | _ => false
#guard match rediscover liveParents authenticate .stale 8 [] [1, 2] with
  | .error .issuance => true | _ => false

-- Hoisting every issuance check would incorrectly report the later failure first.
private def competingRefusals (read : Nat) : Except Refusal Unit :=
  if read = 1 then .error .stale else .error .issuance

#guard match replay competingRefusals [1, 3, 2] with
  | .error .stale => true | _ => false

end LeanPoo.Object.PublishedReadPreorder
