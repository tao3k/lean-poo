-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import LeanPoo.Object.PublishedReadPreorder

namespace LeanPoo.Object.PublishedReadEligibility
open PublishedReadPreorder
open ReadRouteRuns

/-- The reader uses only signed receiver, key, and value facts. Value facts
include identity and the immutable kind of the value, never mutable contents. -/
structure Facts where
  receiver : Nat
  key : Nat
  value : Nat
  pairValue : Bool

inductive Rejection where
  | read (reason : Refusal)
  | ineligible
  deriving DecidableEq, Repr

def check (guard : Nat → Except Rejection Unit) (eligible : Facts → Bool)
    (presented : Nat → Facts) (read : Nat) : Except Rejection Unit :=
  (guard read).bind fun _ =>
    if eligible (presented read) then .ok () else .error .ineligible

/-- Only a successful native guard authorizes reuse. A changed presentation or
a stale live value still fails, at the same record and before any later row. -/
theorem replay_eq_checked
    (guard : Nat → Except Rejection Unit) (eligible : Facts → Bool)
    (signed presented : Nat → Facts) (rows : List Nat)
    (authenticated : ∀ r, guard r = .ok () → presented r = signed r)
    (admitted : ∀ r ∈ rows, eligible (signed r) = true) :
    replay guard rows = replay (check guard eligible presented) rows := by
  induction rows with
  | nil => rfl
  | cons r rest ih =>
    have tail : ∀ s ∈ rest, eligible (signed s) = true := by
      intro s member
      exact admitted s (List.mem_cons_of_mem _ member)
    cases h : guard r with
    | error reason => simp [replay, check, h, Except.bind]
    | ok value =>
      cases value
      have valid : eligible (presented r) = true := by
        rw [authenticated r h]
        exact admitted r (by simp)
      simpa [replay, check, h, valid, Except.bind] using ih tail

/-- A publication shares the fixed classification over every boundary.
Each window supplies its own native guard and its own authentication premise. -/
theorem replay_windows_eq_checked
    {Window : Type} (windows : List Window)
    (guard : Window → Nat → Except Rejection Unit) (eligible : Facts → Bool)
    (signed : Nat → Facts) (presented : Window → Nat → Facts) (rows : List Nat)
    (authenticated : ∀ w r, guard w r = .ok () → presented w r = signed r)
    (admitted : ∀ r ∈ rows, eligible (signed r) = true) :
    windows.map (fun w => replay (guard w) rows) =
      windows.map (fun w => replay (check (guard w) eligible (presented w)) rows) :=
  List.map_congr_left (fun w _ =>
    replay_eq_checked (guard w) eligible signed (presented w) rows (authenticated w) admitted)

private def accepted (_ : Nat) : Facts := ⟨1, 2, 3, false⟩
private def stock (f : Facts) : Bool := f.value == 3 && !f.pairValue
private def current (_ : Nat) : Except Rejection Unit := .ok ()
private def changed (r : Nat) : Except Rejection Unit :=
  if r = 1 then .error (.read .stale) else .error (.read .issuance)

-- A changed validator in live storage and a later unissued record both fail.
-- Reusing the verdict across boundaries would incorrectly admit this window.
#guard match replay current [1, 2] with
  | .ok () => true | _ => false
#guard match replay changed [1, 2] with
  | .error (.read .stale) => true | _ => false
#guard match replay (check changed stock accepted) [1, 2] with
  | .error (.read .stale) => true | _ => false
#guard match replay changed [2] with
  | .error (.read .issuance) => true | _ => false
-- A successful live guard alone cannot publish an unsupported validator.
#guard match replay (check current stock (fun _ => ⟨1, 2, 4, false⟩)) [1] with
  | .error .ineligible => true | _ => false

end LeanPoo.Object.PublishedReadEligibility
