-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.ReadRouteRuns

inductive Refusal where
  | issuance | key | route | stale
  deriving DecidableEq, Repr

structure Read where
  receiver : Nat
  bootstrap : Bool
  key : Nat

structure Window where
  issue : Read → Except Refusal Unit
  key : Read → Except Refusal Unit
  route : Nat → Except Refusal Unit
  live : Read → Except Refusal Unit

def current (window : Window) (read : Read) : Except Refusal Unit := do
  window.issue read
  window.key read
  let _ ← (if !read.bootstrap then window.route read.receiver else .ok ())
  window.live read

def serial (window : Window) : List Read → Except Refusal Unit
  | [] => .ok ()
  | read :: tail => (current window read).bind fun _ => serial window tail

-- A bootstrap key never checks the receiver's value-table route and cannot
-- establish a route for its successor.
def routeNeeded (last : Option Nat) (read : Read) : Bool :=
  !read.bootstrap && last != some read.receiver

def nextReceiver (last : Option Nat) (read : Read) : Option Nat :=
  if read.bootstrap then last else some read.receiver

def runs (window : Window) : List Read → Option Nat → Except Refusal Unit
  | [], _ => .ok ()
  | read :: tail, last => do
    window.issue read
    window.key read
    let _ ← (if routeNeeded last read then window.route read.receiver else .ok ())
    window.live read
    runs window tail (nextReceiver last read)

def Known (window : Window) (last : Option Nat) : Prop :=
  ∀ receiver, last = some receiver → window.route receiver = .ok ()

theorem runs_eq_serial (window : Window) (reads : List Read) (last : Option Nat)
    (known : Known window last) : runs window reads last = serial window reads := by
  induction reads generalizing last with
  | nil => rfl
  | cons read tail ih =>
    have agree : (if routeNeeded last read then window.route read.receiver else .ok ()) =
        (if !read.bootstrap then window.route read.receiver else .ok ()) := by
      by_cases previous : last = some read.receiver
      · simp [routeNeeded, previous, known _ previous]
      · cases bootstrap : read.bootstrap <;> simp [routeNeeded, bootstrap, previous]
    simp only [runs, serial, current, agree]
    cases window.issue read <;> simp only [Except.bind, Bind.bind]
    case ok _ =>
      cases window.key read <;> try rfl
      case ok _ =>
        cases bootstrap : read.bootstrap
        · simp only [Bool.not_false, ite_true]
          cases routed : window.route read.receiver <;> try rfl
          case ok _ =>
            cases window.live read <;> try rfl
            case ok _ =>
              apply ih
              intro receiver same
              simp [nextReceiver, bootstrap] at same
              exact same ▸ routed
        · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases window.live read <;> try rfl
          case ok _ => exact ih _ (by simpa [nextReceiver, bootstrap] using known)

theorem fresh_window (window : Window) (reads : List Read) :
    runs window reads none = serial window reads :=
  runs_eq_serial window reads none (by simp [Known])

-- The callback may return an entirely different Window, even when the
-- original read roster is reused. The return check starts with no route.
def checkpoint (validate : Window → List Read → Except Refusal Unit)
    (before : Window) (reads : List Read) (action : Unit → Window × Nat) :
    Except Refusal Nat := do
  validate before reads
  let (after, value) := action ()
  validate after reads
  pure value

theorem checkpoint_preserves_refusals (before : Window) (reads : List Read)
    (action : Unit → Window × Nat) :
    checkpoint (fun window reads => runs window reads none) before reads action =
      checkpoint serial before reads action := by
  simp [checkpoint, fresh_window]

def routeRequests : List Read → Option Nat → Nat
  | [], _ => 0
  | read :: tail, last =>
    (routeNeeded last read).toNat + routeRequests tail (nextReceiver last read)

theorem route_requests_bounded (reads : List Read) (last : Option Nat) :
    routeRequests reads last ≤ reads.length := by
  induction reads generalizing last with
  | nil => simp [routeRequests]
  | cons read rest ih =>
    have remaining := ih (nextReceiver last read)
    cases needed : routeNeeded last read <;> simp [routeRequests, needed] <;> omega

#guard routeRequests (List.replicate 10000 ⟨0, false, 1⟩) none == 1
#guard routeRequests [⟨0, true, 1⟩, ⟨0, false, 1⟩, ⟨0, false, 2⟩,
                      ⟨1, false, 1⟩, ⟨0, false, 3⟩] none == 3

/-- A detached traversal marks the first non-bootstrap read for each receiver.
These flags depend on structure alone and can be reused in different windows. -/
def markRoutes : List Read → List Nat → List (Read × Bool)
  | [], _ => []
  | read :: tail, seen =>
    let first := !read.bootstrap && !seen.contains read.receiver
    (read, first) :: markRoutes tail (if first then read.receiver :: seen else seen)

def markedCurrent (window : Window) (read : Read) (first : Bool) : Except Refusal Unit := do
  window.issue read
  window.key read
  let _ ← if first then window.route read.receiver else .ok ()
  window.live read

def marked (window : Window) : List (Read × Bool) → Except Refusal Unit
  | [] => .ok ()
  | (read, first) :: tail => (markedCurrent window read first).bind fun _ => marked window tail

theorem marked_eq_serial (window : Window) (reads : List Read) (seen : List Nat)
    (known : ∀ receiver ∈ seen, window.route receiver = .ok ()) :
    marked window (markRoutes reads seen) = serial window reads := by
  induction reads generalizing seen with
  | nil => rfl
  | cons read tail ih =>
    cases bootstrap : read.bootstrap
    · by_cases visited : read.receiver ∈ seen
      · simp [markRoutes, bootstrap, visited, marked, markedCurrent, serial, current,
          known _ visited, ih seen known]
      · simp [markRoutes, bootstrap, visited, marked, markedCurrent, serial, current]
        cases window.issue read <;> simp only [Except.bind, Bind.bind]
        case ok _ =>
          cases window.key read <;> try rfl
          case ok _ =>
            cases routed : window.route read.receiver <;> try rfl
            case ok _ =>
              cases window.live read <;> try rfl
              case ok _ =>
                apply ih
                intro receiver member
                rcases List.mem_cons.mp member with same | old
                · simpa [same] using routed
                · exact known receiver old
    · simp [markRoutes, bootstrap, marked, markedCurrent, serial, current, ih seen known]

theorem marked_checkpoint_eq_serial (before : Window) (reads : List Read)
    (action : Unit → Window × Nat) :
    checkpoint (fun window reads => marked window (markRoutes reads [])) before reads action =
      checkpoint serial before reads action := by
  simp [checkpoint, marked_eq_serial]

/-- Native acquisition authenticates the complete traversal before checking
any receiver route. Keeping this phase outside the sweep preserves refusals
when a later record is unissued but an earlier receiver route is invalid. -/
def preflight (window : Window) : List Read → Except Refusal Unit
  | [] => .ok ()
  | read :: tail => (window.issue read).bind fun _ => preflight window tail

def issuedAt (window : Window) (reads : List Read) : Prop :=
  ∀ read ∈ reads, window.issue read = .ok ()

theorem preflight_ok_iff (window : Window) (reads : List Read) :
    preflight window reads = .ok () ↔ issuedAt window reads := by
  induction reads with
  | nil => simp [preflight, issuedAt]
  | cons read tail ih =>
    cases checked : window.issue read <;>
      simp [preflight, issuedAt, checked, ih, Except.bind]

/-- Only the actual successful preflight in this same pure window permits
omitting duplicate issuance checks. This is not a retained approval. -/
def preissued (window : Window) : Window :=
  { window with issue := fun _ => .ok () }

theorem serial_preissued_eq (window : Window) (reads : List Read)
    (issued : issuedAt window reads) :
    serial (preissued window) reads = serial window reads := by
  induction reads with
  | nil => rfl
  | cons read tail ih =>
    have head := issued read (by simp)
    have rest : issuedAt window tail := fun child member => issued child (by simp [member])
    simp only [serial]
    rw [ih rest]
    simp [current, preissued, head]

def nativeFixed (window : Window) (reads : List Read) : Except Refusal Unit := do
  preflight window reads
  serial (preissued window) reads

def nativeMarked (window : Window) (reads : List Read) : Except Refusal Unit := do
  preflight window reads
  marked (preissued window) (markRoutes reads [])

theorem native_fixed_refusals_exact (window : Window) (reads : List Read) :
    nativeMarked window reads = nativeFixed window reads := by
  simp [nativeMarked, nativeFixed, marked_eq_serial]

theorem native_preflight_skip_exact (window : Window) (reads : List Read) :
    nativeFixed window reads = (do preflight window reads; serial window reads) := by
  unfold nativeFixed
  cases result : preflight window reads with
  | error cause => rfl
  | ok value =>
    cases value
    simpa only [Except.bind, Bind.bind] using
      serial_preissued_eq window reads ((preflight_ok_iff window reads).mp result)

/-- An action may change every guard without changing the traversal. Native
callback return therefore uses fresh issuance, key, route and live checks. -/
def nativeCallback (returnCheck : Window → List Read → Except Refusal Unit)
    (before : Window) (reads : List Read) (action : Unit → Window × Nat) :
    Except Refusal Nat := do
  preflight before reads
  serial before reads
  let (after, value) := action ()
  returnCheck after reads
  pure value

theorem native_callback_return_exact (before : Window) (reads : List Read)
    (action : Unit → Window × Nat) :
    nativeCallback (fun window reads => marked window (markRoutes reads [])) before reads action =
      nativeCallback serial before reads action := by
  simp [nativeCallback, marked_eq_serial]

/-- Entry and return independently validate the structural route markers and
repeat issuance. No successful validation crosses the author action. -/
def nativeMarkedCallback (before : Window) (reads : List Read)
    (action : Unit → Window × Nat) : Except Refusal Nat := do
  preflight before reads
  marked before (markRoutes reads [])
  let (after, value) := action ()
  marked after (markRoutes reads [])
  pure value

theorem native_marked_callback_exact (before : Window) (reads : List Read)
    (action : Unit → Window × Nat) :
    nativeMarkedCallback before reads action = nativeCallback serial before reads action := by
  simp [nativeMarkedCallback, nativeCallback, marked_eq_serial]

private def competingRefusals : Window where
  issue read := if read.key = 1 then .error .issuance else .ok ()
  key _ := .ok ()
  route _ := .error .route
  live _ := .ok ()

-- Interleaving issuance with route checking would incorrectly prefer route.
#guard match nativeFixed competingRefusals [⟨0, false, 0⟩, ⟨1, false, 1⟩] with
  | .error .issuance => true | _ => false
#guard match serial competingRefusals [⟨0, false, 0⟩, ⟨1, false, 1⟩] with
  | .error .route => true | _ => false
#guard match nativeMarked competingRefusals [⟨0, false, 0⟩, ⟨1, false, 1⟩] with
  | .error .issuance => true | _ => false

def routeMarkers (reads : List Read) (seen : List Nat) : List Nat :=
  (markRoutes reads seen).filterMap fun (read, first) => if first then some read.receiver else none

/-- The closed sweep authenticates at most one route per receiver. The
marker index has no duplicate receiver and never marks an already seen one. -/
theorem route_markers_unique (reads : List Read) (seen : List Nat) :
    (routeMarkers reads seen).Nodup ∧ ∀ receiver ∈ routeMarkers reads seen, receiver ∉ seen := by
  induction reads generalizing seen with
  | nil => simp [routeMarkers, markRoutes]
  | cons read tail ih =>
    cases bootstrap : read.bootstrap
    · by_cases visited : read.receiver ∈ seen
      · simpa [routeMarkers, markRoutes, bootstrap, visited] using ih seen
      · have next := ih (read.receiver :: seen)
        have separated : read.receiver ∉ routeMarkers tail (read.receiver :: seen) := by
          intro found
          exact next.2 _ found (.head _)
        have marked : routeMarkers (read :: tail) seen =
            read.receiver :: routeMarkers tail (read.receiver :: seen) := by
          simp [routeMarkers, markRoutes, bootstrap, visited]
        rw [marked]
        refine ⟨List.nodup_cons.mpr ⟨separated, next.1⟩, ?_⟩
        intro receiver member
        rcases List.mem_cons.mp member with same | later
        · simpa [same] using visited
        · exact fun old => next.2 _ later (.tail _ old)
    · simpa [routeMarkers, markRoutes, bootstrap] using ih seen

#guard (markRoutes [⟨0, true, 1⟩, ⟨1, false, 1⟩, ⟨0, false, 2⟩,
                    ⟨1, false, 3⟩, ⟨0, false, 4⟩] []).map Prod.snd ==
  [false, true, true, false, false]

#guard (routeMarkers ((List.range 512).map fun index => ⟨index % 2, false, index⟩) []).length == 2

end LeanPoo.Object.ReadRouteRuns

