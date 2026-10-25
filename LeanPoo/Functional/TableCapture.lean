import LeanPoo.Functional.TableRevision

/-! Finite borrowed Option-cell capture. Cells model mutable shells; child values
are opaque stable observations. This does not verify Gambit's heap or deep-copy
mutable leaves. Runtime capture uses the existing Option map and list builder. -/
namespace LeanPoo.Functional.OrderedDictionary

variable {K Cell V E : Type}

/-- Producer-owned optional cells may be reused between emissions. None denotes
absence; a present cell can contain false or an opaque checked callback handle. -/
structure BorrowedChange (K Cell : Type) where
  key : K
  before : Option Cell
  after : Option Cell

/-- Read both borrowed shells into an owned immutable change BEFORE validation. -/
def captureChange (heap : Cell → V) (event : BorrowedChange K Cell) : Change K V :=
  ⟨event.key, event.before.map heap, event.after.map heap⟩

/-- Emission snapshots may differ even when the same cells are reused. -/
def captureEvents (events : List ((Cell → V) × BorrowedChange K Cell)) : List (Change K V) :=
  events.map (fun observed => captureChange observed.1 observed.2)

/-- Capture retains the original key and its position. -/
theorem captureChange_key (heap : Cell → V) (event : BorrowedChange K Cell) :
    (captureChange heap event).key = event.key := rfl

/-- A present false/Function payload is retained as the exact observed child. -/
theorem captureChange_payload (heap : Cell → V) (key : K) (old next : Cell) :
    captureChange heap ⟨key, some old, some next⟩ =
      ⟨key, some (heap old), some (heap next)⟩ := rfl

/-- Every emitted event remains, including repeated keys and cancelling writes. -/
theorem captureEvents_length (events : List ((Cell → V) × BorrowedChange K Cell)) :
    (captureEvents events).length = events.length := by simp [captureEvents]

/-- Ordered composition neither rereads old shells nor discards expectations. -/
theorem captureEvents_append (a b : List ((Cell → V) × BorrowedChange K Cell)) :
    captureEvents (a ++ b) = captureEvents a ++ captureEvents b := by simp [captureEvents]

/-- The emitted key sequence is preserved independently of shell reuse. -/
theorem captureEvents_keys (events : List ((Cell → V) × BorrowedChange K Cell)) :
    (captureEvents events).map Change.key = events.map (fun observed => observed.2.key) := by
  simp [captureEvents, List.map_map, Function.comp_def, captureChange]

/-- A minimal shell/owned-history state makes producer writes explicit. The
reference history uses append; it does not model the runtime list-builder cost. -/
abbrev ChangeCaptureState (K Cell V : Type) := (Cell → V) × List (Change K V)

/-- Only the borrowed heap changes; already captured events retain their leaves. -/
def overwriteChangeShell [DecidableEq Cell] (state : ChangeCaptureState K Cell V)
    (cell : Cell) (value : V) : ChangeCaptureState K Cell V :=
  (fun query => if query = cell then value else state.1 query, state.2)

/-- Snapshot one emission before the producer regains control. -/
def emitChange (state : ChangeCaptureState K Cell V) (event : BorrowedChange K Cell) :
    ChangeCaptureState K Cell V :=
  (state.1, state.2 ++ [captureChange state.1 event])

/-- Future producer mutation cannot rewrite the captured prefix or latest event. -/
theorem emitChange_owned [DecidableEq Cell] (state : ChangeCaptureState K Cell V)
    (event : BorrowedChange K Cell) (cell : Cell) (value : V) :
    (overwriteChangeShell (emitChange state event) cell value).2 =
      state.2 ++ [captureChange state.1 event] := rfl

/-- Replay has the SAME complete success or first-conflict result after shell
reuse. The installer never receives the mutable shell heap. -/
theorem captured_replay_stable [DecidableEq K] [DecidableEq V] [DecidableEq Cell]
    (state : ChangeCaptureState K Cell V) (cell : Cell) (value : V)
    (before : K → Option V) :
    applyChanges (overwriteChangeShell state cell value).2 before =
      applyChanges state.2 before := rfl

/-- Reversal retains the same owned payloads after unrelated producer writes. -/
theorem captured_inverse_stable [DecidableEq Cell] (state : ChangeCaptureState K Cell V)
    (cell : Cell) (value : V) :
    inverseChanges (overwriteChangeShell state cell value).2 = inverseChanges state.2 := rfl

/-- A recognizer may affect its external heap. Its result can expose only the
pre-recognition captured change; callback effects are explicitly retained. -/
def checkedChangeCapture (heap : Cell → V) (event : BorrowedChange K Cell)
    (recognize : Change K V → (Cell → V) → (Cell → V) × Except E Unit) :
    (Cell → V) × Except E (Change K V) :=
  let captured := captureChange heap event
  let (later, result) := recognize captured heap
  (later, result.map (fun _ => captured))

/-- Successful recognition cannot substitute a value read from a later shell. -/
theorem checkedChangeCapture_ready (heap later : Cell → V) (event : BorrowedChange K Cell)
    (recognize : Change K V → (Cell → V) → (Cell → V) × Except E Unit)
    (ready : recognize (captureChange heap event) heap = (later, .ok ())) :
    checkedChangeCapture heap event recognize = (later, .ok (captureChange heap event)) := by
  simp [checkedChangeCapture, ready, Except.map]

/-- Failed admission returns its exact cause and no partial event. External
recognizer effects are not rolled back or misrepresented as object publication. -/
theorem checkedChangeCapture_refused (heap later : Cell → V) (event : BorrowedChange K Cell)
    (recognize : Change K V → (Cell → V) → (Cell → V) × Except E Unit) (cause : E)
    (refused : recognize (captureChange heap event) heap = (later, .error cause)) :
    checkedChangeCapture heap event recognize = (later, .error cause) := by
  simp [checkedChangeCapture, refused, Except.map]

/-! Declaration buffers are borrowed only during admission. Captured object
identities are immutable; revisions of those objects remain independently checked.
The finite-list model does not infer hidden callback dependencies or copy leaves. -/
section OriginCapture
variable {Id : Type}

/-- Copy a finite declaration spine before a later metadata getter can reuse it. -/
def captureOrigins (buffer : Cell → Id) (cells : List Cell) : List Id := cells.map buffer

/-- Capture retains declaration order and multiplicity, with one entry per cell. -/
theorem captureOrigins_length (buffer : Cell → Id) (cells : List Cell) :
    (captureOrigins buffer cells).length = cells.length := by simp [captureOrigins]

/-- Explicit and descriptor declarations compose without rereading either buffer. -/
theorem captureOrigins_append (buffer : Cell → Id) (left right : List Cell) :
    captureOrigins buffer (left ++ right) =
      captureOrigins buffer left ++ captureOrigins buffer right := by simp [captureOrigins]

/-- Every originally declared identity remains in the captured dependency scope. -/
theorem captureOrigins_member (buffer : Cell → Id) (cells : List Cell)
    (cell : Cell) (member : cell ∈ cells) :
    buffer cell ∈ captureOrigins buffer cells := List.mem_map.mpr ⟨cell, member, rfl⟩

/-- Borrowed buffer writes change only the buffer component, never the owned scope. -/
def replaceOriginBuffer (state : (Cell → Id) × List Id) (later : Cell → Id) :
    (Cell → Id) × List Id := (later, state.2)

/-- Subsequent declaration-buffer reuse cannot change the exact stamp decision. -/
theorem capturedOrigins_stable (buffer later : Cell → Id) (cells : List Cell)
    (expected current : Id → Option Nat) :
    stampMatches (replaceOriginBuffer (buffer, captureOrigins buffer cells) later).2
      expected current = stampMatches (captureOrigins buffer cells) expected current := rfl

/-- A changed original dependency is refused even if its declaration cell now
names a different object carrying the same revision as the old snapshot. -/
theorem capturedOrigins_stale (buffer : Cell → Id) (cells : List Cell)
    (cell : Cell) (member : cell ∈ cells) (expected current : Id → Option Nat)
    (changed : expected (buffer cell) ≠ current (buffer cell)) :
    stampMatches (captureOrigins buffer cells) expected current = false := by
  cases ready : stampMatches (captureOrigins buffer cells) expected current with
  | false => rfl
  | true =>
    have all : ∀ key ∈ captureOrigins buffer cells, expected key = current key := by
      simpa [stampMatches, List.all_eq_true] using ready
    exact False.elim (changed (all _ (captureOrigins_member buffer cells cell member)))

/-- Buffer reuse alone does not invalidate unchanged, explicitly declared objects. -/
theorem capturedOrigins_fresh (buffer : Cell → Id) (cells : List Cell)
    (expected current : Id → Option Nat)
    (unchanged : ∀ key ∈ captureOrigins buffer cells, expected key = current key) :
    stampMatches (captureOrigins buffer cells) expected current = true := by
  simpa [stampMatches, List.all_eq_true] using unchanged

end OriginCapture

end LeanPoo.Functional.OrderedDictionary
