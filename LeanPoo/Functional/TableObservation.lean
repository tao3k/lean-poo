import LeanPoo.Functional.TableOrder

/-! Snapshot-bound style observation reuses the finite ordered cursor. Ownership
is checked when issuing a snapshot, metadata on every delayed pull. Runtime
iterator registration, scheduling and arbitrary callback effects are premises. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Query capability refusal is distinct from ownership, origin and backend errors. -/
inductive TableObservationFailure (E : Type) where
  | stale | consumed | unsupported | backend (cause : E)
  deriving DecidableEq, Repr

/-- Complete eager observation captures one persistent root before delegating.
The caller supplies a backend capability; absence is not an ordering heuristic. -/
def observeStyle (issued current : List Nat) (state : Option A)
    (query : Option (A → Except E R)) : Except (TableObservationFailure E) R :=
  if issued ≠ current then .error .stale else
    match state with
    | none => .error .consumed
    | some snapshot =>
      match query with
      | none => .error .unsupported
      | some run => (run snapshot).mapError TableObservationFailure.backend

/-- A current live source delegates exactly the same result and failure cause. -/
theorem observeStyle_delegates (versions : List Nat) (snapshot : A) (run : A → Except E R) :
    observeStyle versions versions (some snapshot) (some run) =
      (run snapshot).mapError TableObservationFailure.backend := by simp [observeStyle]

/-- An unsupported query cannot consume or mutate a live collection. -/
theorem observeStyle_unsupported (versions : List Nat) (snapshot : A) :
    observeStyle (E := E) (R := R) versions versions (some snapshot) none =
      .error .unsupported := by simp [observeStyle]

/-- Issuing a new cursor from a consumed owner refuses before backend evaluation. -/
theorem observeStyle_consumed (versions : List Nat) (query : Option (A → Except E R)) :
    observeStyle versions versions none query = .error .consumed := by simp [observeStyle]

/-- Stale metadata refuses even when the requested capability or owner is missing. -/
theorem observeStyle_stale (issued current : List Nat) (state : Option A)
    (query : Option (A → Except E R)) (stale : issued ≠ current) :
    observeStyle issued current state query = .error .stale := by simp [observeStyle, stale]

/-- Style erasure does not change snapshot-bound eager observation. -/
theorem receiver_observe_erasure (versions : List Nat) (input : TableReceiver A)
    (query : Option (A → Except E R)) :
    observeStyle versions versions input.value query =
      match input.value with
      | none => .error .consumed
      | some value => match query with
        | none => .error .unsupported
        | some run => (run value).mapError TableObservationFailure.backend := by
  cases input.value <;> cases query <;> simp [observeStyle]

/-- A cursor owns a captured row stream and metadata, never an update capability. -/
structure StyleCursor (K V : Type) where
  issued : List Nat
  rows : List (K × V)
  deriving DecidableEq, Repr

/-- Issue one cursor with backend enumeration order and exact opaque payloads. -/
def issueStyleCursor (issued current : List Nat) (state : Option A)
    (enumerate : A → Except E (List (K × V))) :
    Except (TableObservationFailure E) (StyleCursor K V) :=
  (observeStyle issued current state (some enumerate)).map (fun rows => ⟨issued, rows⟩)

/-- Delayed pulls reuse the existing guarded cursor, including its EOF check. -/
def pullStyleCursor (cursor : StyleCursor K V) (current : List Nat) :
    Except Unit (Option (K × V) × StyleCursor K V) × Nat :=
  let pulled := checkedTablePull cursor.issued current cursor.rows
  (pulled.1.map (fun (entry, rest) => (entry, { cursor with rows := rest })), pulled.2)

/-- No ownership lookup is repeated during a pull: an issued immutable snapshot
remains meaningful after the original update capability is retired. -/
theorem pullStyleCursor_current (versions : List Nat) (rows : List (K × V)) :
    pullStyleCursor ⟨versions, rows⟩ versions =
      (.ok ((tableCursorPull rows).1, ⟨versions, (tableCursorPull rows).2⟩), 1) := by
  simp [pullStyleCursor, checkedTablePull, Except.map]

/-- Stale origin refusal performs zero backend pulls and exposes no staged tail. -/
theorem pullStyleCursor_stale (cursor : StyleCursor K V) (current : List Nat)
    (stale : cursor.issued ≠ current) :
    pullStyleCursor cursor current = (.error (), 0) := by
  simp [pullStyleCursor, checkedTablePull, stale, Except.map]

/-- Exhaustion never bypasses metadata validation. -/
theorem pullStyleCursor_eof (issued current : List Nat) :
    pullStyleCursor (K := K) (V := V) ⟨issued, []⟩ current =
      if issued = current then (.ok (none, ⟨issued, []⟩), 1) else (.error (), 0) := by
  by_cases h : issued = current <;>
    simp [pullStyleCursor, checkedTablePull, tableCursorPull, h, Except.map]

/-- A live captured snapshot issues the exact backend stream without remapping rows. -/
theorem issueStyleCursor_exact (versions : List Nat) (snapshot : A)
    (enumerate : A → Except E (List (K × V))) (rows : List (K × V))
    (enumerated : enumerate snapshot = .ok rows) :
    issueStyleCursor versions versions (some snapshot) enumerate = .ok ⟨versions, rows⟩ := by
  simp [issueStyleCursor, observeStyle, enumerated, Except.mapError, Except.map]

/-- A callback reentering a classy update cannot change a query's captured root:
the fresh head observes after while the captured cursor retains before. -/
theorem classy_observation_snapshots (family identity fresh : Nat) (before after : A)
    (update : A → Except E A) (enumerate : A → List (K × V))
    (updated : update before = .ok after) :
    let result := receiverStep ⟨family, .classy, identity, some before⟩ fresh update
    (result.1.value.map enumerate, enumerate before) =
      (some (enumerate after), enumerate before) := by
  simp [receiverStep_classy family identity fresh before after update updated]

/-- Positioning and range selection happen before stream capture. Applying the
identity style presentation adds no enumeration or change in cursor pull count. -/
theorem style_positioned_range (accept : K → Bool) (rows : List (K × V)) :
    tableRangePrefix accept (rows.map id) = tableRangePrefix accept rows :=
  tableRangePrefix_identity accept rows


/-- Key recognition/conversion precedes value conversion for each demanded row.
The actual Wrapper also checks encountered inverses; those laws are separate. -/
def translateCursorEntry (key : K → Except E L) (value : V → Except E W)
    (entry : K × V) : Except E (L × W) :=
  match key entry.1 with
  | .error cause => .error cause
  | .ok translatedKey => (value entry.2).map (translatedKey, ·)

/-- A refused key suppresses the value callback and preserves the original cause. -/
theorem translateCursorEntry_key_refused (key : K → Except E L) (value : V → Except E W)
    (entry : K × V) (cause : E) (refused : key entry.1 = .error cause) :
    translateCursorEntry key value entry = .error cause := by
  simp [translateCursorEntry, refused]

/-- Successful child conversions preserve both supplied values without normalization. -/
theorem translateCursorEntry_ready (key : K → Except E L) (value : V → Except E W)
    (entry : K × V) (k : L) (v : W) (hk : key entry.1 = .ok k) (hv : value entry.2 = .ok v) :
    translateCursorEntry key value entry = .ok (k, v) := by
  simp [translateCursorEntry, hk, hv, Except.map]
/-- One represented pull reuses the checked source cursor, then translates only
its present entry. State is explicit: conversion failure follows a source pull,
whereas stale metadata retains the original tail. Work counts source pulls and
entry translations, not inverse calls, admission, construction, guards or GC. -/
def mappedTablePull (translate : K × V → Except E R) (issued current : List Nat)
    (rows : List (K × V)) :
    (List (K × V) × Except (TableObservationFailure E) (Option R)) × (Nat × Nat) :=
  let pulled := checkedTablePull issued current rows
  match pulled.1 with
  | .error () => ((rows, .error .stale), (pulled.2, 0))
  | .ok (none, rest) => ((rest, .ok none), (pulled.2, 0))
  | .ok (some row, rest) =>
    ((rest, (translate row).map some |>.mapError TableObservationFailure.backend), (pulled.2, 1))

/-- Rejected origins neither advance the source nor invoke a converter. -/
theorem mappedTablePull_stale (translate : K × V → Except E R) (issued current : List Nat)
    (rows : List (K × V)) (stale : issued ≠ current) :
    mappedTablePull translate issued current rows = ((rows, .error .stale), (0, 0)) := by
  simp [mappedTablePull, checkedTablePull, stale]

/-- A current source translates exactly its first row; later rows are not inspected. -/
theorem mappedTablePull_head (translate : K × V → Except E R) (versions : List Nat)
    (row : K × V) (rest : List (K × V)) :
    mappedTablePull translate versions versions (row :: rest) =
      ((rest, (translate row).map some |>.mapError TableObservationFailure.backend), (1, 1)) := by
  simp [mappedTablePull, checkedTablePull, tableCursorPull]

/-- EOF bypasses translation, never origin checks; repeated exhausted pulls obey
this same law rather than returning an unguarded cached sentinel. -/
theorem mappedTablePull_eof (translate : K × V → Except E R) (issued current : List Nat) :
    mappedTablePull translate issued current [] =
      if issued = current then (([], .ok none), (1, 0)) else (([], .error .stale), (0, 0)) := by
  by_cases same : issued = current <;>
    simp [mappedTablePull, checkedTablePull, tableCursorPull, same]

/-- A checked Function or stored false payload is retained as the exact translated
value; Option distinguishes the present result from EOF. -/
theorem mappedTablePull_success (translate : K × V → Except E R) (versions : List Nat)
    (row : K × V) (rest : List (K × V)) (value : R) (ready : translate row = .ok value) :
    mappedTablePull translate versions versions (row :: rest) =
      ((rest, .ok (some value)), (1, 1)) := by
  simp [mappedTablePull_head, ready, Except.map, Except.mapError]

/-- Conversion refusal preserves the cause and the already advanced source tail.
It makes no claim that an arbitrary mutable backend cursor can rewind. -/
theorem mappedTablePull_conversion_refused (translate : K × V → Except E R)
    (versions : List Nat) (row : K × V) (rest : List (K × V)) (cause : E)
    (refused : translate row = .error cause) :
    mappedTablePull translate versions versions (row :: rest) =
      ((rest, .error (.backend cause)), (1, 1)) := by
  simp [mappedTablePull_head, refused, Except.map, Except.mapError]

/-- A stale outer representation suppresses an otherwise current inner iterator.
Composing protocol layers must not restore an unguarded eager fallback. -/
theorem mappedTablePull_outer_refused (translate : K × V → Except E R)
    (outerIssued outerCurrent innerIssued innerCurrent : List Nat) (rows : List (K × V))
    (stale : outerIssued ≠ outerCurrent) :
    (if outerIssued = outerCurrent then mappedTablePull translate innerIssued innerCurrent rows
      else ((rows, .error .stale), (0, 0))) = ((rows, .error .stale), (0, 0)) := by
  simp [stale]

/-- An accepted outer view adds no second source pull or extra entry translation.
This does not assign constant cost to the number of metadata guard layers. -/
theorem mappedTablePull_outer_current (translate : K × V → Except E R)
    (outer inner : List Nat) (rows : List (K × V)) :
    (if outer = outer then mappedTablePull translate inner inner rows
      else ((rows, .error .stale), (0, 0))) = mappedTablePull translate inner inner rows := by
  simp

/-- Lazy representation delegation agrees with eager mapping at the demanded head
under an explicit successful conversion. No future conversion is required to pass. -/
theorem mappedTablePull_agrees (translate : K × V → Except E (L × W))
    (encode : K × V → L × W) (versions : List Nat) (row : K × V)
    (rest : List (K × V)) (ready : translate row = .ok (encode row)) :
    (mappedTablePull translate versions versions (row :: rest)).1.2 =
      .ok (tableCursorPull ((row :: rest).map encode)).1 := by
  simp [mappedTablePull_success translate versions row rest (encode row) ready, tableCursorPull]

end LeanPoo.Functional.OrderedDictionary
