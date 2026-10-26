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

/-- Runtime weak-map values contain only a subject revision and numeric origin
stamps. Identity-keyed lookup and faithful, stable host snapshots are premises;
this datatype does not certify the collector or raw reflective mutation. -/
abbrev ComparerSeal := Nat × List Nat

/-- An absent constructor seal grants no positioned-backend capability, even if
public callback fields happen to be identical to another comparer's fields. -/
def comparerSealCurrent (captured : Option ComparerSeal) (current : ComparerSeal) : Bool :=
  captured == some current

/-- Unchanged constructor subjects refuse stale origins before observation.
Edited or unsealed protocols retain reference fallback through their existing
primitive guard, without positioned-backend evidence. -/
def admitComparerUse (captured : Option ComparerSeal) (current : ComparerSeal)
    (stale : E) (observe : Unit → Except E R) : Except E R :=
  if captured.any (fun issued => issued.1 == current.1) && !comparerSealCurrent captured current
  then .error stale else observe ()

/-- Constructor identity/revision alone is insufficient: origin stamps must match. -/
theorem comparerSealCurrent_complete (issued current : ComparerSeal) :
    comparerSealCurrent (some issued) current = true ↔ issued = current := by
  simp [comparerSealCurrent]

/-- A copied custom protocol cannot borrow a positioned capability by callback
identity. Its reference fallback remains an independent, explicit caller contract. -/
theorem comparerSealCurrent_unsealed (current : ComparerSeal) (sameCallbacks : Bool) :
    (comparerSealCurrent none current && sameCallbacks) = false := rfl

/-- Origin changes invalidate a seal even when the comparer itself is unchanged. -/
theorem comparerSealCurrent_dependencies (owner : Nat) (issued current : List Nat)
    (changed : issued ≠ current) :
    comparerSealCurrent (some (owner, issued)) (owner, current) = false := by
  simp [comparerSealCurrent, changed]

/-- Editing constructor metadata also revokes its seal; reverting field content
is not equivalent to restoring an earlier host revision. -/
theorem comparerSealCurrent_subject (issued current : Nat) (old next : List Nat)
    (changed : issued ≠ current) :
    comparerSealCurrent (some (issued, old)) (current, next) = false := by
  simp [comparerSealCurrent, changed]

/-- Current seals preserve the exact observation and original callback failure. -/
theorem admitComparerUse_current (current : ComparerSeal) (stale : E)
    (observe : Unit → Except E R) :
    admitComparerUse (some current) current stale observe = observe () := by
  simp [admitComparerUse, comparerSealCurrent]

/-- No constructor stamp is invented for manually declared fallback protocols. -/
theorem admitComparerUse_custom (current : ComparerSeal) (stale : E)
    (observe : Unit → Except E R) :
    admitComparerUse none current stale observe = observe () := rfl

/-- Stale origins of an unchanged subject suppress observation even if sorting compares zero pairs,
for example on an empty/singleton root or an already exhausted cursor. -/
theorem admitComparerUse_stale (issued current : ComparerSeal) (stale : E)
    (observe : Unit → Except E R) (sameSubject : issued.1 = current.1)
    (changed : issued ≠ current) :
    admitComparerUse (some issued) current stale observe = .error stale := by
  simp [admitComparerUse, comparerSealCurrent, sameSubject, changed]

/-- Revising public metadata removes positioning evidence, while reference use
still delegates its existing primitive guard and original failure semantics. -/
theorem admitComparerUse_edited (issued current : ComparerSeal) (stale : E)
    (observe : Unit → Except E R) (changed : issued.1 ≠ current.1) :
    admitComparerUse (some issued) current stale observe = observe () := by
  simp [admitComparerUse, changed]

/-- Reference observation and backend capability are separate. Both callbacks
retain their own admission laws; only a complete current seal selects a shortcut. -/
def observeComparer (captured : Option ComparerSeal) (current : ComparerSeal)
    (stale : E) (backend : Option (Unit → Except E R))
    (reference : Unit → Except E R) : Except E R :=
  admitComparerUse captured current stale (fun _ =>
    if comparerSealCurrent captured current then (backend.getD reference) () else reference ())

/-- A lawful custom protocol keeps its reference result, even when an inherited
backend shortcut exists. Callback identity does not confer backend authority. -/
theorem observeComparer_custom (current : ComparerSeal) (stale : E)
    (backend : Option (Unit → Except E R)) (reference : Unit → Except E R) :
    observeComparer none current stale backend reference = reference () := rfl

/-- Label edits revoke shortcut eligibility without revoking guarded reference use. -/
theorem observeComparer_edited (issued current : ComparerSeal) (stale : E)
    (backend : Option (Unit → Except E R)) (reference : Unit → Except E R)
    (changed : issued.1 ≠ current.1) :
    observeComparer (some issued) current stale backend reference = reference () := by
  simp [observeComparer, admitComparerUse, comparerSealCurrent, changed,
    show issued ≠ current from fun h => changed (congrArg Prod.fst h)]

/-- Current constructor evidence delegates the original backend and failure cause. -/
theorem observeComparer_backend (current : ComparerSeal) (stale : E)
    (backend reference : Unit → Except E R) :
    observeComparer (some current) current stale (some backend) reference = backend () := by
  simp [observeComparer, admitComparerUse, comparerSealCurrent]

/-- A missing shortcut preserves reference observation rather than inventing one. -/
theorem observeComparer_reference (captured : Option ComparerSeal) (current : ComparerSeal)
    (stale : E) (reference : Unit → Except E R) :
    observeComparer captured current stale none reference =
      admitComparerUse captured current stale reference := by
  simp only [observeComparer, Option.getD_none, ite_self]

/-- Stale declared origins suppress both callbacks, including empty observations. -/
theorem observeComparer_stale (owner : Nat) (issued current : List Nat) (stale : E)
    (backend : Option (Unit → Except E R)) (reference : Unit → Except E R)
    (changed : issued ≠ current) :
    observeComparer (some (owner, issued)) (owner, current) stale backend reference = .error stale := by
  apply admitComparerUse_stale
  · rfl
  · exact fun h => changed (congrArg Prod.snd h)

/-- The existing cursor guard sees the complete seal, including origin stamps.
An origin-only change performs no backend pull, including after EOF. -/
theorem checkedComparerPull_dependencies (owner : Nat) (issued current : List Nat)
    (rows : List (K × V)) (changed : issued ≠ current) :
    checkedTablePull (owner :: issued) (owner :: current) rows = (.error (), 0) := by
  apply checkedTablePull_stale
  intro same
  exact changed (List.cons.inj same).2

/-- Fresh metadata retains the original row/EOF and one standard backend pull;
guard work, allocation, scheduling and GC are explicitly outside that counter. -/
theorem checkedComparerPull_current (owner : Nat) (versions : List Nat) (rows : List (K × V)) :
    checkedTablePull (owner :: versions) (owner :: versions) rows =
      (.ok (tableCursorPull rows), 1) := checkedTablePull_current _ rows

/-- Capture only endpoint cells before admission/discovery callbacks. Preparation
may change the caller's cell heap, but observation retains the original keys.
Opaque key stability and faithful host revision checks remain premises; this does
not model arbitrary key mutation, threads, compiler behavior or GC. -/
def observeCapturedBounds (read : Cell → K) (lower upper : Option Cell)
    (prepare : (Cell → K) → Except E (Cell → K))
    (query : Option K → Option K → Except E R) : Except E R :=
  let lo := lower.map read
  let hi := upper.map read
  (prepare read).bind (fun _ => query lo hi)

/-- A successful preparation cannot replace either endpoint, even with a changed heap. -/
theorem observeCapturedBounds_ready (read later : Cell → K) (lower upper : Option Cell)
    (prepare : (Cell → K) → Except E (Cell → K))
    (query : Option K → Option K → Except E R) (ready : prepare read = .ok later) :
    observeCapturedBounds read lower upper prepare query = query (lower.map read) (upper.map read) := by
  simp [observeCapturedBounds, ready, Except.bind]

/-- Admission refusal precedes bound validation and suppresses query evaluation,
including empty roots and malformed requests in the host protocol. -/
theorem observeCapturedBounds_refused (read : Cell → K) (lower upper : Option Cell)
    (prepare : (Cell → K) → Except E (Cell → K)) (cause : E)
    (query : Option K → Option K → Except E R) (refused : prepare read = .error cause) :
    observeCapturedBounds read lower upper prepare query = .error cause := by
  simp [observeCapturedBounds, refused, Except.bind]

/-- An invalid captured key retains its original failure; preparation cannot
repair the request by rewriting the caller's endpoint cell. -/
theorem observeCapturedBounds_query_refused (read later : Cell → K) (lower upper : Option Cell)
    (prepare : (Cell → K) → Except E (Cell → K)) (cause : E)
    (query : Option K → Option K → Except E R) (ready : prepare read = .ok later)
    (refused : query (lower.map read) (upper.map read) = .error cause) :
    observeCapturedBounds read lower upper prepare query = .error cause := by
  rw [observeCapturedBounds_ready read later lower upper prepare query ready, refused]

/-- Unboundedness is an absent Option, never a sentinel from the key domain. -/
theorem observeCapturedBounds_unbounded (read later : Cell → K)
    (query : Option K → Option K → Except E R) :
    observeCapturedBounds read none none (fun _ => .ok later) query = query none none := rfl

/-- Style/index handoffs may capture again through identity without changing
endpoints or invoking preparation a second time. No row scan or key copy is required. -/
theorem observeCapturedBounds_identity (lower upper : Option K)
    (prepare : (K → K) → Except E (K → K)) (query : Option K → Option K → Except E R) :
    observeCapturedBounds id lower upper prepare query =
      (prepare id).bind (fun _ => query lower upper) := by
  simp [observeCapturedBounds]

/-- The existing range algorithm keeps endpoint inclusion, ordered rows and opaque
payloads. Only two endpoint cells are captured; backend positioning costs are unchanged. -/
theorem observeCapturedBounds_range (read later : Cell → K) (lower upper : Option Cell)
    (lowerInclusive upperInclusive : Bool) (compare : K → K → Int) (rows : List (K × V)) :
    observeCapturedBounds (E := E) read lower upper (fun _ => .ok later)
      (fun lo hi => .ok (tableRangeRows compare
        (lo.map (fun key => ⟨key, lowerInclusive⟩))
        (hi.map (fun key => ⟨key, upperInclusive⟩)) rows)) =
    .ok (tableRangeRows compare
      (lower.map (fun cell => ⟨read cell, lowerInclusive⟩))
      (upper.map (fun cell => ⟨read cell, upperInclusive⟩)) rows) := by
  simp [observeCapturedBounds, Except.bind, Option.map_map, Function.comp_def]


section
variable {Cell K V E : Type}

/-- Capture one producer-owned Pair before admission and bound comparison may
rewrite the producer's buffer. Opaque leaves remain values in the captured pair;
external effects are not rolled back. This reuses Except for exact refusal. -/
def observeCapturedEntry (read : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool) : Except E (Option (K × V)) :=
  let entry := read cell
  (admit entry).bind fun _ =>
    (select entry).map fun keep => if keep then some entry else none

/-- A rejected producer row cannot reach selection, even when it would be hidden
below the requested bound. Recognition cannot repair the original captured row. -/
theorem observeCapturedEntry_refused (read : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool) (cause : E)
    (refused : admit (read cell) = .error cause) :
    observeCapturedEntry read cell admit select = .error cause := by
  simp [observeCapturedEntry, refused, Except.bind]

/-- Successful recognition may change the heap, never the binding passed to the
selector or the binding delivered after its effects. -/
theorem observeCapturedEntry_ready (read later : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool)
    (ready : admit (read cell) = .ok later) :
    observeCapturedEntry read cell admit select =
      (select (read cell)).map (fun keep => if keep then some (read cell) else none) := by
  simp [observeCapturedEntry, ready, Except.bind]

/-- An admitted but filtered row returns absence after validation, not before it. -/
theorem observeCapturedEntry_filtered (read later : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool)
    (ready : admit (read cell) = .ok later) (hidden : select (read cell) = .ok false) :
    observeCapturedEntry read cell admit select = .ok none := by
  simp [observeCapturedEntry, ready, hidden, Except.bind, Except.map]

/-- Comparator exceptions retain their cause and suppress row delivery. -/
theorem observeCapturedEntry_selection_refused (read later : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool) (cause : E)
    (ready : admit (read cell) = .ok later) (refused : select (read cell) = .error cause) :
    observeCapturedEntry read cell admit select = .error cause := by
  simp [observeCapturedEntry, ready, refused, Except.bind, Except.map]

/-- Delivery preserves the original key and opaque payload after both callbacks. -/
theorem observeCapturedEntry_delivered (read later : Cell → K × V) (cell : Cell)
    (admit : (K × V) → Except E (Cell → K × V))
    (select : (K × V) → Except E Bool)
    (ready : admit (read cell) = .ok later) (selected : select (read cell) = .ok true) :
    observeCapturedEntry read cell admit select = .ok (some (read cell)) := by
  simp [observeCapturedEntry, ready, selected, Except.bind, Except.map]

end


section
variable {Cell K V E L W : Type}

/-- Capture a producer binding before key conversion can replace its heap. Reuse
translateCursorEntry for conversion order and exact errors; the returned heap is
an explicit effect witness, not a second translation engine or rollback model. -/
def translateCapturedCursorEntry (read : Cell → K × V) (cell : Cell)
    (key : K → Except E (L × (Cell → K × V))) (value : V → Except E W) :
    Except E (L × W) :=
  translateCursorEntry (fun input => (key input).map Prod.fst) value (read cell)

/-- A key refusal suppresses value conversion and retains its original cause. -/
theorem translateCapturedCursorEntry_key_refused (read : Cell → K × V) (cell : Cell)
    (key : K → Except E (L × (Cell → K × V))) (value : V → Except E W)
    (cause : E) (refused : key (read cell).1 = .error cause) :
    translateCapturedCursorEntry read cell key value = .error cause := by
  simp [translateCapturedCursorEntry, translateCursorEntry, refused, Except.map]

/-- Successful conversion uses the original payload even when the key converter
returns a rewritten producer heap. Caller-owned Pair shells are not leaf values. -/
theorem translateCapturedCursorEntry_ready (read later : Cell → K × V) (cell : Cell)
    (key : K → Except E (L × (Cell → K × V))) (value : V → Except E W)
    (k : L) (v : W) (hk : key (read cell).1 = .ok (k, later))
    (hv : value (read cell).2 = .ok v) :
    translateCapturedCursorEntry read cell key value = .ok (k, v) := by
  simp [translateCapturedCursorEntry, translateCursorEntry, hk, hv, Except.map]

/-- A key converter cannot repair an invalid original payload by rewriting the
producer buffer; value refusal still suppresses delivery and downstream consumers. -/
theorem translateCapturedCursorEntry_value_refused (read later : Cell → K × V) (cell : Cell)
    (key : K → Except E (L × (Cell → K × V))) (value : V → Except E W)
    (k : L) (cause : E) (hk : key (read cell).1 = .ok (k, later))
    (refused : value (read cell).2 = .error cause) :
    translateCapturedCursorEntry read cell key value = .error cause := by
  simp [translateCapturedCursorEntry, translateCursorEntry, hk, refused, Except.map]

/-- Identity payload conversion retains an opaque Function or other admitted leaf,
without any equality, cloning, normalization or purity premise on that leaf. -/
theorem translateCapturedCursorEntry_leaf (read later : Cell → K × V) (cell : Cell)
    (key : K → Except E (L × (Cell → K × V))) (k : L)
    (hk : key (read cell).1 = .ok (k, later)) :
    translateCapturedCursorEntry read cell key (fun value => .ok value) =
      .ok (k, (read cell).2) := by
  simp [translateCapturedCursorEntry, translateCursorEntry, hk, Except.map]

end


/-- Complete Table observation uses the same metadata/Except protocol as styles.
Admission precedes backend observation without normalizing opaque leaves. -/
def observeTable (issued current : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (query : A → Except E R) :
    Except (TableObservationFailure E) R :=
  observeStyle issued current (some snapshot)
    (some (fun value => (admit value).bind fun _ => query value))

/-- Whole-root refusal suppresses backend list materialization or cursor issuance. -/
theorem observeTable_refused (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (query : A → Except E R) (cause : E)
    (refused : admit snapshot = .error cause) :
    observeTable versions versions snapshot admit query = .error (.backend cause) := by
  simp [observeTable, observeStyle, refused, Except.bind, Except.mapError]

/-- Accepted observation delegates exactly, retaining order and opaque payloads. -/
theorem observeTable_ready (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (query : A → Except E R)
    (accepted : admit snapshot = .ok ()) :
    observeTable versions versions snapshot admit query =
      (query snapshot).mapError TableObservationFailure.backend := by
  simp [observeTable, observeStyle, accepted, Except.bind]

/-- Metadata refusal precedes whole-root recognition and backend work. -/
theorem observeTable_stale (issued current : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (query : A → Except E R) (stale : issued ≠ current) :
    observeTable issued current snapshot admit query = .error .stale := by
  simp [observeTable, observeStyle, stale]

/-- A backend refusal retains its cause after successful complete admission. -/
theorem observeTable_backend_refused (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (query : A → Except E R) (cause : E)
    (accepted : admit snapshot = .ok ()) (refused : query snapshot = .error cause) :
    observeTable versions versions snapshot admit query = .error (.backend cause) := by
  simp [observeTable, observeStyle, accepted, refused, Except.bind, Except.mapError]

/-- Issue the existing immutable cursor after complete Table admission. Deferred
pulls continue to use pullStyleCursor, including zero delegation after invalidation. -/
def issueTableCursor (issued current : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × V))) :
    Except (TableObservationFailure E) (StyleCursor K V) :=
  (observeTable issued current snapshot admit enumerate).map (fun rows => ⟨issued, rows⟩)

/-- Refused issuance exposes no cursor, including for empty or malformed roots. -/
theorem issueTableCursor_refused (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × V)))
    (cause : E) (refused : admit snapshot = .error cause) :
    issueTableCursor versions versions snapshot admit enumerate = .error (.backend cause) := by
  simp [issueTableCursor, observeTable_refused versions snapshot admit enumerate cause refused, Except.map]

/-- The accepted stream preserves original enumeration without an ownership lookup. -/
theorem issueTableCursor_ready (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × V)))
    (rows : List (K × V)) (accepted : admit snapshot = .ok ())
    (enumerated : enumerate snapshot = .ok rows) :
    issueTableCursor versions versions snapshot admit enumerate = .ok ⟨versions, rows⟩ := by
  simp [issueTableCursor, observeTable_ready versions snapshot admit enumerate accepted,
    enumerated, Except.mapError, Except.map]

end LeanPoo.Functional.OrderedDictionary
