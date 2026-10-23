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

end LeanPoo.Functional.OrderedDictionary
