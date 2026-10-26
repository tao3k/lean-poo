import LeanPoo.Functional.SetAlgebra
import LeanPoo.Functional.TableObservation

/-! Set style derivation changes presentation only. Independent update capabilities
reuse table ownership, and element cursors reuse the original metadata guards. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Capture a compatible right snapshot once, then use the original left engine.
The pair models distinct capabilities. Aliased handles follow the left capability's
retirement; no physical exclusivity of persistent snapshots is assumed. -/
def setStyleCombine (style : TableStyle) (left right : Option A)
    (combine : A → A → Except E A) :
    (Option A × Option A) × Except (StyleFailure E) A :=
  match right with
  | none => ((left, right), .error .consumed)
  | some other =>
    let result := styleStep style left (fun before => combine before other)
    ((result.1, right), result.2)

/-- A retired right capability refuses before the left transformation begins. -/
theorem setStyleCombine_right_consumed (style : TableStyle) (left : Option A)
    (combine : A → A → Except E A) :
    setStyleCombine style left none combine = ((left, none), .error .consumed) := rfl

/-- Independent right capabilities retain their state on success and failure. -/
theorem setStyleCombine_right_retained (style : TableStyle) (left right : Option A)
    (combine : A → A → Except E A) :
    (setStyleCombine style left right combine).1.2 = right := by
  cases right <;> rfl

/-- Exact backend refusal preserves both independent owners for explicit retry. -/
theorem setStyleCombine_failure (style : TableStyle) (left right : A)
    (combine : A → A → Except E A) (cause : E)
    (refused : combine left right = .error cause) :
    setStyleCombine style (some left) (some right) combine =
      ((some left, some right), .error (.callback cause)) := by
  simp [setStyleCombine, styleStep, refused]

/-- Every presentation delegates exactly one captured-snapshot merge to styleStep. -/
theorem setStyleCombine_delegates (style : TableStyle) (left right : A)
    (combine : A → A → Except E A) :
    setStyleCombine style (some left) (some right) combine =
      (((styleStep style (some left) (fun before => combine before right)).1, some right),
       (styleStep style (some left) (fun before => combine before right)).2) := rfl

/-- A successful pure merge preserves both original snapshots. -/
theorem setStyleCombine_pure (left right after : A) (combine : A → A → Except E A)
    (merged : combine left right = .ok after) :
    setStyleCombine .pure (some left) (some right) combine =
      ((some left, some right), .ok after) := by simp [setStyleCombine, styleStep, merged]

/-- A successful mutable merge replaces only the left owned payload. -/
theorem setStyleCombine_mutable (left right after : A) (combine : A → A → Except E A)
    (merged : combine left right = .ok after) :
    setStyleCombine .mutable (some left) (some right) combine =
      ((some after, some right), .ok after) := by simp [setStyleCombine, styleStep, merged]

/-- A successful linear merge retires left aliases and retains the independent right. -/
theorem setStyleCombine_linear (left right after : A) (combine : A → A → Except E A)
    (merged : combine left right = .ok after) :
    setStyleCombine .linear (some left) (some right) combine =
      ((none, some right), .ok after) := by simp [setStyleCombine, styleStep, merged]

/-- Changing style does not change merge results or the original failure cause. -/
theorem setStyleCombine_result (first second : TableStyle) (left right : Option A)
    (combine : A → A → Except E A) :
    (setStyleCombine first left right combine).2 = (setStyleCombine second left right combine).2 := by
  cases right with
  | none => rfl
  | some other => exact styleStep_result first second left (fun before => combine before other)

/-- Set presentation needs no carrier conversion: all twenty-five transfers use
exactly the existing representation-independent prepared transfer theorem. -/
theorem setStyle_transfer (source target : TablePresentation) (value : A) :
    prepareStyleConvert (E := E) source (some value) (fun payload => .ok (target, payload)) =
      (if source.base = .pure then some value else none, .ok (target, value)) :=
  presentation_conversion source target value

/-- Element observation erases only Unit payloads, retaining original key objects. -/
def setElements (rows : List (K × Unit)) : List K := rows.map Prod.fst

/-- Element count and backend order are unchanged, without any equality premise. -/
theorem setElements_length (rows : List (K × Unit)) : (setElements rows).length = rows.length := by
  simp [setElements]

/-- Left fold projects callback arity without rebuilding a set or comparing keys. -/
theorem setElements_foldl (rows : List (K × Unit)) (f : K → R → R) (seed : R) :
    rows.foldl (fun acc entry => f entry.1 acc) seed =
      (setElements rows).foldl (fun acc key => f key acc) seed := by
  induction rows generalizing seed with
  | nil => rfl
  | cons entry rest ih => simpa [setElements] using ih (f entry.1 seed)

/-- Right fold retains the backend's original order and callback nesting. -/
theorem setElements_foldr (rows : List (K × Unit)) (f : K → R → R) (seed : R) :
    rows.foldr (fun entry acc => f entry.1 acc) seed = (setElements rows).foldr f seed := by
  induction rows with
  | nil => rfl
  | cons entry rest ih => simp [setElements, ih]

/-- A delayed element pull maps the same guarded table cursor, not another engine. -/
def pullSetElement (cursor : StyleCursor K Unit) (current : List Nat) :
    Except Unit (Option K × StyleCursor K Unit) × Nat :=
  let result := pullStyleCursor cursor current
  (result.1.map (fun (entry, next) => (entry.map Prod.fst, next)), result.2)

/-- Current metadata exposes the original opaque element and one backend pull. -/
theorem pullSetElement_current (issued : List Nat) (key : K) (rest : List (K × Unit)) :
    pullSetElement ⟨issued, (key, ()) :: rest⟩ issued = (.ok (some key, ⟨issued, rest⟩), 1) := by
  simp [pullSetElement, pullStyleCursor, checkedTablePull, tableCursorPull, Except.map]

/-- Stale set/table origins prevent delegation, including exhausted cursors. -/
theorem pullSetElement_stale (cursor : StyleCursor K Unit) (current : List Nat)
    (stale : cursor.issued ≠ current) :
    pullSetElement cursor current = (.error (), 0) := by
  simp [pullSetElement, pullStyleCursor_stale cursor current stale, Except.map]

/-- EOF remains an origin-checked observation after projecting away Unit. -/
theorem pullSetElement_eof (issued current : List Nat) :
    pullSetElement (K := K) ⟨issued, []⟩ current =
      if issued = current then (.ok (none, ⟨issued, []⟩), 1) else (.error (), 0) := by
  by_cases h : issued = current <;>
    simp [pullSetElement, pullStyleCursor, checkedTablePull, tableCursorPull, h, Except.map]

/-- A specialized set Type must refine, rather than replace, backing admission. -/
def admitSetRoot (backing specialized : A → Bool) (failure : E) (value : A) : Except E A :=
  if backing value && specialized value then .ok value else .error failure

/-- A broad custom recognizer cannot authorize an invalid backing carrier. -/
theorem admitSetRoot_backing_refusal (backing specialized : A → Bool) (failure : E) (value : A)
    (invalid : backing value = false) :
    admitSetRoot backing specialized failure value = .error failure := by simp [admitSetRoot, invalid]

/-- A valid table root still has to satisfy the specialized set recognizer. -/
theorem admitSetRoot_specialized_refusal (backing specialized : A → Bool) (failure : E) (value : A)
    (invalid : specialized value = false) :
    admitSetRoot backing specialized failure value = .error failure := by simp [admitSetRoot, invalid]

/-- Output refinement refusal precedes the existing owner commit for every style. -/
theorem setStyle_refinement_refusal (style : TableStyle) (before after : A)
    (update : A → Except E A) (backing specialized : A → Bool) (failure : E)
    (updated : update before = .ok after) (invalid : specialized after = false) :
    prepareStyleStep style (some before) update (admitSetRoot backing specialized failure) =
      (some before, .error (.callback failure)) :=
  prepareStyleStep_refused style before after update _ failure updated
    (admitSetRoot_specialized_refusal backing specialized failure after invalid)

/-- Direct Set issuance uses the existing cursor and complete Set admission before
backend enumeration. Persistent carriers and faithful runtime Iterator dispatch
remain premises; admission recognizes opaque Function leaves without cooking. -/
def issueSetCursor (issued current : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × Unit))) :
    Except (TableObservationFailure E) (StyleCursor K Unit) :=
  issueTableCursor issued current snapshot admit enumerate

/-- A refused Set cannot issue a cursor or call its backend enumerator. -/
theorem issueSetCursor_refused (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × Unit)))
    (cause : E) (refused : admit snapshot = .error cause) :
    issueSetCursor versions versions snapshot admit enumerate = .error (.backend cause) := by
  simp [issueSetCursor, issueTableCursor, observeTable, observeStyle, refused, Except.bind,
    Except.mapError, Except.map]

/-- Complete admission retains exact keys and backend order, including false keys. -/
theorem issueSetCursor_ready (versions : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × Unit)))
    (rows : List (K × Unit)) (accepted : admit snapshot = .ok ())
    (enumerated : enumerate snapshot = .ok rows) :
    issueSetCursor versions versions snapshot admit enumerate = .ok ⟨versions, rows⟩ := by
  simp [issueSetCursor, issueTableCursor, observeTable, observeStyle, accepted, enumerated,
    Except.bind, Except.mapError, Except.map]

/-- Issuance validates revisions before admission or backend enumeration. -/
theorem issueSetCursor_stale (issued current : List Nat) (snapshot : A)
    (admit : A → Except E Unit) (enumerate : A → Except E (List (K × Unit)))
    (stale : issued ≠ current) :
    issueSetCursor issued current snapshot admit enumerate = .error .stale := by
  simp [issueSetCursor, issueTableCursor, observeTable, observeStyle, stale, Except.map]



/-- Set admission reuses the Table reentry guard around BOTH backing and refined
recognition. Identity tokens and dynamic scope restoration are host premises;
this finite model does not certify termination of arbitrary recognizers. -/
def guardSetAdmission (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure : E) (backing specialized : List (Nat × Nat) → Except E Unit) : Except E Unit :=
  guardTableAdmission active request failure (fun _ => do
    backing (request :: active)
    specialized (request :: active))

/-- A repeated Set request refuses before backing or specialized recognition. -/
theorem guardSetAdmission_reentry (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure : E) (backing specialized : List (Nat × Nat) → Except E Unit)
    (present : request ∈ active) :
    guardSetAdmission active request failure backing specialized = .error failure := by
  simp [guardSetAdmission, guardTableAdmission, present]

/-- Fresh admission exposes the same extended scope to both recognition stages. -/
theorem guardSetAdmission_fresh (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure : E) (backing specialized : List (Nat × Nat) → Except E Unit)
    (fresh : request ∉ active) :
    guardSetAdmission active request failure backing specialized =
      (backing (request :: active)).bind (fun _ => specialized (request :: active)) := by
  simp [guardSetAdmission, guardTableAdmission, fresh]
  rfl

/-- A backing refusal suppresses refinement and retains its exact cause. -/
theorem guardSetAdmission_backing_refused (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure cause : E) (backing specialized : List (Nat × Nat) → Except E Unit)
    (fresh : request ∉ active) (refused : backing (request :: active) = .error cause) :
    guardSetAdmission active request failure backing specialized = .error cause := by
  simp [guardSetAdmission_fresh active request failure backing specialized fresh, refused, Except.bind]

/-- Successful backing recognition delegates the exact specialized result. -/
theorem guardSetAdmission_backing_ready (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure : E) (backing specialized : List (Nat × Nat) → Except E Unit)
    (fresh : request ∉ active) (accepted : backing (request :: active) = .ok ()) :
    guardSetAdmission active request failure backing specialized = specialized (request :: active) := by
  simp [guardSetAdmission_fresh active request failure backing specialized fresh, accepted, Except.bind]

/-- Direct recursive refinement encounters the original request before replaying
either recognizer. The successful outer backing stage is the only premise. -/
theorem guardSetAdmission_direct_cycle (active : List (Nat × Nat)) (request : Nat × Nat)
    (failure : E) (backing nextBacking nextSpecialized : List (Nat × Nat) → Except E Unit)
    (fresh : request ∉ active) (accepted : backing (request :: active) = .ok ()) :
    guardSetAdmission active request failure backing
      (fun scope => guardSetAdmission scope request failure nextBacking nextSpecialized) =
      .error failure := by
  rw [guardSetAdmission_backing_ready _ _ _ _ _ fresh accepted]
  exact guardSetAdmission_reentry _ _ _ _ _ (by simp)

/-- In a mutual cycle, the second fresh receiver is admitted but returning to
the first receiver/root refuses, without conflating their shared snapshot. -/
theorem guardSetAdmission_mutual_cycle (active : List (Nat × Nat)) (first second : Nat × Nat)
    (failure : E) (firstBacking secondBacking nextBacking nextSpecialized : List (Nat × Nat) → Except E Unit)
    (firstFresh : first ∉ active) (secondFresh : second ∉ first :: active)
    (firstAccepted : firstBacking (first :: active) = .ok ())
    (secondAccepted : secondBacking (second :: first :: active) = .ok ()) :
    guardSetAdmission active first failure firstBacking
      (fun scope => guardSetAdmission scope second failure secondBacking
        (fun inner => guardSetAdmission inner first failure nextBacking nextSpecialized)) =
      .error failure := by
  rw [guardSetAdmission_backing_ready _ _ _ _ _ firstFresh firstAccepted]
  rw [guardSetAdmission_backing_ready _ _ _ _ _ secondFresh secondAccepted]
  exact guardSetAdmission_reentry _ _ _ _ _ (by simp)

/-- The complete observation boundary suppresses reads and downstream consumers
when the shared Set guard refuses. No rollback of earlier callback effects follows. -/
theorem observeSetAdmission_refused (versions : List Nat) (snapshot : A)
    (active : List (Nat × Nat)) (request : Nat × Nat) (failure cause : E)
    (backing specialized : List (Nat × Nat) → Except E Unit) (query : A → Except E R)
    (refused : guardSetAdmission active request failure backing specialized = .error cause) :
    observeTable versions versions snapshot
      (fun _ => guardSetAdmission active request failure backing specialized) query =
      .error (.backend cause) :=
  observeTable_refused _ _ _ _ _ refused

end LeanPoo.Functional.OrderedDictionary
