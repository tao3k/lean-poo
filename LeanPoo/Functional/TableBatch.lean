import LeanPoo.Functional.TableRevision

/-! Ordered persistent revision batches. Composition retains intermediate writes,
conflicts and dependency observations; it does not squash edits to endpoints. -/
namespace LeanPoo.Functional.OrderedDictionary

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- Capture one optional replacement, omitting an unchanged binding just as finite
snapshot discovery does. Empty results are not read assertions on later bases. -/
def pointChanges (before : K → Option V) (key : K) (after : Option V) : List (Change K V) :=
  if before key = after then [] else [⟨key, before key, after⟩]

/-- Callback refusal precedes publication of a captured request. The supplied
computation is evaluated once; applying its resulting edits never replays it. -/
def capturePointChanges {E : Type} (before : K → Option V) (key : K)
    (update : Option V → Except E (Option V)) : Except E (List (Change K V)) :=
  (update (before key)).map (pointChanges before key)

/-- One-key capture equals discovery restricted to that key and its optional write. -/
theorem pointChanges_diff (before : K → Option V) (key : K) (after : Option V) :
    pointChanges before key after = diffChanges [key] before (replace before key after) := by
  unfold diffChanges
  rw [List.filterMap_cons]
  simp only [replace, ite_true]
  unfold pointChanges
  split <;> rfl

/-- No trial carrier or whole-key inventory is required to describe this write. -/
theorem pointChanges_apply (before : K → Option V) (key : K) (after : Option V) :
    applyChanges (pointChanges before key after) before = .ok (replace before key after) := by
  rw [pointChanges_diff, apply_diffChanges [key] (by simp)]
  simp [replace]

/-- Captured point updates frame unrelated bindings, including a rebased snapshot. -/
theorem pointChanges_rebase (before rebased : K → Option V) (key : K) (after : Option V)
    (aligned : before key = rebased key) :
    applyChanges (pointChanges before key after) rebased = .ok (replace rebased key after) := by
  have same : pointChanges before key after = pointChanges rebased key after := by
    simp [pointChanges, aligned]
  rw [same, pointChanges_apply]

/-- A nonempty request retains its original expectation and exact conflicting key. -/
theorem pointChanges_stale (before rebased : K → Option V) (key : K) (after : Option V)
    (changed : before key ≠ after) (stale : rebased key ≠ before key) :
    applyChanges (pointChanges before key after) rebased = .error key := by
  simp [pointChanges, changed, applyChanges, stale]

/-- Inverting an accepted point request recovers the entire source observation. -/
theorem pointChanges_inverse (before : K → Option V) (key : K) (after : Option V) :
    applyChanges (inverseChanges (pointChanges before key after)) (replace before key after) =
      .ok before := applyChanges_inverse _ _ _ (pointChanges_apply before key after)

/-- Generation emits at most one edit, independently of the snapshot's domain size.
Admission, recognizers, metadata, lookup, callbacks and backend costs are separate. -/
theorem pointChanges_length (before : K → Option V) (key : K) (after : Option V) :
    (pointChanges before key after).length ≤ 1 := by
  unfold pointChanges; split <;> simp

/-- A failed callback returns only its unchanged cause, without a usable delta. -/
theorem capturePointChanges_failure {E : Type} (before : K → Option V) (key : K)
    (update : Option V → Except E (Option V)) (cause : E)
    (failed : update (before key) = .error cause) :
    capturePointChanges before key update = .error cause := by
  simp [capturePointChanges, failed, Except.map]

/-- Explicit key/value isomorphisms commute with capture, including no-op omission. -/
theorem pointChanges_transport {L W : Type} [DecidableEq L] [DecidableEq W]
    (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (before : K → Option V) (key : K) (after : Option V) :
    transportChanges keys values (pointChanges before key after) =
      pointChanges (transportView keys values before) (keys.toFields key) (after.map values.toFields) := by
  have same : (before key).map values.toFields = after.map values.toFields ↔ before key = after :=
    (transport_option_injective values).eq_iff
  simp only [pointChanges, transportView, keys.from_to, same]
  split <;> simp [transportChanges, transportChange]

/-- Flatten finite batches in caller order without reading any table snapshot. -/
def batchChanges (batches : List (List (Change K V))) : List (Change K V) :=
  batches.flatten

/-- Sequential specification: the first failing batch suppresses later batches. -/
def applyBatches (batches : List (List (Change K V))) (view : K → Option V) :
    Except K (K → Option V) :=
  match batches with
  | [] => .ok view
  | edits :: rest => (applyChanges edits view).bind (applyBatches rest)

/-- One private installation has exactly the sequential successes and first error.
No uniqueness premise excludes repeated, deleted or reinserted keys. -/
theorem batchChanges_correct (batches : List (List (Change K V))) (view : K → Option V) :
    applyChanges (batchChanges batches) view = applyBatches batches view := by
  induction batches generalizing view with
  | nil => rfl
  | cons edits rest ih =>
    simp only [batchChanges, List.flatten_cons, applyChanges_append, applyBatches]
    cases h : applyChanges edits view with
    | error key => rfl
    | ok next => exact ih next

omit [DecidableEq K] [DecidableEq V] in
/-- Grouping batches changes neither edit order nor intermediate expectations. -/
theorem batchChanges_append (left right : List (List (Change K V))) :
    batchChanges (left ++ right) = batchChanges left ++ batchChanges right := by
  simp [batchChanges, List.flatten_append]

omit [DecidableEq K] [DecidableEq V] in
/-- Rebatching already composed requests is associative as an exact edit list. -/
theorem batchChanges_associative (a b c : List (Change K V)) :
    batchChanges [batchChanges [a, b], c] = batchChanges [a, batchChanges [b, c]] := by
  simp [batchChanges, List.append_assoc]

omit [DecidableEq K] [DecidableEq V] in
/-- Undo reverses batch order and each internal revision, retaining all checks. -/
theorem batchChanges_inverse (batches : List (List (Change K V))) :
    inverseChanges (batchChanges batches) =
      batchChanges (batches.reverse.map inverseChanges) := by
  induction batches with
  | nil => rfl
  | cons edits rest ih =>
    simp only [batchChanges, List.flatten_cons] at *
    simp [inverseChanges, List.reverse_append, List.map_append] at ih ⊢
    exact ih

/-- A successful batch can be undone even when a key occurs in many revisions. -/
theorem applyBatches_inverse (batches : List (List (Change K V)))
    (before after : K → Option V) (success : applyBatches batches before = .ok after) :
    applyChanges (inverseChanges (batchChanges batches)) after = .ok before := by
  apply applyChanges_inverse
  rw [batchChanges_correct]
  exact success

omit [DecidableEq K] [DecidableEq V] in
/-- Explicit key/value isomorphisms commute with ordered batch composition. -/
theorem transport_batchChanges {L W : Type}
    (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (batches : List (List (Change K V))) :
    transportChanges keys values (batchChanges batches) =
      batchChanges (batches.map (transportChanges keys values)) := by
  induction batches with
  | nil => rfl
  | cons edits rest ih =>
    simp only [batchChanges, List.flatten_cons, List.map_cons, transportChanges,
      List.map_append] at *
    rw [ih]

omit [DecidableEq K] [DecidableEq V] in
/-- Integer aggregation processes every intermediate contribution in order. -/
theorem foldChanges_append (score : K → V → Int) (left right : List (Change K V)) (acc : Int) :
    foldChanges score (left ++ right) acc = foldChanges score right (foldChanges score left acc) := by
  simp [foldChanges, List.foldl_append]

/-- Full batch admission precedes aggregate projection; errors retain the first key. -/
theorem applyFold_batch_error (score : K → V → Int)
    (batches : List (List (Change K V))) (view : K → Option V) (acc : Int) (key : K)
    (failure : applyBatches batches view = .error key) :
    applyFold score (batchChanges batches) view acc = .error key := by
  simp only [applyFold, batchChanges_correct, failure, Except.map]

omit [DecidableEq K] [DecidableEq V] in
/-- Composition allocates one edit spine proportional to total edits; no table-size
term appears. This does not model backend writes, GC or compiler wall time. -/
theorem batchChanges_length (batches : List (List (Change K V))) :
    (batchChanges batches).length = (batches.map List.length).sum := by
  simp [batchChanges, List.length_flatten]

omit [DecidableEq K] [DecidableEq V] in
/-- Changed-binding aggregate work retains the existing two-projections-per-edit bound. -/
theorem batch_foldWork_bound (batches : List (List (Change K V))) :
    foldWork (batchChanges batches) ≤ 2 * (batches.map List.length).sum := by
  rw [← batchChanges_length]
  exact foldWork_bound _

/-- Prune removed keys only when absent from the completed staged table.
A deletion followed by reinsertion must retain its previous collision owner. -/
def pruneDeletedOwners {Owner : Type} (removed : List K) (final : K → Option V)
    (owners : K → Option Owner) : K → Option Owner :=
  match removed with
  | [] => owners
  | key :: rest => pruneDeletedOwners rest final
      (if (final key).isSome then owners else replace owners key none)

omit [DecidableEq V] in
/-- Any live final key retains its collision owner, however often deleted earlier. -/
theorem pruneDeletedOwners_live {Owner : Type} (removed : List K) (final : K → Option V)
    (owners : K → Option Owner) (query : K) (value : V) (live : final query = some value) :
    pruneDeletedOwners removed final owners query = owners query := by
  induction removed generalizing owners with
  | nil => rfl
  | cons key rest ih =>
    simp only [pruneDeletedOwners]
    rw [ih]
    by_cases same : query = key
    · subst key; simp [live]
    · split <;> simp [replace, same]

omit [DecidableEq K] [DecidableEq V] in
/-- Every origin, including an empty batch's origin, must remain current. -/
theorem batch_stampMatches {Id : Type} (origins : List (List Id))
    (expected current : Id → Option Nat) :
    stampMatches origins.flatten expected current =
      origins.all (fun scope => stampMatches scope expected current) := by
  induction origins with
  | nil => rfl
  | cons scope rest ih =>
    simp only [List.flatten_cons, stampMatches_append, List.all_cons, ih]

/-- Final observation of a finite admitted input stream. Repeated logical keys
retain the last yielded value; no intermediate business root is published. -/
def streamView (rows : List (K × V)) (before : K → Option V) : K → Option V :=
  rows.foldl (fun current row => replace current row.1 (some row.2)) before

omit [DecidableEq V] in
/-- Concatenated streams preserve ordered last-write interpretation. -/
theorem streamView_append (left right : List (K × V)) (before : K → Option V) :
    streamView (left ++ right) before = streamView right (streamView left before) := by
  simp [streamView, List.foldl_append]

omit [DecidableEq V] in
/-- The last occurrence wins independently of a backend list constructor's order. -/
theorem streamView_last (rows : List (K × V)) (before : K → Option V) (key : K) (value : V) :
    streamView (rows ++ [(key, value)]) before key = some value := by
  simp [streamView, replace]

omit [DecidableEq V] in
/-- A stream cannot change keys it never yielded. -/
theorem streamView_frame (rows : List (K × V)) (before : K → Option V) (key : K)
    (absent : key ∉ rows.map Prod.fst) : streamView rows before key = before key := by
  induction rows generalizing before with
  | nil => rfl
  | cons head tail ih =>
    have parts : key ≠ head.1 ∧ key ∉ tail.map Prod.fst := by
      simpa only [List.map_cons, List.mem_cons, not_or] using absent
    have apart := parts.1
    have rest := parts.2
    change streamView tail (replace before head.1 (some head.2)) key = before key
    rw [ih _ rest]
    simp [replace, apart]

/-- A faithful backend key registry supplies distinct touched keys. Discovery
uses only that explicit inventory, not a scan of the original snapshot. -/
def streamChanges (keys : List K) (rows : List (K × V)) (before : K → Option V) : List (Change K V) :=
  diffChanges keys before (streamView rows before)

/-- One ordinary installer reconstructs final stream observations. Distinctness
and coverage are explicit persistent key-registry laws, not inferred host equality. -/
theorem streamChanges_correct (keys : List K) (unique : keys.Nodup) (rows : List (K × V))
    (covered : ∀ row ∈ rows, row.1 ∈ keys) (before : K → Option V) :
    applyChanges (streamChanges keys rows before) before = .ok (streamView rows before) := by
  apply diff_complete keys unique before (streamView rows before)
  intro key absent
  apply Eq.symm
  apply streamView_frame
  intro present
  obtain ⟨row, member, same⟩ := List.mem_map.mp present
  exact absent (same ▸ covered row member)

/-- Ordinary inverse deltas recover the exact original lookup observation. -/
theorem streamChanges_inverse (keys : List K) (unique : keys.Nodup) (rows : List (K × V))
    (covered : ∀ row ∈ rows, row.1 ∈ keys) (before : K → Option V) :
    applyChanges (inverseChanges (streamChanges keys rows before)) (streamView rows before) = .ok before := by
  exact applyChanges_inverse _ _ _ (streamChanges_correct keys unique rows covered before)

/-- Delta cardinality is bounded by the distinct touched-key registry, not the
entire seed snapshot or the number of repeated input occurrences. -/
theorem streamChanges_length (keys : List K) (rows : List (K × V)) (before : K → Option V) :
    (streamChanges keys rows before).length ≤ keys.length := by
  exact List.length_filterMap_le _ _

omit [DecidableEq K] [DecidableEq V] in
/-- A faithful registry has no more distinct keys than the finite input has rows. -/
theorem streamKeys_length (keys : List K) (unique : keys.Nodup) (rows : List (K × V))
    (noExtra : ∀ key ∈ keys, key ∈ rows.map Prod.fst) : keys.length ≤ rows.length := by
  have bound := List.Nodup.length_le_of_subset unique noExtra
  simpa using bound

/-- Each finite event represents one Iterator pull plus Pair capture and child
admission. A failure stops before later events; arbitrary Iterator execution and
EOF behavior remain host-interface premises, not proven runtime claims. -/
def collectStreamEntries {E : Type} : List (Except E (K × V)) → Except E (List (K × V))
  | [] => .ok []
  | event :: rest => match event with
    | .error cause => .error cause
    | .ok row => match collectStreamEntries rest with
      | .error cause => .error cause
      | .ok rows => .ok (row :: rows)

omit [DecidableEq K] [DecidableEq V] in
/-- A rejected entry cannot be hidden by later overwrites or successful rows. -/
theorem collectStreamEntries_head_refused {E : Type} (cause : E)
    (rest : List (Except E (K × V))) :
    collectStreamEntries (.error cause :: rest) = .error cause := rfl

omit [DecidableEq K] [DecidableEq V] in
/-- Every successful event contributes exactly one captured Pair, before coalescing. -/
theorem collectStreamEntries_length {E : Type} (events : List (Except E (K × V)))
    (rows : List (K × V)) (success : collectStreamEntries events = .ok rows) :
    rows.length = events.length := by
  induction events generalizing rows with
  | nil => simpa [collectStreamEntries] using success
  | cons event rest ih =>
    cases event with
    | error cause => simp [collectStreamEntries] at success
    | ok row =>
      cases hr : collectStreamEntries rest with
      | error cause => simp [collectStreamEntries, hr] at success
      | ok tail =>
        have same : row :: tail = rows := by simpa [collectStreamEntries, hr] using success
        subst rows
        simpa using congrArg Nat.succ (ih tail hr)

/-- Seed admission precedes the finite read request; final business admission
runs once on the complete coalesced observation, never on intermediate roots. -/
def prepareStreamImport {E : Type} (admit : (K → Option V) → Except E Unit)
    (read : Unit → Except E (List (K × V))) (before : K → Option V) : Except E (K → Option V) :=
  match admit before with
  | .error cause => .error cause
  | .ok () => match read () with
    | .error cause => .error cause
    | .ok rows =>
      let after := streamView rows before
      match admit after with
      | .error cause => .error cause
      | .ok () => .ok after

omit [DecidableEq V] in
/-- An invalid seed refuses independently of any stream-reader computation. -/
theorem prepareStreamImport_seed_refused {E : Type} (admit : (K → Option V) → Except E Unit)
    (read : Unit → Except E (List (K × V))) (before : K → Option V) (cause : E)
    (refused : admit before = .error cause) :
    prepareStreamImport admit read before = .error cause := by simp [prepareStreamImport, refused]

omit [DecidableEq V] in
/-- Stream failure exposes no partial observation and keeps its original cause. -/
theorem prepareStreamImport_read_refused {E : Type} (admit : (K → Option V) → Except E Unit)
    (read : Unit → Except E (List (K × V))) (before : K → Option V) (cause : E)
    (ready : admit before = .ok ()) (refused : read () = .error cause) :
    prepareStreamImport admit read before = .error cause := by simp [prepareStreamImport, ready, refused]

omit [DecidableEq V] in
/-- Final policy refusal exposes no candidate, even though all rows were read. -/
theorem prepareStreamImport_final_refused {E : Type} (admit : (K → Option V) → Except E Unit)
    (read : Unit → Except E (List (K × V))) (before : K → Option V) (rows : List (K × V)) (cause : E)
    (ready : admit before = .ok ()) (readReady : read () = .ok rows)
    (refused : admit (streamView rows before) = .error cause) :
    prepareStreamImport admit read before = .error cause := by
  simp [prepareStreamImport, ready, readReady, refused]

omit [DecidableEq V] in
/-- Only the admitted complete result is exposed after a successful finite read. -/
theorem prepareStreamImport_ready {E : Type} (admit : (K → Option V) → Except E Unit)
    (read : Unit → Except E (List (K × V))) (before : K → Option V) (rows : List (K × V))
    (ready : admit before = .ok ()) (readReady : read () = .ok rows)
    (finalReady : admit (streamView rows before) = .ok ()) :
    prepareStreamImport admit read before = .ok (streamView rows before) := by
  simp [prepareStreamImport, ready, readReady, finalReady]

end LeanPoo.Functional.OrderedDictionary
