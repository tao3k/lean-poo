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

end LeanPoo.Functional.OrderedDictionary
