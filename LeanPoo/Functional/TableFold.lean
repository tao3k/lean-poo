import LeanPoo.Functional.TableRevision
import LeanPoo.Functional.TableIndex

/-! Complete final-root admission for incremental aggregate publication. This is
finite future work for explicit persistent carriers and supplied recognizers. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Stage privately, recognize the final root, then advance the aggregate.
No intermediate root is required to satisfy a whole-table refinement. -/
def admitFoldUpdate (install : Except E T) (admit : T → Except E Unit)
    (advance : T → Except E A) : Except E (T × A) :=
  install.bind fun table => (admit table).bind fun _ => (advance table).map (table, ·)

/-- An installation conflict retains its exact cause and suppresses later phases. -/
theorem admitFoldUpdate_install_refused (admit : T → Except E Unit)
    (advance : T → Except E A) (cause : E) :
    admitFoldUpdate (.error cause) admit advance = .error cause := rfl

/-- Root refusal occurs before aggregate advancement; neither private result escapes. -/
theorem admitFoldUpdate_root_refused (admit : T → Except E Unit)
    (advance : T → Except E A) (table : T) (cause : E)
    (refused : admit table = .error cause) :
    admitFoldUpdate (.ok table) admit advance = .error cause := by
  simp [admitFoldUpdate, refused, Except.bind]

/-- A successful operation preserves the actual admitted root and aggregate. -/
theorem admitFoldUpdate_ready (admit : T → Except E Unit) (advance : T → Except E A)
    (table : T) (value : A) (accepted : admit table = .ok ())
    (advanced : advance table = .ok value) :
    admitFoldUpdate (.ok table) admit advance = .ok (table, value) := by
  simp [admitFoldUpdate, accepted, advanced, Except.bind, Except.map]

/-- Recognition is an explicit premise, not inferred from child membership,
representation correspondence, or a previous root's acceptance. -/
theorem admitFoldUpdate_valid (install : Except E T) (admit : T → Except E Unit)
    (advance : T → Except E A) (Valid : T → Prop)
    (faithful : ∀ root, admit root = .ok () → Valid root) (table : T) (value : A)
    (published : admitFoldUpdate install admit advance = .ok (table, value)) : Valid table := by
  cases hi : install with
  | error cause => simp [admitFoldUpdate, hi, Except.bind] at published
  | ok root =>
    cases ha : admit root with
    | error cause => simp [admitFoldUpdate, hi, ha, Except.bind] at published
    | ok acceptedUnit =>
      cases acceptedUnit
      cases hv : advance root with
      | error cause => simp [admitFoldUpdate, hi, ha, hv, Except.bind, Except.map] at published
      | ok result =>
        simp [admitFoldUpdate, hi, ha, hv, Except.bind, Except.map] at published
        rcases published with ⟨rfl, rfl⟩
        exact faithful root ha

/-- Existing ordered conflicts and exact recognizer causes remain distinguishable.
Sparse contributions are demanded only after the complete successor is admitted. -/
def checkedFold [DecidableEq K] [DecidableEq V]
    (score : K → V → Int) (admit : (K → Option V) → Except E Unit)
    (edits : List (Change K V)) (before : K → Option V) (acc : Int) :
    Except (Sum K E) ((K → Option V) × Int) :=
  admitFoldUpdate ((applyChanges edits before).mapError Sum.inl)
    (fun root => (admit root).mapError Sum.inr)
    (fun _ => .ok (foldChanges score edits acc))

/-- Final recognition and the existing full-fold oracle agree on accepted updates.
The inventory and aggregate law remain explicit, separate from recognition. -/
theorem checkedFold_correct [DecidableEq K] [DecidableEq V]
    (inventory : List K) (unique : inventory.Nodup) (score : K → V → Int)
    (admit : (K → Option V) → Except E Unit) (edits : List (Change K V))
    (covered : ∀ edit ∈ edits, edit.key ∈ inventory) (before after : K → Option V)
    (installed : applyChanges edits before = .ok after) (accepted : admit after = .ok ()) :
    checkedFold score admit edits before (foldView inventory score before) =
      .ok (after, foldView inventory score after) := by
  have correct := foldChanges_correct inventory unique score edits covered before after installed
  simp [checkedFold, installed, accepted, admitFoldUpdate, correct,
    Except.bind, Except.map, Except.mapError]

/-- Inverse recovery requires admission of the recovered original root, rather than
assuming a target constraint follows automatically from bijective child mappings. -/
theorem checkedFold_inverse [DecidableEq K] [DecidableEq V]
    (score : K → V → Int) (admit : (K → Option V) → Except E Unit)
    (edits : List (Change K V)) (before after : K → Option V) (acc : Int)
    (installed : applyChanges edits before = .ok after) (accepted : admit before = .ok ()) :
    checkedFold score admit (inverseChanges edits) after (foldChanges score edits acc) =
      .ok (before, acc) := by
  have inverse := applyChanges_inverse edits before after installed
  simp [checkedFold, inverse, accepted, admitFoldUpdate, foldChanges_inverse,
    Except.bind, Except.map, Except.mapError]

/-- Source fold completion precedes conversion and complete target admission.
The accepted aggregate is reused exactly, without a second aggregate initializer. -/
def admitFoldTransfer (source : Except E (S × A)) (convert : S → Except E T)
    (admit : T → Except E Unit) : Except E (T × A) :=
  source.bind fun result => admitFoldUpdate (convert result.1) admit (fun _ => .ok result.2)

/-- Source failure suppresses target conversion and recognition without changing its cause. -/
theorem admitFoldTransfer_source_refused (convert : S → Except E T)
    (admit : T → Except E Unit) (cause : E) :
    admitFoldTransfer (.error cause : Except E (S × A)) convert admit = .error cause := rfl

/-- Even lawful translated bindings must pass the independent whole-target constraint. -/
theorem admitFoldTransfer_target_refused (source : S) (value : A)
    (convert : S → Except E T) (admit : T → Except E Unit) (target : T) (cause : E)
    (converted : convert source = .ok target) (refused : admit target = .error cause) :
    admitFoldTransfer (.ok (source, value)) convert admit = .error cause := by
  simp [admitFoldTransfer, converted, admitFoldUpdate_root_refused admit _ target cause refused,
    Except.bind]

/-- Accepted translation preserves an opaque aggregate, including checked Functions. -/
theorem admitFoldTransfer_ready (source : S) (value : A)
    (convert : S → Except E T) (admit : T → Except E Unit) (target : T)
    (converted : convert source = .ok target) (accepted : admit target = .ok ()) :
    admitFoldTransfer (.ok (source, value)) convert admit = .ok (target, value) := by
  simp [admitFoldTransfer, converted, admitFoldUpdate, accepted,
    Except.bind, Except.map]


/-- A key-space capability changes registry payloads independently of business
rows. Key equality is transported by the same explicit bijection, not inferred. -/
def keySpaceView (keys : Prototype.DictionaryBridge K L) (registry : K → Option A) : L → Option A :=
  transportView keys (Prototype.DictionaryBridge.identity A) registry

/-- Registry writes preserve arbitrary owner payloads through an explicit key map. -/
theorem keySpaceView_replace [DecidableEq K] [DecidableEq L]
    (keys : Prototype.DictionaryBridge K L) (registry : K → Option A) (key : K) (value : Option A) :
    keySpaceView keys (replace registry key value) =
      replace (keySpaceView keys registry) (keys.toFields key) value := by
  simpa [keySpaceView, Prototype.DictionaryBridge.identity] using
    transport_replace keys (Prototype.DictionaryBridge.identity A) registry key value

/-- A touched key retains its last optional value. Some none means a known
removal; none means no overlay entry, so stored false cannot collapse either. -/
def overlayView (base : K → Option V) (pending : K → Option (Option V)) : K → Option V :=
  fun key => (pending key).getD (base key)

/-- One overlay update has the same observation as a persistent table write. -/
theorem overlayView_replace [DecidableEq K] (base : K → Option V)
    (pending : K → Option (Option V)) (key : K) (value : Option V) :
    overlayView base (replace pending key (some value)) = replace (overlayView base pending) key value := by
  funext query
  by_cases same : query = key <;> simp [overlayView, replace, same]

/-- Final write-only observation; intermediate roots need no whole-family admission. -/
def writeBindings [DecidableEq K] (writes : List (K × Option V)) (view : K → Option V) : K → Option V :=
  writes.foldl (fun current write => replace current write.1 write.2) view

/-- Retain every requested write in order while capturing expectations from a
private overlay or the original target. Old values need no conversion callback. -/
def traceBindings [DecidableEq K] (writes : List (K × Option V)) (base : K → Option V)
    (pending : K → Option (Option V)) : List (Change K V) :=
  match writes with
  | [] => []
  | (key, value) :: rest =>
    ⟨key, overlayView base pending key, value⟩ ::
      traceBindings rest base (replace pending key (some value))

/-- The entire traced request installs as one ordered delta, including repeated
keys, cancellation, deletion/reinsertion and stored false. -/
theorem traceBindings_apply [DecidableEq K] [DecidableEq V] (writes : List (K × Option V))
    (base : K → Option V) (pending : K → Option (Option V)) :
    applyChanges (traceBindings writes base pending) (overlayView base pending) =
      .ok (writeBindings writes (overlayView base pending)) := by
  induction writes generalizing pending with
  | nil => rfl
  | cons write rest ih =>
    rcases write with ⟨key, value⟩
    simp only [traceBindings, applyChanges, ite_true, writeBindings, List.foldl_cons]
    rw [← overlayView_replace]
    exact ih _

/-- A fresh overlay starts at the admitted paired target without enumerating it. -/
theorem traceBindings_fresh [DecidableEq K] [DecidableEq V] (writes : List (K × Option V))
    (base : K → Option V) :
    applyChanges (traceBindings writes base (fun _ => none)) base = .ok (writeBindings writes base) := by
  have empty : overlayView base (fun _ => none) = base := by funext key; rfl
  simpa only [empty] using traceBindings_apply writes base (fun _ => none)

/-- Key order and multiplicity are retained rather than squashed to endpoints. -/
theorem traceBindings_keys [DecidableEq K] (writes : List (K × Option V))
    (base : K → Option V) (pending : K → Option (Option V)) :
    (traceBindings writes base pending).map Change.key = writes.map Prod.fst := by
  induction writes generalizing pending with
  | nil => rfl
  | cons write rest ih => cases write; simp [traceBindings, ih]

/-- Exactly one edit is emitted per requested write, independent of snapshot size. -/
theorem traceBindings_length [DecidableEq K] (writes : List (K × Option V))
    (base : K → Option V) (pending : K → Option (Option V)) :
    (traceBindings writes base pending).length = writes.length := by
  induction writes generalizing pending with
  | nil => rfl
  | cons write rest ih => cases write; simp [traceBindings, ih]

/-- Tracing drops supplied old values because the source already checked them;
the actual target expectations are recovered from its own issued snapshot. -/
theorem writeBindings_changes [DecidableEq K] (edits : List (Change K V)) (view : K → Option V) :
    writeBindings (edits.map (fun edit => (edit.key, edit.after))) view = writeChanges edits view := by
  induction edits generalizing view with
  | nil => rfl
  | cons edit rest ih => simpa [writeBindings, writeChanges] using ih (replace view edit.key edit.after)

/-- With an admitted source delta and lawful paired target, the traced target
installer gives exactly the transported final source, without converting old rows. -/
theorem traceBindings_transport [DecidableEq K] [DecidableEq V] [DecidableEq L] [DecidableEq W]
    (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (edits : List (Change K V)) (source after : K → Option V) (target : L → Option W)
    (paired : target = transportView keys values source)
    (installed : applyChanges edits source = .ok after) :
    applyChanges (traceBindings ((transportChanges keys values edits).map
      (fun edit => (edit.key, edit.after))) target (fun _ => none)) target =
      .ok (transportView keys values after) := by
  rw [traceBindings_fresh, writeBindings_changes]
  subst target
  rw [transport_writeChanges, applyChanges_writeChanges edits source after installed]

/-- Correlated indexes use the existing final-state two-phase update after one
complete traced installation, so transient duplicate identifiers need no admission. -/
theorem traceBindings_index [DecidableEq K] [DecidableEq V] [DecidableEq I]
    (writes : List (K × Option V)) (base : K → Option V) (project : K → V → I) :
    reviseIndex (writes.map Prod.fst) project (writeBindings writes base) (indexView project base) =
      indexView project (writeBindings writes base) := by
  apply reviseIndex_correct
  intro key outside
  apply applyChanges_frame _ base _ (traceBindings_fresh writes base) key
  intro edit member same
  apply outside
  rw [← traceBindings_keys writes base (fun _ => none)]
  exact List.mem_map.mpr ⟨edit, member, same.symm⟩

/-- Count overlay entries (one read and one write each) and encountered replacement
conversions. Registry
construction, complete root/cache admission, backend lookup and GC remain separate. -/
def traceBindingsWork (writes : List (K × Option V)) : Nat × Nat :=
  (writes.length, (writes.filter (fun write => write.2.isSome)).length)

/-- The overlay emits one edit and converts at most one present replacement per
request; it does not infer constant-time backend or whole-workflow costs. -/
theorem traceBindingsWork_bound (writes : List (K × Option V)) :
    (traceBindingsWork writes).1 = writes.length ∧ (traceBindingsWork writes).2 ≤ writes.length := by
  exact ⟨rfl, List.length_filter_le _ _⟩


/-- A representation view can validate public expectations first, then trace one
inverse-mapped source install. Intermediate point writes and old-value conversion
are unnecessary; existing representation and installer laws supply the result. -/
theorem traceBindings_represented [DecidableEq K] [DecidableEq V] [DecidableEq L] [DecidableEq W]
    (keys : Prototype.DictionaryBridge K L) (values : Prototype.DictionaryBridge V W)
    (edits : List (Change L W)) (source : K → Option V) (presented after : L → Option W)
    (paired : presented = transportView keys values source)
    (installed : applyChanges edits presented = .ok after) :
    applyChanges (traceBindings ((transportChanges keys.inverse values.inverse edits).map
      (fun edit => (edit.key, edit.after))) source (fun _ => none)) source =
      .ok (transportView keys.inverse values.inverse after) := by
  have inversePair : source = transportView keys.inverse values.inverse presented := by
    rw [paired]
    exact (transportView_inverse keys values source).symm
  exact traceBindings_transport keys.inverse values.inverse edits presented after source inversePair installed

/-- Fold each nonempty owner bucket; a zero aggregate is still a present group.
The finite inventory covers live owners and fixes the reference traversal order. -/
def foldGroups (owners : List K) (summarize : (K → Option V) → A)
    (groups : I → K → Option V) (bucket : I) : Option A :=
  if owners.any (fun key => (groups bucket key).isSome) then some (summarize (groups bucket)) else none

/-- Presence depends on owners, never on the aggregate value being nonzero. -/
theorem foldGroups_present (owners : List K) (summarize : (K → Option V) → A)
    (groups : I → K → Option V) (bucket : I) :
    (foldGroups owners summarize groups bucket).isSome = true ↔
      ∃ key ∈ owners, (groups bucket key).isSome = true := by
  simp [foldGroups, List.any_eq_true]

/-- Any surviving owner keeps even an opaque or zero-valued aggregate present. -/
theorem foldGroups_survives (owners : List K) (summarize : (K → Option V) → A)
    (groups : I → K → Option V) (bucket : I) (key : K)
    (listed : key ∈ owners) (live : (groups bucket key).isSome = true) :
    foldGroups owners summarize groups bucket = some (summarize (groups bucket)) := by
  have present : owners.any (fun key => (groups bucket key).isSome) = true :=
    List.any_eq_true.mpr ⟨key, listed, live⟩
  simp [foldGroups, present]

/-- No live owners means no group; the empty fold's zero is not published. -/
theorem foldGroups_empty (owners : List K) (summarize : (K → Option V) → A)
    (groups : I → K → Option V) (bucket : I)
    (empty : ∀ key ∈ owners, groups bucket key = none) :
    foldGroups owners summarize groups bucket = none := by
  have absent : owners.any (fun key => (groups bucket key).isSome) = false := by
    simp only [List.any_eq_false]
    intro key listed
    simp [empty key listed]
  simp [foldGroups, absent]

/-- Existing selective index repair supplies the exact final buckets to aggregation.
No law for an inverse or commutative aggregate is needed for this equality. -/
theorem foldGroups_revise [DecidableEq K] [DecidableEq I]
    (owners keys : List K) (summarize : (K → Option V) → A)
    (project : K → V → I) (before after : K → Option V)
    (frame : ∀ key, key ∉ keys → after key = before key) :
    foldGroups owners summarize (reviseIndex keys project after (indexView project before)) =
      foldGroups owners summarize (indexView project after) := by
  rw [reviseIndex_correct keys project before after frame]

/-- The touched group inventory contains both original and final memberships of
changed rows. Therefore every other complete bucket is observationally unchanged. -/
theorem grouped_bucket_frame [DecidableEq I]
    (buckets : List I) (project : K → V → I) (before after : K → Option V)
    (covered : ∀ key, before key ≠ after key → ∀ row,
      (before key = some row ∨ after key = some row) → project key row ∈ buckets)
    (bucket : I) (outside : bucket ∉ buckets) :
    indexView project before bucket = indexView project after bucket := by
  funext key
  by_cases same : before key = after key
  · simp [indexView, same]
  · have excludes (row : V) (live : before key = some row ∨ after key = some row) :
        project key row ≠ bucket := by
      intro equal
      exact outside (equal ▸ covered key same row live)
    have old : indexView project before bucket key = none := by
      cases h : before key with
      | none => simp [indexView, h]
      | some row => simp [indexView, h, excludes row (Or.inl h)]
    have new : indexView project after bucket key = none := by
      cases h : after key with
      | none => simp [indexView, h]
      | some row => simp [indexView, h, excludes row (Or.inr h)]
    rw [old, new]

/-- Unaffected groups retain their cached aggregate without evaluating summarize. -/
def repairGroupFolds [DecidableEq I] (buckets : List I)
    (compute : I → Option A) (cache : I → Option A) : I → Option A :=
  fun bucket => if bucket ∈ buckets then compute bucket else cache bucket

/-- Refolding only old/final groups agrees with full regrouping and aggregation. -/
theorem repairGroupFolds_correct [DecidableEq I]
    (owners : List K) (buckets : List I) (summarize : (K → Option V) → A)
    (project : K → V → I) (before after : K → Option V)
    (covered : ∀ key, before key ≠ after key → ∀ row,
      (before key = some row ∨ after key = some row) → project key row ∈ buckets) :
    repairGroupFolds buckets (foldGroups owners summarize (indexView project after))
      (foldGroups owners summarize (indexView project before)) =
      foldGroups owners summarize (indexView project after) := by
  funext bucket
  by_cases h : bucket ∈ buckets
  · simp [repairGroupFolds, h]
  · simp only [repairGroupFolds]
    split
    · contradiction
    · unfold foldGroups
      rw [grouped_bucket_frame buckets project before after covered bucket h]

/-- A direct target delta over touched groups reconstructs the whole summary.
No target snapshot discovery or unconditional full target-key inventory is needed. -/
theorem foldGroups_delta [DecidableEq I] [DecidableEq A]
    (owners : List K) (buckets : List I) (unique : buckets.Nodup)
    (summarize : (K → Option V) → A) (project : K → V → I) (before after : K → Option V)
    (covered : ∀ key, before key ≠ after key → ∀ row,
      (before key = some row ∨ after key = some row) → project key row ∈ buckets) :
    applyChanges (diffChanges buckets (foldGroups owners summarize (indexView project before))
      (foldGroups owners summarize (indexView project after)))
      (foldGroups owners summarize (indexView project before)) =
      .ok (foldGroups owners summarize (indexView project after)) := by
  apply diff_complete buckets unique
  intro bucket outside
  unfold foldGroups
  rw [grouped_bucket_frame buckets project before after covered bucket outside]

/-- Source inversion restores grouped summaries even when migration erased an
entire group. This inverts the explicit delta, not the aggregate's information loss. -/
theorem foldGroups_inverse [DecidableEq K] [DecidableEq V] [DecidableEq I]
    (owners : List K) (summarize : (K → Option V) → A) (project : K → V → I)
    (edits : List (Change K V)) (before after : K → Option V)
    (ready : applyChanges edits before = .ok after) :
    (applyChanges (inverseChanges edits) after).map
      (fun restored => foldGroups owners summarize (indexView project restored)) =
      .ok (foldGroups owners summarize (indexView project before)) := by
  rw [applyChanges_inverse edits before after ready]
  rfl

end LeanPoo.Functional.OrderedDictionary
