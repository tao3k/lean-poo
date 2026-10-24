import LeanPoo.Functional.TableMapping
import LeanPoo.Functional.TableFold

/-! Incremental heterogeneous entry projection over logical key observations.
Stable, key-local callbacks, faithful backend equality and persistent atomic
installers are explicit premises. Full recognition/backend/GC costs are separate
from the number of demanded projection callbacks. -/
namespace LeanPoo.Functional.OrderedDictionary

/-- Deletion demands no callback; a retained source row produces a checked Option. -/
def projectedEntry (project : K → V → Except E (Option (L × W)))
    (source : K → Option V) (key : K) : Except E (Option (L × W)) :=
  match source key with
  | none => .ok none
  | some value => project key value

/-- Refresh only the supplied first-touch inventory against the FINAL source.
The caller coalesces keys using source logical equality after source installation. -/
def refreshEntryCache [DecidableEq K] (project : K → V → Except E (Option (L × W)))
    (source : K → Option V) : List K → (K → Option (L × W)) → Except E (K → Option (L × W))
  | [], cache => .ok cache
  | key :: rest, cache => (projectedEntry project source key).bind fun next =>
      refreshEntryCache project source rest (replace cache key next)

/-- Every refreshed observation agrees with a full projection; untouched cached
rows remain exact, without requiring equality or normalization of Function leaves. -/
theorem refreshEntryCache_observe [DecidableEq K]
    (project : K → V → Except E (Option (L × W))) (source : K → Option V)
    (keys : List K) (cache result : K → Option (L × W))
    (ready : refreshEntryCache project source keys cache = .ok result) (query : K) :
    .ok (result query) = if query ∈ keys then projectedEntry project source query else .ok (cache query) := by
  induction keys generalizing cache with
  | nil => cases ready; simp
  | cons key rest ih =>
    cases hp : projectedEntry project source key with
    | error cause => simp [refreshEntryCache, hp, Except.bind] at ready
    | ok next =>
      have later : refreshEntryCache project source rest (replace cache key next) = .ok result := by
        simpa [refreshEntryCache, hp, Except.bind] using ready
      have observed := ih _ later
      by_cases member : query ∈ rest
      · simpa [member] using observed
      · by_cases same : query = key
        · subst query
          simpa [member, replace, hp] using observed
        · simpa [member, same, replace] using observed

/-- No touched-key inventory can alter an unselected cache observation. -/
theorem refreshEntryCache_frame [DecidableEq K]
    (project : K → V → Except E (Option (L × W))) (source : K → Option V)
    (keys : List K) (cache result : K → Option (L × W))
    (ready : refreshEntryCache project source keys cache = .ok result)
    (query : K) (outside : query ∉ keys) : result query = cache query := by
  have observed := refreshEntryCache_observe project source keys cache result ready query
  simpa [outside] using observed

/-- If the inventory covers source differences and the old cache was coherent,
selective refresh equals full recomputation at EVERY source key. -/
theorem refreshEntryCache_complete [DecidableEq K]
    (project : K → V → Except E (Option (L × W))) (before after : K → Option V)
    (keys : List K) (cache result : K → Option (L × W))
    (coherent : ∀ key, projectedEntry project before key = .ok (cache key))
    (covered : ∀ key, key ∉ keys → before key = after key)
    (ready : refreshEntryCache project after keys cache = .ok result) :
    ∀ key, projectedEntry project after key = .ok (result key) := by
  intro key
  have observed := refreshEntryCache_observe project after keys cache result ready key
  by_cases member : key ∈ keys
  · exact (by simpa [member] using observed.symm)
  · have same : projectedEntry project after key = projectedEntry project before key := by
      simp only [projectedEntry, ← covered key member]
    rw [same, coherent key]
    simpa [member] using observed.symm

/-- The existing changed-key frame theorem supplies precisely the inventory
coverage premise; the cache theorem does not assume arbitrary global freshness. -/
theorem projection_changes_covered [DecidableEq K] [DecidableEq V]
    (changes : List (Change K V)) (before after : K → Option V)
    (installed : applyChanges changes before = .ok after) (key : K)
    (outside : key ∉ changes.map Change.key) : before key = after key := by
  symm
  apply applyChanges_frame changes before after installed key
  intro change member same
  apply outside
  exact List.mem_map.mpr ⟨change, member, same.symm⟩

/-- Successful work demands one callback per final PRESENT touched key. With a
coalesced inventory this is at most one per logical source key, including batches. -/
def projectionCalls (source : K → Option V) (keys : List K) : Nat :=
  (keys.filter (fun key => (source key).isSome)).length

/-- Deleted rows and missing rows do not increase callback work. Recognition,
registry operations, index preparation and backend writes are charged separately. -/
theorem projectionCalls_bound (source : K → Option V) (keys : List K) :
    projectionCalls source keys ≤ keys.length := List.length_filter_le _ _

/-- All affected old owners are released before checking new rows. The retained
list represents the target registry's untouched owners, not an implementation scan. -/
def reserveProjection [DecidableEq L] (project : K → V → Except E (Option (L × W)))
    (retained : List (L × W)) (changed : List (K × V)) : Except (E ⊕ L) (List (L × W)) :=
  (mapEntries project changed (retained.map Prod.fst)).map (retained ++ ·)

/-- A reservation error cannot return even the otherwise valid retained prefix. -/
theorem reserveProjection_refused [DecidableEq L]
    (project : K → V → Except E (Option (L × W))) (retained : List (L × W))
    (changed : List (K × V)) (cause : E ⊕ L)
    (refused : mapEntries project changed (retained.map Prod.fst) = .error cause) :
    reserveProjection project retained changed = .error cause := by
  simp [reserveProjection, refused, Except.map]

/-- New/new and new/untouched collisions are both excluded from published keys.
Affected/affected swaps remain legal because their old owners are absent here. -/
theorem reserveProjection_unique [DecidableEq L]
    (project : K → V → Except E (Option (L × W))) (retained : List (L × W))
    (changed : List (K × V)) (added : List (L × W))
    (unique : (retained.map Prod.fst).Nodup)
    (ready : mapEntries project changed (retained.map Prod.fst) = .ok added) :
    ((retained ++ added).map Prod.fst).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨unique, mapEntries_nodup project changed _ added ready, ?_⟩
  intro key old other new same
  subst other
  exact mapEntries_avoids project changed _ added ready key new old

/-- Source admission precedes every projection; complete target installation and
recognition precede the returned source/cache/target triple. Exceptions remain
in their supplied sum domain, so callers distinguish conflicts and typed refusal. -/
def prepareProjectionRevision (install : Except E S) (admitSource : S → Except E Unit)
    (refresh : S → Except E C) (installTarget : C → Except E T)
    (admitTarget : T → Except E Unit) : Except E (S × C × T) :=
  install.bind fun source => (admitSource source).bind fun _ =>
    (refresh source).bind fun cache => (installTarget cache).bind fun target =>
      (admitTarget target).map fun _ => (source, cache, target)

/-- An invalid source suppresses projection, cache preparation and target writes. -/
theorem prepareProjectionRevision_source_refused (source : S)
    (admitSource : S → Except E Unit) (refresh : S → Except E C)
    (installTarget : C → Except E T) (admitTarget : T → Except E Unit) (cause : E)
    (refused : admitSource source = .error cause) :
    prepareProjectionRevision (.ok source) admitSource refresh installTarget admitTarget = .error cause := by
  simp [prepareProjectionRevision, refused, Except.bind]

/-- Failed target admission returns no successor cache or source. Reusing the
immutable predecessor with a new valid request is ordinary retry, not rollback
of external callback effects or a claim about concurrent publication. -/
theorem prepareProjectionRevision_target_refused (source : S) (cache : C) (target : T)
    (admitSource : S → Except E Unit) (refresh : S → Except E C)
    (installTarget : C → Except E T) (admitTarget : T → Except E Unit) (cause : E)
    (accepted : admitSource source = .ok ()) (refreshed : refresh source = .ok cache)
    (installed : installTarget cache = .ok target) (refused : admitTarget target = .error cause) :
    prepareProjectionRevision (.ok source) admitSource refresh installTarget admitTarget = .error cause := by
  simp [prepareProjectionRevision, accepted, refreshed, installed, refused, Except.bind, Except.map]

/-- A projection callback refusal cannot reach target installation or recognition. -/
theorem prepareProjectionRevision_refresh_refused (source : S)
    (admitSource : S → Except E Unit) (refresh : S → Except E C)
    (installTarget : C → Except E T) (admitTarget : T → Except E Unit) (cause : E)
    (accepted : admitSource source = .ok ()) (refused : refresh source = .error cause) :
    prepareProjectionRevision (.ok source) admitSource refresh installTarget admitTarget = .error cause := by
  simp [prepareProjectionRevision, accepted, refused, Except.bind]

/-- The published triple is exactly the admitted source, refreshed cache and
complete target; none is reconstructed after admission. -/
theorem prepareProjectionRevision_ready (source : S) (cache : C) (target : T)
    (admitSource : S → Except E Unit) (refresh : S → Except E C)
    (installTarget : C → Except E T) (admitTarget : T → Except E Unit)
    (accepted : admitSource source = .ok ()) (refreshed : refresh source = .ok cache)
    (installed : installTarget cache = .ok target) (checked : admitTarget target = .ok ()) :
    prepareProjectionRevision (.ok source) admitSource refresh installTarget admitTarget =
      .ok (source, cache, target) := by
  simp [prepareProjectionRevision, accepted, refreshed, installed, checked, Except.bind, Except.map]

/-- Retrying a failed pure preparation starts from the identical predecessor;
external callback effects, thread scheduling and IO are not rolled back. -/
def publishProjection (before : A) (prepared : Except E A) : A :=
  match prepared with | .error _ => before | .ok next => next

/-- No partial cache or carrier escapes a failed installation. -/
theorem publishProjection_refused (before : A) (cause : E) :
    publishProjection before (.error cause) = before := rfl

/-- A successful preparation publishes its complete result once. -/
theorem publishProjection_ready (before next : A) :
    publishProjection before (.ok next : Except E A) = next := rfl

/-- Deliver the exact admitted successor and already prepared target delta.
The continuation has no snapshot inventory or difference-discovery argument. -/
def deliverProjection (prepared : Except E (S × D))
    (receive : S → D → Except E A) : Except E A :=
  prepared.bind fun result => receive result.1 result.2

/-- Preparation refusal suppresses the receiver and preserves its exact cause. -/
theorem deliverProjection_refused (cause : E) (receive : S → D → Except E A) :
    deliverProjection (.error cause) receive = .error cause := rfl

/-- Successful delivery does not reconstruct or compare the delta or opaque state. -/
theorem deliverProjection_exact (state : S) (delta : D) (receive : S → D → Except E A) :
    deliverProjection (.ok (state, delta)) receive = receive state delta := rfl

/-- Default state-only use and standard multiple-value delivery retain the same
state and exact delta, including empty deltas carrying provenance. -/
theorem deliverProjection_values (state : S) (delta : D) :
    deliverProjection (.ok (state, delta)) (fun next edits => .ok (next, edits) :
      S → D → Except E (S × D)) = .ok (state, delta) := rfl

/-- Omitting the receiver keeps the exact ordinary state-only result. -/
theorem deliverProjection_state (state : S) (delta : D) :
    deliverProjection (.ok (state, delta)) (fun next _ => .ok next : S → D → Except E S) =
      .ok state := rfl

/-- Receiver refusal does not change its cause or publish a successor result. -/
theorem deliverProjection_receiver_refused (state : S) (delta : D) (cause : E) :
    deliverProjection (.ok (state, delta)) (fun _ _ => .error cause : S → D → Except E A) =
      .error cause := rfl

/-- Reuse the existing style update and its admission-bearing installer. The
canonical projection state remains distinct from a public root rebased over
unrelated rows. No new mutation protocol or inferred inverse is introduced. -/
def publishProjectionDelivery (prepared : Except E (S × D)) (style : TableStyle)
    (current : Option T) (install : T → D → Except E T) :
    Option T × Except (StyleFailure E) (S × D × T) :=
  match prepared with
  | .error cause => (current, .error (.callback cause))
  | .ok (next, delta) =>
    let result := styleStep style current (fun root => install root delta)
    (result.1, result.2.map (fun root => (next, delta, root)))

/-- Source/projection failure cannot demand any public target installation. -/
theorem publishProjectionDelivery_preparation_refused (cause : E) (style : TableStyle)
    (current : Option T) (install : T → D → Except E T) :
    publishProjectionDelivery (.error cause : Except E (S × D)) style current install =
      (current, .error (.callback cause)) := rfl

/-- Any target conflict or target admission failure retains the public owner and
returns no projection successor; retry may reuse the immutable predecessor. -/
theorem publishProjectionDelivery_install_refused (next : S) (delta : D)
    (style : TableStyle) (before : T) (install : T → D → Except E T) (cause : E)
    (refused : install before delta = .error cause) :
    publishProjectionDelivery (.ok (next, delta)) style (some before) install =
      (some before, .error (.callback cause)) := by
  simp [publishProjectionDelivery, styleStep, refused, Except.map]

/-- Consumed target ownership refuses before any target write, in every style. -/
theorem publishProjectionDelivery_consumed (next : S) (delta : D)
    (style : TableStyle) (install : T → D → Except E T) :
    publishProjectionDelivery (.ok (next, delta) : Except E (S × D)) style none install =
      (none, .error .consumed) := rfl

/-- Success preserves exact prepared state/delta and actual published root. Posh
and classy inherit the pure/mutable cases through the existing presentation map. -/
theorem publishProjectionDelivery_ready (next : S) (delta : D) (style : TableStyle)
    (before after : T) (install : T → D → Except E T)
    (ready : install before delta = .ok after) :
    publishProjectionDelivery (.ok (next, delta)) style (some before) install =
      ((match style with | .pure => some before | .mutable => some after | .linear => none),
        .ok (next, delta, after)) := by
  cases style <;> simp [publishProjectionDelivery, styleStep, ready, Except.map]

/-- Already prepared target edits reuse changed-key refusal. A conflict cannot
silently overwrite an independent publication even if private preparation passed. -/
theorem publishProjectionDelivery_changed [DecidableEq K] [DecidableEq V]
    (next : S) (style : TableStyle) (change : Change K V) (rest : List (Change K V))
    (current : K → Option V) (stale : current change.key ≠ change.before) :
    publishProjectionDelivery (.ok (next, change :: rest) : Except K (S × List (Change K V)))
      style (some current) (fun root edits => applyChanges edits root) =
        (some current, .error (.callback change.key)) :=
  publishProjectionDelivery_install_refused next _ style current _ change.key
    (reject_changed change rest current stale)

/-- Inversion uses the DELIVERED target edits, not an inferred inverse projection
or a discovered snapshot diff. The complete original public root is recovered. -/
theorem publishProjectionDelivery_inverse [DecidableEq K] [DecidableEq V]
    (next : S) (style : TableStyle) (edits : List (Change K V))
    (before after : K → Option V) (ready : applyChanges edits before = .ok after) :
    publishProjectionDelivery (.ok (next, inverseChanges edits) : Except K (S × List (Change K V)))
      style (some after) (fun root changes => applyChanges changes root) =
        ((match style with | .pure => some after | .mutable => some before | .linear => none),
          .ok (next, inverseChanges edits, before)) :=
  publishProjectionDelivery_ready next _ style after before _ (applyChanges_inverse edits before after ready)

/-- Unrelated rows in the public root are deliberately preserved by changed-key
rebasing; they need not appear in the canonical projection cache. -/
theorem publishProjectionDelivery_frame [DecidableEq K] [DecidableEq V]
    (changes : List (Change K V)) (before after : K → Option V)
    (ready : applyChanges changes before = .ok after) (query : K)
    (outside : ∀ change ∈ changes, query ≠ change.key) : after query = before query :=
  applyChanges_frame changes before after ready query outside

/-- The existing generation check also rejects a target winner installed DURING
an installer callback. It protects against ABA even when changed values match. -/
theorem projectionDelivery_stale_generation (style : TableStyle)
    (current : TableGeneration T) (expected : Nat) (after : T)
    (stale : current.version ≠ expected) :
    installStyle (E := E) style current expected after = (current, .error .stale) :=
  installStyle_stale style current expected after stale

/-- Typed lookup enrichment is key preserving on the left. Option distinguishes
an absent right row from a stored false or opaque Function payload. -/
def lookupJoinView (classify : K → V → I) (left : K → Option V)
    (right : I → Option R) (key : K) : Option (V × Option R) :=
  (left key).map fun row => (row, right (classify key row))

/-- Deleted left rows demand neither a lookup nor an output projection. -/
theorem lookupJoinView_absent (classify : K → V → I) (left : K → Option V)
    (right : I → Option R) (key : K) (absent : left key = none) :
    lookupJoinView classify left right key = none := by simp [lookupJoinView, absent]

/-- The original left payload and right presence are retained exactly. -/
theorem lookupJoinView_present (classify : K → V → I) (left : K → Option V)
    (right : I → Option R) (key : K) (row : V) (present : left key = some row) :
    lookupJoinView classify left right key = some (row, right (classify key row)) := by
  simp [lookupJoinView, present]

/-- Left edits and old/final buckets referencing right edits form a sound affected
inventory. Unlisted rows have unchanged left payloads and right observations. -/
theorem lookupJoin_frame (leftKeys : List K) (rightKeys : List I) (affected : List K)
    (classify : K → V → I) (lb la : K → Option V) (rb ra : I → Option R)
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (coversLeft : ∀ key ∈ leftKeys, key ∈ affected)
    (coversRight : ∀ key row, (lb key = some row ∨ la key = some row) →
      classify key row ∈ rightKeys → key ∈ affected)
    (key : K) (outside : key ∉ affected) :
    lookupJoinView classify lb rb key = lookupJoinView classify la ra key := by
  have same := leftFrame key (fun member => outside (coversLeft key member))
  cases found : lb key with
  | none => simp [lookupJoinView, ← same, found]
  | some row =>
    have unaffected : classify key row ∉ rightKeys :=
      fun member => outside (coversRight key row (Or.inl found) member)
    simp [lookupJoinView, ← same, found, rightFrame _ unaffected]

/-- Repair only the finite affected inventory, retaining all other enriched rows.
The coalesced registry is an implementation of logical key equality, not a scan. -/
theorem lookupJoin_repair [DecidableEq K] (leftKeys : List K) (rightKeys : List I)
    (affected : List K) (classify : K → V → I) (lb la : K → Option V) (rb ra : I → Option R)
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (coversLeft : ∀ key ∈ leftKeys, key ∈ affected)
    (coversRight : ∀ key row, (lb key = some row ∨ la key = some row) →
      classify key row ∈ rightKeys → key ∈ affected) :
    repairGroupFolds affected (lookupJoinView classify la ra) (lookupJoinView classify lb rb) =
      lookupJoinView classify la ra := by
  funext key
  by_cases member : key ∈ affected
  · simp [repairGroupFolds, member]
  · simpa [repairGroupFolds, member] using
      lookupJoin_frame leftKeys rightKeys affected classify lb la rb ra
        leftFrame rightFrame coversLeft coversRight key member

/-- The existing projection cache can refresh lookup-enriched rows without a new
output-claim or collision algorithm. Every final observation equals full projection. -/
theorem lookupJoin_refresh [DecidableEq K] (leftKeys : List K) (rightKeys : List I)
    (affected : List K) (classify : K → V → I) (lb la : K → Option V) (rb ra : I → Option R)
    (project : K → (V × Option R) → Except E (Option (L × W)))
    (cache result : K → Option (L × W))
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (coversLeft : ∀ key ∈ leftKeys, key ∈ affected)
    (coversRight : ∀ key row, (lb key = some row ∨ la key = some row) →
      classify key row ∈ rightKeys → key ∈ affected)
    (coherent : ∀ key, projectedEntry project (lookupJoinView classify lb rb) key = .ok (cache key))
    (ready : refreshEntryCache project (lookupJoinView classify la ra) affected cache = .ok result) :
    ∀ key, projectedEntry project (lookupJoinView classify la ra) key = .ok (result key) := by
  apply refreshEntryCache_complete project (lookupJoinView classify lb rb)
    (lookupJoinView classify la ra) affected cache result coherent _ ready
  exact lookupJoin_frame leftKeys rightKeys affected classify lb la rb ra
    leftFrame rightFrame coversLeft coversRight

/-- Explicit inverses of both checked source deltas restore the enriched view.
No inverse of a lossy lookup/projection or rollback of postcommit IO is inferred. -/
theorem lookupJoin_inverse [DecidableEq K] [DecidableEq I] [DecidableEq V] [DecidableEq R]
    (classify : K → V → I) (dl : List (Change K V)) (dr : List (Change I R))
    (lb la : K → Option V) (rb ra : I → Option R)
    (leftReady : applyChanges dl lb = .ok la) (rightReady : applyChanges dr rb = .ok ra) :
    (((applyChanges (inverseChanges dl) la).mapError (Sum.inl : K → Sum K I)).bind fun l =>
      ((applyChanges (inverseChanges dr) ra).mapError (Sum.inr : I → Sum K I)).map
        fun r => lookupJoinView classify l r) =
      .ok (lookupJoinView classify lb rb) := by
  rw [applyChanges_inverse dl lb la leftReady, applyChanges_inverse dr rb ra rightReady]
  rfl

/-- Source preparation is ordered: complete left installation/admission precedes
right installation/admission, and both precede classification/projection. -/
def prepareLookupSources (left : Except E L) (right : L → Except E R) : Except E (L × R) :=
  left.bind fun l => (right l).map (l, ·)

/-- A left refusal retains its cause and does not invoke the right preparation. -/
theorem prepareLookupSources_left_refused (cause : E) (right : L → Except E R) :
    prepareLookupSources (.error cause) right = .error cause := rfl

/-- Right refusal exposes no prepared source pair or projection successor. -/
theorem prepareLookupSources_right_refused (left : L) (right : L → Except E R) (cause : E)
    (refused : right left = .error cause) :
    prepareLookupSources (.ok left) right = .error cause := by
  simp [prepareLookupSources, refused, Except.bind, Except.map]

/-- Successful paired admission preserves the exact supplied source values. -/
theorem prepareLookupSources_ready (left : L) (right : L → Except E R) (next : R)
    (ready : right left = .ok next) :
    prepareLookupSources (.ok left) right = .ok (left, next) := by
  simp [prepareLookupSources, ready, Except.bind, Except.map]

/-- Explicit finite equijoin observations retain both admitted payloads. Group
comparison is supplied as a decidable logical equality, never inferred hashing. -/
def groupJoinView [DecidableEq G] (cl : K → V → G) (cr : I → R → G)
    (left : K → Option V) (right : I → Option R) (key : K × I) : Option (V × R) :=
  match left key.1, right key.2 with
  | some l, some r => if cl key.1 l = cr key.2 r then some (l, r) else none
  | _, _ => none

/-- Deleted endpoints and unequal groups contribute no pair or user projection. -/
theorem groupJoinView_missing [DecidableEq G] (cl : K → V → G) (cr : I → R → G)
    (left : K → Option V) (right : I → Option R) (key : K × I)
    (missing : left key.1 = none ∨ right key.2 = none) :
    groupJoinView cl cr left right key = none := by
  rcases missing with h | h
  · simp [groupJoinView, h]
  · cases left key.1 <;> simp [groupJoinView, h]

/-- A finite reference inventory includes edited endpoints only when their old
or final pair exists. The runtime obtains this set from old/final group buckets,
not by scanning a Cartesian product. Payload equality is deliberately unnecessary. -/
def groupJoinAffected [DecidableEq K] [DecidableEq I]
    (inventory : List (K × I)) (leftKeys : List K) (rightKeys : List I)
    (before after : K × I → Option (V × R)) : List (K × I) :=
  inventory.filter fun key => decide (key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys) &&
    ((before key).isSome || (after key).isSome)

/-- All live edited-endpoint pairs are covered under the finite bucket inventory
premise. Stored false and opaque Function values require no equality operation. -/
theorem groupJoinAffected_covers [DecidableEq K] [DecidableEq I]
    (inventory : List (K × I)) (leftKeys : List K) (rightKeys : List I)
    (before after : K × I → Option (V × R)) (key : K × I)
    (listed : key ∈ inventory) (edited : key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys)
    (live : (before key).isSome = true ∨ (after key).isSome = true) :
    key ∈ groupJoinAffected inventory leftKeys rightKeys before after := by
  simp only [groupJoinAffected, List.mem_filter]
  refine ⟨listed, ?_⟩
  rcases live with h | h <;> simp [edited, h]

/-- No filtering step creates pair identities; coalescing may further reduce
this finite bound. It does not bound whole-root recognition, allocation or GC. -/
theorem groupJoinAffected_bound [DecidableEq K] [DecidableEq I]
    (inventory : List (K × I)) (leftKeys : List K) (rightKeys : List I)
    (before after : K × I → Option (V × R)) :
    (groupJoinAffected inventory leftKeys rightKeys before after).length ≤ inventory.length :=
  List.length_filter_le _ _

/-- Outside old/final matching buckets, either both endpoints are unchanged or
both pair observations are absent. This is the selective invalidation invariant. -/
theorem groupJoin_frame [DecidableEq G] (cl : K → V → G) (cr : I → R → G)
    (lb la : K → Option V) (rb ra : I → Option R)
    (leftKeys : List K) (rightKeys : List I) (affected : List (K × I))
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (covers : ∀ key, (key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys) →
      (groupJoinView cl cr lb rb key ≠ none ∨ groupJoinView cl cr la ra key ≠ none) → key ∈ affected)
    (key : K × I) (outside : key ∉ affected) :
    groupJoinView cl cr lb rb key = groupJoinView cl cr la ra key := by
  by_cases edited : key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys
  · have h : ¬ (groupJoinView cl cr lb rb key ≠ none ∨ groupJoinView cl cr la ra key ≠ none) :=
      fun live => outside (covers key edited live)
    have old : groupJoinView cl cr lb rb key = none := by
      exact Classical.byContradiction (fun different => h (Or.inl different))
    have next : groupJoinView cl cr la ra key = none := by
      exact Classical.byContradiction (fun different => h (Or.inr different))
    rw [old, next]
  · have hl : key.1 ∉ leftKeys := fun h => edited (Or.inl h)
    have hr : key.2 ∉ rightKeys := fun h => edited (Or.inr h)
    simp only [groupJoinView, leftFrame key.1 hl, rightFrame key.2 hr]

/-- A complete finite old/final bucket inventory discharges the frame premise
of selective refresh. No completeness assumption about unrelated groups is used. -/
theorem groupJoinAffected_frame [DecidableEq K] [DecidableEq I] [DecidableEq G]
    (cl : K → V → G) (cr : I → R → G) (lb la : K → Option V) (rb ra : I → Option R)
    (leftKeys : List K) (rightKeys : List I) (inventory : List (K × I))
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (listed : ∀ key, (key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys) →
      (groupJoinView cl cr lb rb key ≠ none ∨ groupJoinView cl cr la ra key ≠ none) → key ∈ inventory)
    (key : K × I)
    (outside : key ∉ groupJoinAffected inventory leftKeys rightKeys
      (groupJoinView cl cr lb rb) (groupJoinView cl cr la ra)) :
    groupJoinView cl cr lb rb key = groupJoinView cl cr la ra key := by
  apply groupJoin_frame cl cr lb la rb ra leftKeys rightKeys _ leftFrame rightFrame _ key outside
  intro pair edited live
  apply groupJoinAffected_covers inventory leftKeys rightKeys _ _ pair (listed pair edited live) edited
  rcases live with h | h
  · cases eq : groupJoinView cl cr lb rb pair with
    | none => exact False.elim (h eq)
    | some value => exact Or.inl (by simp [eq])
  · cases eq : groupJoinView cl cr la ra pair with
    | none => exact False.elim (h eq)
    | some value => exact Or.inr (by simp [eq])

/-- The unchanged projection engine gives full recomputation equivalence after
selective pair repair. Its existing claim/delivery laws supply collision refusal,
exact target deltas, style installation and predecessor-preserving retry. -/
theorem groupJoin_refresh [DecidableEq K] [DecidableEq I] [DecidableEq G]
    (cl : K → V → G) (cr : I → R → G) (lb la : K → Option V) (rb ra : I → Option R)
    (leftKeys : List K) (rightKeys : List I) (affected : List (K × I))
    (project : (K × I) → (V × R) → Except E (Option (L × W)))
    (cache result : (K × I) → Option (L × W))
    (leftFrame : ∀ key, key ∉ leftKeys → lb key = la key)
    (rightFrame : ∀ key, key ∉ rightKeys → rb key = ra key)
    (covers : ∀ key, (key.1 ∈ leftKeys ∨ key.2 ∈ rightKeys) →
      (groupJoinView cl cr lb rb key ≠ none ∨ groupJoinView cl cr la ra key ≠ none) → key ∈ affected)
    (coherent : ∀ key, projectedEntry project (groupJoinView cl cr lb rb) key = .ok (cache key))
    (ready : refreshEntryCache project (groupJoinView cl cr la ra) affected cache = .ok result) :
    ∀ key, projectedEntry project (groupJoinView cl cr la ra) key = .ok (result key) := by
  apply refreshEntryCache_complete project (groupJoinView cl cr lb rb)
    (groupJoinView cl cr la ra) affected cache result coherent _ ready
  exact groupJoin_frame cl cr lb la rb ra leftKeys rightKeys affected leftFrame rightFrame covers

/-- Both source inverses recover every pair observation, without an inverse
classifier or an inverse output projection. Error-side keys remain distinguished. -/
theorem groupJoin_inverse [DecidableEq K] [DecidableEq I] [DecidableEq G]
    [DecidableEq V] [DecidableEq R] (cl : K → V → G) (cr : I → R → G)
    (dl : List (Change K V)) (dr : List (Change I R))
    (lb la : K → Option V) (rb ra : I → Option R)
    (hl : applyChanges dl lb = .ok la) (hr : applyChanges dr rb = .ok ra) :
    (((applyChanges (inverseChanges dl) la).mapError (Sum.inl : K → Sum K I)).bind fun l =>
      ((applyChanges (inverseChanges dr) ra).mapError (Sum.inr : I → Sum K I)).map
        fun r => groupJoinView cl cr l r) = .ok (groupJoinView cl cr lb rb) := by
  rw [applyChanges_inverse dl lb la hl, applyChanges_inverse dr rb ra hr]
  rfl

/-- Empty finite expansions carry no ownership; nonempty packets retain opaque
payloads exactly. Unit lets the existing generic entry-cache kernel do the work. -/
def expansionPacket (rows : List (L × W)) : Option (Unit × List (L × W)) :=
  if rows.isEmpty then none else some ((), rows)

/-- Generalize the existing optional projection at its single callback boundary.
Absent source rows still demand no callback; expansion refusal retains its cause. -/
def expansionProject (expand : K → V → Except E (List (L × W)))
    (key : K) (value : V) : Except E (Option (Unit × List (L × W))) :=
  (expand key value).map expansionPacket

/-- Reading an empty ownership packet yields no target bindings. -/
def expansionRows (packet : Option (Unit × List (L × W))) : List (L × W) :=
  (packet.map Prod.snd).getD []

/-- Packing never reconstructs or normalizes values, including Function leaves. -/
theorem expansionRows_packet (rows : List (L × W)) :
    expansionRows (expansionPacket rows) = rows := by
  cases rows <;> rfl

/-- The exact existing selective-cache theorem now covers every finite output
list. Coverage is supplied by installed source changes, not a global freshness
assumption. Recognition and callback purity remain explicit premises. -/
theorem expansion_refresh_complete [DecidableEq K]
    (expand : K → V → Except E (List (L × W))) (before after : K → Option V)
    (keys : List K) (cache result : K → Option (Unit × List (L × W)))
    (coherent : ∀ key, projectedEntry (expansionProject expand) before key = .ok (cache key))
    (covered : ∀ key, key ∉ keys → before key = after key)
    (ready : refreshEntryCache (expansionProject expand) after keys cache = .ok result) :
    ∀ key, projectedEntry (expansionProject expand) after key = .ok (result key) :=
  refreshEntryCache_complete _ before after keys cache result coherent covered ready

/-- Unselected source owners retain their entire finite output packet. This
includes output order and opaque payload identity, not only target membership. -/
theorem expansion_refresh_frame [DecidableEq K]
    (expand : K → V → Except E (List (L × W))) (after : K → Option V)
    (keys : List K) (cache result : K → Option (Unit × List (L × W)))
    (ready : refreshEntryCache (expansionProject expand) after keys cache = .ok result)
    (key : K) (outside : key ∉ keys) : expansionRows (result key) = expansionRows (cache key) := by
  rw [refreshEntryCache_frame _ after keys cache result ready key outside]

/-- With total pure expansion, selective cache refresh gives exactly the full
finite expansion at each source key, including absent and empty owners. -/
theorem expansion_refresh_rows [DecidableEq K]
    (expand : K → V → List (L × W)) (before after : K → Option V) (keys : List K)
    (cache result : K → Option (Unit × List (L × W)))
    (coherent : ∀ key, cache key = (before key).bind (fun value => expansionPacket (expand key value)))
    (covered : ∀ key, key ∉ keys → before key = after key)
    (ready : refreshEntryCache (expansionProject (fun key value => .ok (expand key value) :
      K → V → Except E (List (L × W)))) after keys cache = .ok result) (key : K) :
    expansionRows (result key) = ((after key).map (expand key)).getD [] := by
  have old : ∀ query, projectedEntry (expansionProject (fun k v => .ok (expand k v) :
      K → V → Except E (List (L × W)))) before query = .ok (cache query) := by
    intro query
    rw [coherent query]
    cases h : before query <;> simp [projectedEntry, expansionProject, h, Except.map]
  have complete := expansion_refresh_complete (fun k v => .ok (expand k v) :
    K → V → Except E (List (L × W))) before after keys cache result old covered ready key
  cases h : after key with
  | none =>
    simp [projectedEntry, h] at complete
    rw [← complete]
    rfl
  | some value =>
    simp [projectedEntry, expansionProject, h, Except.map] at complete
    rw [← complete]
    simpa [h] using expansionRows_packet (expand key value)

/-- Reserve an already admitted finite expansion with the same collision kernel
as ordinary projection. Every duplicate refuses, even within a single owner. -/
def reserveExpansion [DecidableEq L] (rows : List (L × W)) (seen : List L) :
    Except (E ⊕ L) (List (L × W)) :=
  mapEntries (fun key value => .ok (some (key, value))) rows seen

/-- Successful reservation preserves every entry in order, without value equality. -/
theorem reserveExpansion_preserves [DecidableEq L] (rows : List (L × W))
    (seen : List L) (output : List (L × W))
    (ready : reserveExpansion (E := E) rows seen = .ok output) : output = rows := by
  induction rows generalizing seen output with
  | nil => simpa [reserveExpansion, mapEntries] using ready.symm
  | cons row rest ih =>
    rcases row with ⟨key, value⟩
    by_cases duplicate : key ∈ seen
    · simp [reserveExpansion, mapEntries, duplicate] at ready
    · cases hr : reserveExpansion (E := E) rest (key :: seen) with
      | error cause =>
        unfold reserveExpansion at hr
        simp [reserveExpansion, mapEntries, duplicate, hr, Except.map] at ready
      | ok tail =>
        have same := ih (key :: seen) tail hr
        unfold reserveExpansion at hr
        simpa [reserveExpansion, mapEntries, duplicate, hr, Except.map, same] using ready.symm

/-- Internal and cross-owner duplicates cannot survive successful reservation. -/
theorem reserveExpansion_unique [DecidableEq L] (rows : List (L × W))
    (seen : List L) (output : List (L × W))
    (ready : reserveExpansion (E := E) rows seen = .ok output) :
    (output.map Prod.fst).Nodup := mapEntries_nodup _ rows seen output ready

/-- Untouched owners cannot be overwritten, even by an equal payload. -/
theorem reserveExpansion_avoids [DecidableEq L] (rows : List (L × W))
    (seen : List L) (output : List (L × W))
    (ready : reserveExpansion (E := E) rows seen = .ok output) (key : L)
    (present : key ∈ output.map Prod.fst) : key ∉ seen :=
  mapEntries_avoids _ rows seen output ready key present

/-- A repeated logical key refuses at that entry before later reservations. -/
theorem reserveExpansion_collision [DecidableEq L] (row : L × W)
    (rest : List (L × W)) (seen : List L) (duplicate : row.1 ∈ seen) :
    reserveExpansion (E := E) (row :: rest) seen = .error (.inr row.1) := by
  exact mapEntries_collision _ row.1 row.2 rest seen row rfl duplicate

/-- Installed source inverses recover every full finite expansion. Output
projection need not be invertible: the original source delta carries recovery. -/
theorem expansion_inverse [DecidableEq K] [DecidableEq V]
    (expand : K → V → Except E (List (L × W))) (edits : List (Change K V))
    (before after : K → Option V) (installed : applyChanges edits before = .ok after) :
    (applyChanges (inverseChanges edits) after).map
      (fun source => projectedEntry (expansionProject expand) source) =
      .ok (projectedEntry (expansionProject expand) before) := by
  rw [applyChanges_inverse edits before after installed]
  rfl

end LeanPoo.Functional.OrderedDictionary
