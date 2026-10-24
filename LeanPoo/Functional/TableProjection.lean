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

end LeanPoo.Functional.OrderedDictionary
