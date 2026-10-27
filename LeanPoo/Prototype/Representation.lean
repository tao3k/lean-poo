import LeanPoo.Object.CacheInvalidation

/-! Persistent ordered specifications and guarded receiver-local vector layouts.
This models source semantics, not the standard RBTree implementation, weak-table
collector, Scheme compiler or pointer layout. A runtime layout token denotes one
immutable shape and one receiver's cells; supported edits discard that token.
Registered finite dependency edges and serialized edits remain prerequisites. -/
namespace LeanPoo.Prototype.Representation

/-- Ordered contributions can repeat a name; replacing the first preserves later methods. -/
def putFirst (entries : List (String × Value)) (name : String) (value : Value) : List (String × Value) :=
  match entries with
  | [] => [(name,value)]
  | (key,old) :: tail => if key = name then (key,value) :: tail else (key,old) :: putFirst tail name value

/-- Direct removal erases all local contributions; inheritance is resolved separately. -/
def erase (entries : List (String × Value)) (name : String) := entries.filter (fun entry => entry.1 != name)

/-- Observe the first contribution while retaining the complete ordered method chain. -/
def first (entries : List (String × Value)) (name : String) : Option Value :=
  match entries with
  | [] => none
  | (key,value) :: tail => if key = name then some value else first tail name

/-- Persistent writes replace the intended contribution, including previously absent keys. -/
theorem first_put (entries : List (String × Value)) (name : String) (value : Value) :
    first (putFirst entries name value) name = some value := by
  induction entries with
  | nil => simp [putFirst,first]
  | cons entry tail ih => rcases entry with ⟨key,old⟩; by_cases h : key = name <;> simp [putFirst,first,h,ih]

/-- An unrelated field is unchanged by a persistent write. -/
theorem first_put_frame (entries : List (String × Value)) (name other : String) (value : Value)
    (different : other ≠ name) : first (putFirst entries name value) other = first entries other := by
  induction entries with
  | nil => simp [putFirst,first,Ne.symm different]
  | cons entry tail ih =>
    rcases entry with ⟨key,old⟩
    by_cases h : key = name
    · subst key; simp [putFirst,first,Ne.symm different]
    · simp [putFirst,first,h,ih]

/-- Removing a local name leaves no forgotten same-name contribution. -/
theorem first_erase (entries : List (String × Value)) (name : String) : first (erase entries name) name = none := by
  induction entries with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key,value⟩
    by_cases h : key = name <;> simp [erase,first,h] at * <;> assumption

/-- A source-level storage refinement. Tree contents denote the standard library's
ordered contribution observation; this does not model balancing or physical cells. -/
inductive Storage (Value : Type) where
  | small (entries : List (String × Value))
  | tree (entries : List (String × Value)) (compact : Bool)
  deriving DecidableEq

/-- Both physical choices must expose precisely the same ordered contributions. -/
def Storage.entries : Storage Value → List (String × Value)
  | .small entries => entries
  | .tree entries _ => entries

/-- Count contributions, including duplicates, rather than only unique field names. -/
def pack (entries : List (String × Value)) : Storage Value :=
  if entries.length ≤ 8 then .small entries else .tree entries true

/-- Promotion/demotion retain the entire ordered method chain, without evaluation. -/
@[simp] theorem entries_pack (entries : List (String × Value)) : (pack entries).entries = entries := by
  simp only [pack]; split <;> rfl

/-- Exactly the compact branch has the declared bounded contribution count. -/
theorem pack_small_iff (entries : List (String × Value)) :
    pack entries = .small entries ↔ entries.length ≤ 8 := by
  simp only [pack]; split <;> simp_all

/-- The explicit policy survives promotion; tree-only mode never enables small maps. -/
def Storage.compact : Storage Value → Bool
  | .small _ => true
  | .tree _ compact => compact

/-- New snapshots default to the standard tree policy; compact storage is explicit. -/
def packWith (compact : Bool) (entries : List (String × Value)) : Storage Value :=
  if compact then pack entries else .tree entries false

/-- Policy selection changes storage, never the ordered contribution observation. -/
@[simp] theorem entries_packWith (compact : Bool) (entries : List (String × Value)) :
    (packWith compact entries).entries = entries := by
  cases compact with
  | false => rfl
  | true => exact entries_pack entries

/-- Representation conversion retains the caller-selected strategy, including large maps. -/
@[simp] theorem compact_packWith (compact : Bool) (entries : List (String × Value)) :
    (packWith compact entries).compact = compact := by
  cases compact <;> by_cases small : entries.length ≤ 8 <;>
    simp [packWith, pack, small, Storage.compact]

/-- Persistent writes use the existing first-contribution operation before repacking. -/
def Storage.put (source : Storage Value) (name : String) (value : Value) : Storage Value :=
  packWith source.compact (putFirst source.entries name value)

/-- Persistent removal uses the existing all-contribution erasure before repacking. -/
def Storage.remove (source : Storage Value) (name : String) : Storage Value :=
  packWith source.compact (erase source.entries name)

/-- Either representation preserves all untouched and later same-name contributions. -/
@[simp] theorem entries_put (source : Storage Value) (name : String) (value : Value) :
    (source.put name value).entries = putFirst source.entries name value := by
  simp [Storage.put]

/-- Demotion cannot retain a forgotten direct method or change surviving order. -/
@[simp] theorem entries_remove (source : Storage Value) (name : String) :
    (source.remove name).entries = erase source.entries name := by
  simp [Storage.remove]

/-- Writes cannot silently enable a rejected automatic policy. -/
@[simp] theorem put_policy (source : Storage Value) (name : String) (value : Value) :
    (source.put name value).compact = source.compact := by simp [Storage.put]

/-- Removal/demotion retains the chosen policy for future revisions. -/
@[simp] theorem remove_policy (source : Storage Value) (name : String) :
    (source.remove name).compact = source.compact := by simp [Storage.remove]

/-- The default tree policy remains a tree even for small or empty revised rows. -/
theorem default_put_tree (entries : List (String × Value)) (name : String) (value : Value) :
    (Storage.tree entries false).put name value = .tree (putFirst entries name value) false := by rfl

/-- The existing first-write law applies across both representation transitions. -/
theorem storage_first_put (source : Storage Value) (name : String) (value : Value) :
    first (source.put name value).entries name = some value := by
  simpa using first_put source.entries name value

/-- A persistent revision cannot change an unrelated field's first contribution. -/
theorem storage_put_frame (source : Storage Value) (name other : String) (value : Value)
    (different : other ≠ name) :
    first (source.put name value).entries other = first source.entries other := by
  simpa using first_put_frame source.entries name other value different

/-- Count actual identity tests in the compact first-name search, including misses. -/
def searchWork (entries : List (String × Value)) (name : String) : Nat :=
  match entries with
  | [] => 0
  | (key, _) :: tail => if key = name then 1 else 1 + searchWork tail name

/-- Compact search never examines more contributions than the stored vector holds. -/
theorem searchWork_le (entries : List (String × Value)) (name : String) :
    searchWork entries name ≤ entries.length := by
  induction entries with
  | nil => simp [searchWork]
  | cons entry tail ih =>
    rcases entry with ⟨key, value⟩
    simp only [searchWork, List.length_cons]
    split <;> omega

/-- A selected compact representation has at most eight identity tests per lookup.
This counts source operations only, not allocator, GC, compiler or wall time. -/
theorem compact_search_bound (entries : List (String × Value)) (name : String)
    (compact : pack entries = .small entries) : searchWork entries name ≤ 8 := by
  exact Nat.le_trans (searchWork_le entries name) ((pack_small_iff entries).mp compact)

/-- First replacement preserves length; a new contribution increases it by one. -/
theorem putFirst_length_le (entries : List (String × Value)) (name : String) (value : Value) :
    (putFirst entries name value).length ≤ entries.length + 1 := by
  induction entries with
  | nil => simp [putFirst]
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    simp only [putFirst, List.length_cons]
    split <;> simp_all only [List.length_cons] <;> omega

/-- Compact writes copy at most nine vector cells, including the promotion row.
Tree construction after promotion has a separate standard-library cost. -/
theorem compact_copy_bound (entries : List (String × Value)) (name : String) (value : Value)
    (compact : pack entries = .small entries) : (putFirst entries name value).length ≤ 9 := by
  have size := (pack_small_iff entries).mp compact
  have written := putFirst_length_le entries name value
  omega

/-- Whole finite revision traces use one semantic operation family in both stores. -/
inductive Edit (Value : Type) where
  | put (name : String) (value : Value)
  | remove (name : String)

/-- One standard semantic revision step on the ordered contribution list. -/
def editEntries (entries : List (String × Value)) : Edit Value → List (String × Value)
  | .put name value => putFirst entries name value
  | .remove name => erase entries name

/-- One revision step through the concrete representation selector. -/
def editStorage (source : Storage Value) : Edit Value → Storage Value
  | .put name value => source.put name value
  | .remove name => source.remove name

/-- Arbitrarily many promotions/demotions preserve the full ordered specification. -/
theorem revision_trace (edits : List (Edit Value)) (source : Storage Value) :
    (edits.foldl editStorage source).entries = edits.foldl editEntries source.entries := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases edit <;> simp [editStorage, editEntries]

/-- A complete finite revision trace preserves the explicitly selected strategy. -/
theorem revision_trace_policy (edits : List (Edit Value)) (source : Storage Value) :
    (edits.foldl editStorage source).compact = source.compact := by
  induction edits generalizing source with
  | nil => rfl
  | cons edit tail ih =>
    simp only [List.foldl_cons]
    rw [ih]
    cases edit <;> simp [editStorage]

/-- A layout has one receiver identity, monotone revision and allocation token.
Shapes may be shared, while the field interpretation belongs to this receiver. -/
structure View (Value : Type) where
  owner : Nat
  revision : Nat
  token : Nat
  names : List String
  fields : String → Option Value

/-- Materialize the receiver's lazy/cached interpretation at its shape index.
An absent cell remains distinct from a present false Boolean. -/
def cell (view : View Value) (index : Nat) : Option Value := view.names[index]?.bind view.fields

/-- An access site retains a certified shape index, never a retained result value. -/
structure Site where
  owner : Nat
  revision : Nat
  token : Nat
  names : List String
  name : String
  index : Nat
  indexed : names[index]? = some name

/-- Runtime identity guards mean the same receiver, revision and immutable layout.
Structural shape equality states the semantic obligation of token/pointer identity. -/
abbrev valid (site : Site) (view : View Value) : Prop :=
  site.owner = view.owner ∧ site.revision = view.revision ∧ site.token = view.token ∧ site.names = view.names

/-- A failed guard publishes no cached value; ordinary lookup performs the miss. -/
def read (site : Site) (view : View Value) : Option Value :=
  if valid site view then cell view site.index else none

/-- Every accepted index observes this receiver's current field, not a different owner. -/
theorem read_sound (site : Site) (view : View Value) (current : valid site view) :
    read site view = view.fields site.name := by
  have indexed : view.names[site.index]? = some site.name := current.2.2.2 ▸ site.indexed
  simp [read,current,cell,indexed]

/-- Shape sharing alone never authorizes the old receiver value guard. -/
theorem reject_owner (site : Site) (view : View Value) (different : site.owner ≠ view.owner) :
    read site view = none := by simp [read,valid,different]

/-- An old reference is rejected even if a revision restores the same values/shape. -/
theorem reject_revision (site : Site) (view : View Value) (different : site.revision ≠ view.revision) :
    read site view = none := by simp [read,valid,different]

/-- Replacing a layout rejects the old value guard, even for equal field sets.
The separate shape-offset path must read the new receiver-local cells. -/
theorem reject_layout (site : Site) (view : View Value) (different : site.token ≠ view.token) :
    read site view = none := by simp [read,valid,different]

/-- Reuse the existing graph theorem: a shared descendant advances exactly once.
This connects the index guard to supported parent/hook/descriptor invalidation. -/
theorem descendant_revision_rejected (graph : C4.Graph) (changed : List String)
    (cache : String → Object.RevisionCache Value) (name : String)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    (cache name).revision ≠ (Object.invalidateCaches graph changed cache name).revision := by
  rw [Object.invalidateCaches_once graph changed cache name affected]
  omega

/-- Present false is a valid vector result and cannot be confused with absence. -/
theorem false_cell (view : View Bool) (index : Nat) (name : String)
    (indexed : view.names[index]? = some name) (present : view.fields name = some false) :
    cell view index = some false := by simp [cell,indexed,present]

/-- Equal immutable shapes certify an offset across receivers, never an old
receiver's value. Runtime pointer equality must imply this shape equality. -/
def reuseIndex (site : Site) (view : View Value) : Option Nat :=
  if site.names = view.names then some site.index else none

/-- A reused offset always denotes the requested name in the CURRENT layout. -/
theorem reuseIndex_sound (site : Site) (view : View Value)
    (same : site.names = view.names) : view.names[site.index]? = some site.name :=
  same ▸ site.indexed

/-- The switched-owner ready-cell path reads this view; an unknown shape or
uncomputed cell uses the existing lazy fallback. No Value equality is required. -/
def readPrepared (site : Site) (view : View Value) (fallback : Unit → Except E Value) : Except E Value :=
  match (reuseIndex site view).bind (cell view) with
  | some value => .ok value
  | none => fallback ()

/-- Owner/revision/token can differ: only the current view supplies the value. -/
theorem readPrepared_current (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (value : Value) (same : site.names = view.names) (ready : view.fields site.name = some value) :
    readPrepared site view fallback = .ok value := by
  have indexed := reuseIndex_sound site view same
  simp [readPrepared, reuseIndex, same, cell, indexed, ready]

/-- A known offset does not force an uncomputed body until its ordinary fallback. -/
theorem readPrepared_lazy (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (same : site.names = view.names) (uncomputed : view.fields site.name = none) :
    readPrepared site view fallback = fallback () := by
  have indexed := reuseIndex_sound site view same
  simp [readPrepared, reuseIndex, same, cell, indexed, uncomputed]

/-- A different shape grants no reusable offset or cached value authority. -/
theorem readPrepared_reshaped (site : Site) (view : View Value) (fallback : Unit → Except E Value)
    (different : site.names ≠ view.names) : readPrepared site view fallback = fallback () := by
  simp [readPrepared, reuseIndex, different]

/-- Lazy refusal retains its exact cause; the caller cannot bind a successful value. -/
theorem readPrepared_refused (site : Site) (view : View Value) (cause : E)
    (same : site.names = view.names) (uncomputed : view.fields site.name = none) :
    readPrepared site view (fun _ => .error cause) = .error cause :=
  readPrepared_lazy site view _ same uncomputed

/-- Stored false is ready data, not an uncomputed cell or a request to retry. -/
theorem readPrepared_false (site : Site) (view : View Bool) (fallback : Unit → Except E Bool)
    (same : site.names = view.names) (ready : view.fields site.name = some false) :
    readPrepared site view fallback = .ok false :=
  readPrepared_current site view fallback false same ready

/-- Count only name-to-index hash resolutions in the switched-site path. Shape
checks, value reads, guards, initialization, callback/evaluator and GC costs are
separate; faithful constant-time shape identity is a runtime premise. -/
def resolutionWork (site : Site) (view : View Value) : Nat :=
  if site.names = view.names then 0 else 1

/-- A matching shape removes the name-map resolution, not all access costs. -/
theorem resolutionWork_shared (site : Site) (view : View Value) (same : site.names = view.names) :
    resolutionWork site view = 0 := by simp [resolutionWork, same]

/-- Shape mismatch retains one ordinary resolution rather than inventing an offset. -/
theorem resolutionWork_changed (site : Site) (view : View Value) (different : site.names ≠ view.names) :
    resolutionWork site view = 1 := by simp [resolutionWork, different]

/-- Observation selects the existing ordinary read protocol before any lazy
layout preparation. Both branches remain thunks; no alternate evaluator or
observation-record engine is introduced by the access policy. -/
def selectRead (observed : Bool) (ordinary optimized : Unit → Except E Value) : Except E Value :=
  if observed then ordinary () else optimized ()

/-- Tracked reads bypass all optimized preparation and retain ordinary behavior. -/
theorem selectRead_observed (ordinary optimized : Unit → Except E Value) :
    selectRead true ordinary optimized = ordinary () := rfl

/-- Disabled observation retains the existing explicit layout/cell protocol. -/
theorem selectRead_unobserved (ordinary optimized : Unit → Except E Value) :
    selectRead false ordinary optimized = optimized () := rfl

/-- Ordinary precheck or evaluator refusal is not replaced by cached data. -/
theorem selectRead_refused (optimized : Unit → Except E Value) (cause : E) :
    selectRead true (fun _ => .error cause) optimized = .error cause := rfl

/-- Select the existing reader before cold layout construction for a pinned
bootstrap hook. A live prepared layout is reused; invalidation must clear it
with the instance. The three actions model effects/refusals without running
unchosen branches or assuming that preparation terminates. -/
def selectLayoutRead (observed prepared anchored : Bool)
    (ordinary ready prepare : Unit → Except E Value) : Except E Value :=
  if observed || (!prepared && anchored) then ordinary ()
  else if prepared then ready () else prepare ()

/-- Observers retain ordinary demand checks regardless of an available layout. -/
theorem selectLayoutRead_observed (prepared anchored : Bool)
    (ordinary ready prepare : Unit → Except E Value) :
    selectLayoutRead true prepared anchored ordinary ready prepare = ordinary () := by
  simp [selectLayoutRead]

/-- Cold pinned hooks cannot force unrelated metadata or layout preparation. -/
theorem selectLayoutRead_anchor (ordinary ready prepare : Unit → Except E Value) :
    selectLayoutRead false false true ordinary ready prepare = ordinary () := rfl

/-- A supported live layout removes redundant instance preparation, not value guards. -/
theorem selectLayoutRead_ready (anchored : Bool)
    (ordinary ready prepare : Unit → Except E Value) :
    selectLayoutRead false true anchored ordinary ready prepare = ready () := by
  simp [selectLayoutRead]

/-- Ordinary cold fields still run the guarded preparation protocol. -/
theorem selectLayoutRead_cold (ordinary ready prepare : Unit → Except E Value) :
    selectLayoutRead false false false ordinary ready prepare = prepare () := rfl

/-- A failed cold preparation remains the exact refusal, rather than a cached value. -/
theorem selectLayoutRead_refused (ordinary ready : Unit → Except E Value) (cause : E) :
    selectLayoutRead false false false ordinary ready (fun _ => .error cause) = .error cause := rfl

/-- Without observation or an available layout, hook identity is the only bypass.
This does not allow arbitrary cyclic fields to escape guarded construction. -/
theorem selectLayoutRead_cold_cases (anchored : Bool)
    (ordinary ready prepare : Unit → Except E Value) :
    selectLayoutRead false false anchored ordinary ready prepare =
      (if anchored then ordinary () else prepare ()) := by
  cases anchored <;> rfl

/-- An explicit consumer policy; symbolic demand never requests a layout.
Prepared demand reuses the existing current-cell/fallback protocol. -/
def demandRead (indexed : Bool) (site : Site) (view : View Value)
    (ordinary : Unit → Except E Value) : Except E Value :=
  if indexed then readPrepared site view ordinary else ordinary ()

/-- A ready cell agrees with the current ordinary evaluator. This is an
invalidation/fidelity premise, never evidence inferred from module caching. -/
abbrev faithful (site : Site) (view : View Value) (ordinary : Unit → Except E Value) : Prop :=
  ∀ value, view.fields site.name = some value → ordinary () = .ok value

/-- A faithful current layout and symbolic demand have the same value/refusal.
The shape can change: mismatch and uncomputed cells retain ordinary fallback. -/
theorem demandRead_sound (indexed : Bool) (site : Site) (view : View Value)
    (ordinary : Unit → Except E Value) (current : faithful site view ordinary) :
    demandRead indexed site view ordinary = ordinary () := by
  cases indexed with
  | false => rfl
  | true =>
    change readPrepared site view ordinary = ordinary ()
    by_cases same : site.names = view.names
    · cases ready : view.fields site.name with
      | none => exact readPrepared_lazy site view ordinary same ready
      | some value => rw [readPrepared_current site view ordinary value same ready, current value ready]
    · exact readPrepared_reshaped site view ordinary same

/-- One complete finite consumer batch stops at the first ordinary refusal.
Callbacks and module linking are outside this source-level result model. -/
def demandBatch (indexed : Bool) (site : Site) (views : List (View Value))
    (ordinary : View Value → Except E Value) : Except E (List Value) :=
  match views with
  | [] => .ok []
  | view :: rest => do
    let value ← demandRead indexed site view (fun _ => ordinary view)
    let tail ← demandBatch indexed site rest ordinary
    pure (value :: tail)

/-- Explicit access selection preserves a whole batch, including empty and
refused prefixes, when every accepted view has current evaluation evidence. -/
theorem demandBatch_sound (indexed : Bool) (site : Site) (views : List (View Value))
    (ordinary : View Value → Except E Value)
    (current : ∀ view ∈ views, faithful site view (fun _ => ordinary view)) :
    demandBatch indexed site views ordinary = demandBatch false site views ordinary := by
  induction views with
  | nil => rfl
  | cons view rest ih =>
    simp only [demandBatch]
    rw [demandRead_sound indexed site view _ (current view (by simp)),
        ih (fun item member => current item (by simp [member]))]
    rfl

/-- A symbolic-only deployment cannot demand an otherwise refused layout. -/
theorem demandRead_symbolic (site : Site) (view : View Value) (ordinary : Unit → Except E Value) :
    demandRead false site view ordinary = ordinary () := rfl

/-- No receiver evaluation or preparation is demanded by an empty finite batch. -/
theorem demandBatch_empty (indexed : Bool) (site : Site) (ordinary : View Value → Except E Value) :
    demandBatch indexed site [] ordinary = .ok [] := rfl

/-- A shape can allocate empty memo cells without visiting the ordinary value
cache. Names, owner and generation remain unchanged; ordinary lookup still owns
values/evaluation. Empty here means unpromoted, not field absence. -/
def deferCells (view : View Value) : View Value :=
  { view with fields := fun _ => none }

/-- Every deferred access uses its ordinary value/refusal, even for an unknown
shape. Deferred preparation does not turn a cached false into field absence. -/
theorem readPrepared_deferred (site : Site) (view : View Value) (ordinary : Unit → Except E Value) :
    readPrepared site (deferCells view) ordinary = ordinary () := by
  by_cases same : site.names = view.names
  · exact readPrepared_lazy site (deferCells view) ordinary same rfl
  · exact readPrepared_reshaped site (deferCells view) ordinary same

/-- Promote one already successful ordinary read. Runtime canonical shapes have
unique names: the name update denotes its certified single vector position.
This operation models promotion only, not effects inside ordinary evaluation. -/
def rememberCell (view : View Value) (name : String) (value : Value) : View Value :=
  { view with fields := fun key => if key = name then some value else view.fields key }

/-- Promotion grants no new shape or generation authority to an access site. -/
theorem rememberCell_identity (view : View Value) (name : String) (value : Value) :
    (rememberCell view name value).owner = view.owner ∧
    (rememberCell view name value).revision = view.revision ∧
    (rememberCell view name value).token = view.token ∧
    (rememberCell view name value).names = view.names := by exact ⟨rfl, rfl, rfl, rfl⟩

/-- Only the promoted memo field changes. Evaluation may independently populate
other dependency cells; this frame law does not constrain that evaluator. -/
theorem rememberCell_frame (view : View Value) (name other : String) (value : Value)
    (different : other ≠ name) :
    (rememberCell view name value).fields other = view.fields other := by
  simp [rememberCell, different]

/-- Successful ordinary false/Function values become direct current-cell hits.
No equality or revalidation of Value is needed, and the old owner is irrelevant. -/
theorem readPrepared_remembered (site : Site) (view : View Value) (ordinary : Unit → Except E Value)
    (value : Value) (same : site.names = view.names) :
    readPrepared site (rememberCell view site.name value) ordinary = .ok value := by
  apply readPrepared_current site (rememberCell view site.name value) ordinary value same
  simp [rememberCell]

/-- All present memo cells must agree with the CURRENT ordinary value cache. -/
abbrev faithfulCells (view : View Value) (ordinary : String → Except E Value) : Prop :=
  ∀ name value, view.fields name = some value → ordinary name = .ok value

/-- Empty memo cells require no source-value scan or successful source evidence. -/
theorem faithfulCells_deferred (view : View Value) (ordinary : String → Except E Value) :
    faithfulCells (deferCells view) ordinary := by
  intro name value cached
  simp [deferCells] at cached

/-- A successful named read preserves whole-cache fidelity when promoted.
Supported invalidation must discard this view when the ordinary source changes. -/
theorem faithfulCells_remembered (view : View Value) (ordinary : String → Except E Value)
    (name : String) (value : Value) (current : faithfulCells view ordinary)
    (successful : ordinary name = .ok value) :
    faithfulCells (rememberCell view name value) ordinary := by
  intro key found cached
  by_cases same : key = name
  · subst key
    simp [rememberCell] at cached
    rw [← cached]
    exact successful
  · exact current key found (by simpa [rememberCell, same] using cached)

/-- A whole finite batch over fresh deferred layouts retains ordinary failures
and demand order, without assuming all source values were materialized. -/
theorem demandBatch_deferred (site : Site) (views : List (View Value))
    (ordinary : View Value → Except E Value) :
    demandBatch true site (views.map deferCells) ordinary =
      demandBatch false site (views.map deferCells) ordinary := by
  apply demandBatch_sound
  intro view member value cached
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  simp [deferCells] at cached

/-- Only VALUE-cache seeding lookups are charged here. Canonical shape sorting,
key inventory, vector allocation/fill, demand reads and GC remain separate work. -/
def seedingLookups (eager : Bool) (canonicalNames : List String) : Nat :=
  if eager then canonicalNames.length else 0

/-- Demand-filled layout preparation performs zero ordinary value-table probes. -/
theorem seedingLookups_deferred (names : List String) : seedingLookups false names = 0 := rfl

/-- The eager source path probes once per canonical field, including uncached ones. -/
theorem seedingLookups_eager (names : List String) : seedingLookups true names = names.length := rfl

/-- The runtime first deduplicates by symbol identity, then compares cardinality
and every membership. String equality denotes faithful symbol identity here. -/
def shapeMatches (catalog hint : List String) : Bool :=
  catalog.length == hint.length && catalog.all (fun name => hint.contains name)

/-- Full membership and cardinality checking cannot retain an extra old field.
Deduplication is essential: equal lengths alone do not justify this conclusion. -/
theorem shapeMatches_members (catalog hint : List String) (unique : catalog.Nodup)
    (matched : shapeMatches catalog hint = true) :
    ∀ name, name ∈ hint ↔ name ∈ catalog := by
  have checked := Bool.and_eq_true_iff.mp matched
  have size : catalog.length = hint.length := by simpa using checked.1
  have forward : catalog ⊆ hint := by
    intro name member
    have := List.all_eq_true.mp checked.2 name member
    simpa using this
  intro name
  constructor
  · intro member
    by_cases absent : name ∈ catalog
    · exact absent
    apply False.elim
    have distinct : (name :: catalog).Nodup := List.nodup_cons.mpr ⟨absent, unique⟩
    have subset : name :: catalog ⊆ hint := by
      intro key belongs
      rcases List.mem_cons.mp belongs with rfl | tail
      · exact member
      · exact forward tail
    have bound := distinct.length_le_of_subset subset
    simp only [List.length_cons] at bound
    omega
  · exact fun member => forward member

/-- Reuse only the immutable ordered name vector; fallback canonicalization has
its own faithful ordering premise. The current receiver supplies ALL cell values. -/
def prepareFromHint (current : View Value) (hint : List String) : View Value :=
  { current with names := if shapeMatches current.names hint then hint else current.names }

/-- Choosing a certified old order changes no field presence, including removals. -/
theorem prepareFromHint_members (current : View Value) (hint : List String)
    (unique : current.names.Nodup) (name : String) :
    name ∈ (prepareFromHint current hint).names ↔ name ∈ current.names := by
  simp only [prepareFromHint]
  split
  · next h => exact shapeMatches_members _ _ unique h name
  · rfl

/-- Immutable shape sharing grants no old owner, revision, allocation or values. -/
theorem prepareFromHint_identity (current : View Value) (hint : List String) :
    (prepareFromHint current hint).owner = current.owner ∧
    (prepareFromHint current hint).revision = current.revision ∧
    (prepareFromHint current hint).token = current.token ∧
    (prepareFromHint current hint).fields = current.fields := by exact ⟨rfl, rfl, rfl, rfl⟩

/-- Any accepted old index must name a CURRENT field. No cached offset can
resurrect a removed name after a failed complete-set match. -/
theorem prepareFromHint_index (current : View Value) (hint : List String)
    (unique : current.names.Nodup) (index : Nat) (name : String)
    (indexed : (prepareFromHint current hint).names[index]? = some name) :
    name ∈ current.names := by
  apply (prepareFromHint_members current hint unique name).mp
  exact List.mem_of_getElem? indexed

/-- Whole-cache fidelity survives shape reuse without copying any old cells. -/
theorem faithfulCells_prepareFromHint (current : View Value) (hint : List String)
    (ordinary : String → Except E Value) (faithful : faithfulCells current ordinary) :
    faithfulCells (prepareFromHint current hint) ordinary := faithful

/-- Exact values/refusals still come from the current ordinary evaluator.
This composes the existing access law rather than adding another evaluator. -/
theorem demandRead_prepareFromHint (current : View Value) (hint : List String)
    (site : Site) (ordinary : Unit → Except E Value)
    (faithful : ∀ value, current.fields site.name = some value → ordinary () = .ok value) :
    demandRead true site (prepareFromHint current hint) ordinary = ordinary () := by
  exact demandRead_sound true site _ ordinary faithful

/-- Count canonical-sort entries only; name capture, deduplication, membership
probes, vector allocation/seeding, construction and GC are separate costs. -/
def shapeSorts (catalog hint : List String) : Nat := if shapeMatches catalog hint then 0 else 1

/-- A complete-set match skips sorting/interning even when input order differs. -/
theorem shapeSorts_hit (catalog hint : List String) (matched : shapeMatches catalog hint = true) :
    shapeSorts catalog hint = 0 := by simp [shapeSorts, matched]

/-- A changed catalog retains the original canonicalization path. -/
theorem shapeSorts_miss (catalog hint : List String) (matched : shapeMatches catalog hint = false) :
    shapeSorts catalog hint = 1 := by simp [shapeSorts, matched]

end LeanPoo.Prototype.Representation
