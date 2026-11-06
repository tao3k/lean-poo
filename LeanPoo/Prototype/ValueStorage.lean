import LeanPoo.Prototype.Representation
import Init.Data.List.Count

/-! One authoritative receiver-local value store behind symbolic and indexed reads.
Shape/index fidelity, serialized supported mutation and faithful host interpretation
remain premises. Metadata tables and issued-read provenance are not value caches;
these laws certify neither a compiler nor physical allocation/GC/wall-clock cost. -/
namespace LeanPoo.Prototype.Representation

variable {Value Error : Type}

/-- Ordinary lookup consults the same primary cells as the indexed reader.
An uncomputed cell alone calls the original evaluator; errors are not memo values. -/
def primaryRead (view : View Value) (name : String) (evaluate : Unit → Except Error Value) : Except Error Value :=
  match view.fields name with
  | some value => .ok value
  | none => evaluate ()

/-- A present value, including false or a function, needs no evaluator call. -/
theorem primaryRead_present (view : View Value) (name : String) (value : Value)
    (evaluate : Unit → Except Error Value) (present : view.fields name = some value) :
    primaryRead view name evaluate = .ok value := by simp [primaryRead, present]

/-- Absence is demand, not a successful false value or a cached failure. -/
theorem primaryRead_uncomputed (view : View Value) (name : String)
    (evaluate : Unit → Except Error Value) (empty : view.fields name = none) :
    primaryRead view name evaluate = evaluate () := by simp [primaryRead, empty]

/-- Indexed and symbolic lookup share their value authority: no independent
hash/vector agreement assumption is needed for successful memo cells. -/
theorem demandRead_primary (indexed : Bool) (site : Site) (view : View Value)
    (evaluate : Unit → Except Error Value) :
    demandRead indexed site view (fun _ => primaryRead view site.name evaluate) =
      primaryRead view site.name evaluate := by
  apply demandRead_sound
  intro value present
  exact primaryRead_present view site.name value evaluate present

/-- One successful publication updates exactly one primary cell. The input is the
state after evaluation/dependency work: failure adds no publication writes and
does not roll back callback effects or already memoized dependencies. -/
def commitPrimary (view : View Value) (name : String) (outcome : Except Error Value) :
    View Value × Except Error Value :=
  match outcome with
  | .error cause => (view, .error cause)
  | .ok value => (rememberCell view name value, .ok value)

/-- A refused force publishes neither a value nor a changed receiver/layout. -/
@[simp] theorem commitPrimary_error (view : View Value) (name : String) (cause : Error) :
    commitPrimary view name (.error cause) = (view, .error cause) := rfl

/-- Success transports the exact normalized value, without another wrapper. -/
@[simp] theorem commitPrimary_success (view : View Value) (name : String) (value : Value) :
    commitPrimary (Error := Error) view name (.ok value) =
      (rememberCell view name value, .ok value) := rfl

/-- Reusing either reader after success observes the exact one stored value. -/
theorem primaryRead_committed (view : View Value) (name : String) (value : Value)
    (evaluate : Unit → Except Error Value) :
    primaryRead (commitPrimary (Error := Error) view name (.ok value)).1 name evaluate = .ok value := by
  simp [commitPrimary, primaryRead, rememberCell]

/-- Publication leaves every disjoint memo cell unchanged. -/
theorem commitPrimary_frame (view : View Value) (name other : String)
    (outcome : Except Error Value) (different : other ≠ name) :
    (commitPrimary view name outcome).1.fields other = view.fields other := by
  cases outcome with
  | error => rfl
  | ok value => exact rememberCell_frame view name other value different

/-- Refusal cannot poison a later independent retry. -/
theorem commitPrimary_retry (view : View Value) (name : String) (cause : Error)
    (later : Except Error Value) :
    commitPrimary (commitPrimary view name (.error cause)).1 name later =
      commitPrimary view name later := rfl

/-- Clearing primary cells makes both readers demand the original evaluator.
Object invalidation additionally advances the existing source/layout guards. -/
theorem demandRead_cleared (indexed : Bool) (site : Site) (view : View Value)
    (evaluate : Unit → Except Error Value) :
    demandRead indexed site (deferCells view)
      (fun _ => primaryRead (deferCells view) site.name evaluate) = evaluate () := by
  rw [demandRead_primary]
  rfl

/-- Shape extension/reordering changes metadata, never a second value store. -/
def reshapePrimary (view : View Value) (names : List String) : View Value :=
  { view with names := names }

/-- Symbolic observation is invariant under a faithful metadata-only reshape. -/
theorem primaryRead_reshape (view : View Value) (names : List String) (name : String)
    (evaluate : Unit → Except Error Value) :
    primaryRead (reshapePrimary view names) name evaluate = primaryRead view name evaluate := rfl

/-- Even when owner/revision/layout pointers survive, changed shape identity must
reject the old offset. Runtime stores this immutable stamp in the existing site. -/
theorem read_reject_changed_shape (site : Site) (view : View Value)
    (different : site.names ≠ view.names) : read site view = none := by
  have stale : ¬ valid site view := fun current => different current.2.2.2
  simp [read, stale]

/-- Indexed fallback after reshape still shares the same current value authority. -/
theorem demandRead_reshape_primary (indexed : Bool) (site : Site) (view : View Value)
    (names : List String) (evaluate : Unit → Except Error Value) :
    demandRead indexed site (reshapePrimary view names)
      (fun _ => primaryRead view site.name evaluate) = primaryRead view site.name evaluate := by
  exact demandRead_primary indexed site (reshapePrimary view names) evaluate

/-- Source-operation cost only: successful dual publication writes two value
stores, primary publication writes one. Metadata/provenance work is separate. -/
def valuePublicationWrites (dual : Bool) (outcome : Except Error Value) : Nat :=
  match outcome with
  | .error _ => 0
  | .ok _ => if dual then 2 else 1

/-- No successful value-store write is charged for refused evaluation. -/
theorem valuePublicationWrites_error (dual : Bool) (cause : Error) :
    valuePublicationWrites (Value := Value) dual (.error cause) = 0 := rfl

/-- Primary publication eliminates one value write, without predicting time/GC. -/
theorem valuePublicationWrites_success (value : Value) :
    valuePublicationWrites (Error := Error) true (.ok value) =
      valuePublicationWrites (Error := Error) false (.ok value) + 1 := rfl

/-- A whole-workflow comparison must charge preparation separately: a saved write
does not imply a win when shape preparation, dispatch or GC costs more. -/
theorem primary_total_work_bound (prepareDual preparePrimary evaluations : Nat)
    (prepared : preparePrimary ≤ prepareDual + evaluations) :
    preparePrimary + evaluations ≤ prepareDual + 2 * evaluations := by omega

/-- Authenticate the actual metadata route before consulting cells or evaluating
callbacks. Host admission must check wrapper/ref, layout class and index route. -/
def routedPrimaryRead (admit : Except Error Unit) (view : Unit → View Value)
    (name : String) (evaluate : Unit → Except Error Value) : Except Error Value :=
  admit.bind (fun _ => primaryRead (view ()) name evaluate)

/-- A malformed route preserves its exact refusal without consulting the store. -/
theorem routedPrimaryRead_refused (cause : Error) (view : Unit → View Value)
    (name : String) (evaluate : Unit → Except Error Value) :
    routedPrimaryRead (.error cause) view name evaluate = .error cause := rfl

/-- Successfully admitted routes retain ordinary value/demand semantics. -/
theorem routedPrimaryRead_accepted (view : Unit → View Value) (name : String)
    (evaluate : Unit → Except Error Value) :
    routedPrimaryRead (.ok ()) view name evaluate = primaryRead (view ()) name evaluate := rfl

/-- Evaluation can grow the memo shape. Reuse its pre-evaluation index only when
that immutable descriptor survives; otherwise resolve against the current shape. -/
def finalValueOffset (before current : List String) (prior : Nat) (resolve : Unit → Nat) : Nat :=
  if before = current then prior else resolve ()

/-- Unchanged descriptors incur no second named resolution. -/
theorem finalValueOffset_unchanged (names : List String) (prior : Nat) (resolve : Unit → Nat) :
    finalValueOffset names names prior resolve = prior := by simp [finalValueOffset]

/-- A changed shape never publishes the old position as a current index. -/
theorem finalValueOffset_changed (before current : List String) (prior : Nat)
    (resolve : Unit → Nat) (changed : before ≠ current) :
    finalValueOffset before current prior resolve = resolve () := by simp [finalValueOffset, changed]

/-- The published index is correct for the final shape, including reorderings.
The resolver fidelity premise is the existing host shape/index correspondence. -/
theorem finalValueOffset_sound (before current : List String) (prior : Nat)
    (resolve : Unit → Nat) (name : String) (oldIndex : before[prior]? = some name)
    (newIndex : current[resolve ()]? = some name) :
    current[finalValueOffset before current prior resolve]? = some name := by
  by_cases same : before = current
  · simpa [finalValueOffset, same] using (same ▸ oldIndex)
  · simpa [finalValueOffset, same] using newIndex

/-- A retained view can certify an offset only while its receiver revision is live.
The caller's matching revision and token do not make an older view current. -/
def retainedValueHit (site : Site) (view : View Value) (current : Nat) : Option Nat :=
  if valid site view ∧ view.revision = current then some site.index else none

/-- Invalidation rejects the hit even when the caller supplies every old stamp. -/
theorem retainedValueHit_invalidated (graph : C4.Graph) (changed : List String)
    (cache : String → Object.RevisionCache Value) (name : String)
    (site : Site) (view : View Value) (captured : view.revision = (cache name).revision)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    retainedValueHit site view (Object.invalidateCaches graph changed cache name).revision = none := by
  have retired : view.revision ≠ (Object.invalidateCaches graph changed cache name).revision := by
    rw [captured]
    exact descendant_revision_rejected graph changed cache name affected
  simp [retainedValueHit, retired]

/-- A fresh binding still delivers its exact offset, including zero. -/
theorem retainedValueHit_current (site : Site) (view : View Value) (admitted : valid site view) :
    retainedValueHit site view view.revision = some site.index := by
  simp [retainedValueHit, admitted]

/-- Read a materialized cell on the retained allocation only at its live revision.
A shape change, a retired allocation, or eviction refuses before delivery. -/
def readBoundOffset (site : Site) (view : View Value) (current : Nat) (stale empty : Error) :
    Except Error Value :=
  if site.names = view.names ∧ site.revision = view.revision ∧ view.revision = current then
    match cell view site.index with
    | some value => .ok value
    | none => .error empty
  else .error stale

/-- Layout growth rejects an old offset even when it remains in bounds. -/
theorem readBoundOffset_stale (site : Site) (view : View Value) (current : Nat)
    (stale empty : Error) (changed : site.names ≠ view.names) :
    readBoundOffset site view current stale empty = .error stale := by
  simp [readBoundOffset, changed]

/-- A retained layout cannot read after its owning revision advances. -/
theorem readBoundOffset_retired (site : Site) (view : View Value) (current : Nat)
    (stale empty : Error) (advanced : view.revision ≠ current) :
    readBoundOffset site view current stale empty = .error stale := by
  simp [readBoundOffset, advanced]

/-- Every affected descendant rejects its old allocation after shared invalidation. -/
theorem readBoundOffset_invalidated (graph : C4.Graph) (changed : List String)
    (cache : String → Object.RevisionCache Value) (name : String)
    (site : Site) (view : View Value) (stale empty : Error)
    (captured : view.revision = (cache name).revision)
    (affected : name ∈ Proof.invalidatedNodes graph changed) :
    readBoundOffset site view (Object.invalidateCaches graph changed cache name).revision
      stale empty = .error stale := by
  apply readBoundOffset_retired
  rw [captured]
  exact descendant_revision_rejected graph changed cache name affected

/-- Even with a certified offset, an evicted cell refuses direct delivery. -/
theorem readBoundOffset_empty (site : Site) (view : View Value) (stale empty : Error)
    (same : site.names = view.names) (bound : site.revision = view.revision)
    (evicted : view.fields site.name = none) :
    readBoundOffset site view view.revision stale empty = .error empty := by
  have indexed : view.names[site.index]? = some site.name := same ▸ site.indexed
  simp [readBoundOffset, same, bound, cell, indexed, evicted]

/-- A filled live cell delivers its exact named value, including false or a function. -/
theorem readBoundOffset_current (site : Site) (view : View Value) (stale empty : Error)
    (same : site.names = view.names) (bound : site.revision = view.revision)
    (value : Value) (present : view.fields site.name = some value) :
    readBoundOffset site view view.revision stale empty = .ok value := by
  have indexed : view.names[site.index]? = some site.name := same ▸ site.indexed
  simp [readBoundOffset, same, bound, cell, indexed, present]

/-- Computed cardinality counts present cells, including false and functions.
The runtime sentinel must be disjoint from successful values. This is scalar
metadata over the single primary store, never a second store of values. -/
def populatedCells (cells : List (Option Value)) : Nat := cells.countP Option.isSome

/-- An overwrite adjusts cardinality only when presence changes. -/
def adjustPopulation (count : Nat) (old next : Option Value) : Nat :=
  count + (if next.isSome then 1 else 0) - (if old.isSome then 1 else 0)

/-- Every named/indexed write preserves the exact occupancy invariant. A faithful
current offset decomposes the primary cells into prefix, current cell and suffix. -/
theorem populatedCells_overwrite (beforeCells afterCells : List (Option Value)) (old next : Option Value) :
    populatedCells (beforeCells ++ next :: afterCells) =
      adjustPopulation (populatedCells (beforeCells ++ old :: afterCells)) old next := by
  cases old <;> cases next <;>
    simp [populatedCells, adjustPopulation, List.countP_append] <;> omega

/-- Declared but uncomputed fields do not contribute to cardinality. -/
@[simp] theorem populatedCells_empty (width : Nat) :
    populatedCells (List.replicate width (none : Option Value)) = 0 := by
  simp [populatedCells, List.countP_replicate]

/-- Shape growth inserts empty cells without forcing a callback or changing count.
The host also preserves symbolic value associations when rearranging offsets. -/
theorem populatedCells_extend (beforeCells afterCells : List (Option Value)) :
    populatedCells (beforeCells ++ none :: afterCells) = populatedCells (beforeCells ++ afterCells) := by
  simp [populatedCells, List.countP_append]

/-- A refused update does not publish its target. The supplied cells are the
post-callback state: nested successful writes remain visible and counted. -/
def commitCountedCell (beforeCells afterCells : List (Option Value)) (old : Option Value)
    (outcome : Except Error Value) : List (Option Value) :=
  match outcome with
  | .error _ => beforeCells ++ old :: afterCells
  | .ok value => beforeCells ++ some value :: afterCells

/-- Failure retains the actual post-callback cardinality, without rollback. -/
theorem commitCountedCell_refused (beforeCells afterCells : List (Option Value)) (old : Option Value) (cause : Error) :
    populatedCells (commitCountedCell beforeCells afterCells old (.error cause)) =
      populatedCells (beforeCells ++ old :: afterCells) := rfl

/-- Successful publication maintains the same invariant as a direct setter. -/
theorem commitCountedCell_success (beforeCells afterCells : List (Option Value)) (old : Option Value) (value : Value) :
    populatedCells (commitCountedCell (Error := Error) beforeCells afterCells old (.ok value)) =
      adjustPopulation (populatedCells (beforeCells ++ old :: afterCells)) old (some value) :=
  populatedCells_overwrite beforeCells afterCells old (some value)

/-- Source work only: a maintained scalar needs one metadata read; scanning
requires one cell observation per declared field. Construction/update work stays
charged separately, and this inequality predicts neither latency nor allocation. -/
theorem population_read_work (width : Nat) (nonempty : 0 < width) : 1 ≤ width := by omega

/-- Seed one authoritative store and its scalar occupancy in one traversal.
Names are the already admitted canonical shape, not a second value cache. The
runtime writes these resolved cells directly into its final fresh vector. -/
def seedPrimaryCells (names : List String) (resolve : String → Option Value) :
    List (Option Value) × Nat :=
  match names with
  | [] => ([], 0)
  | name :: rest =>
      let seeded := seedPrimaryCells rest resolve
      let value := resolve name
      (value :: seeded.1, seeded.2 + if value.isSome then 1 else 0)

/-- Fused preparation preserves every exact resolved cell, including false and
Function payloads. The host supplies finite canonical names and faithful lookup. -/
theorem seedPrimaryCells_values (names : List String) (resolve : String → Option Value) :
    (seedPrimaryCells names resolve).1 = names.map resolve := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp [seedPrimaryCells, ih]

/-- The count produced during seeding equals a separate scan's result, without
requiring that scan at runtime. Uncomputed declarations contribute zero. -/
theorem seedPrimaryCells_population (names : List String) (resolve : String → Option Value) :
    (seedPrimaryCells names resolve).2 = populatedCells (seedPrimaryCells names resolve).1 := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp [seedPrimaryCells, populatedCells, List.countP_cons] at ih ⊢
      exact ih

/-- A refused seed does not publish a replacement for an already live store.
The candidate is built privately; prior callback effects are not rolled back. -/
def publishSeed (current : List (Option Value))
    (candidate : Except Error (List (Option Value))) : List (Option Value) :=
  match candidate with
  | .error _ => current
  | .ok cells => cells

/-- Failure leaves the existing value authority available for independent retry. -/
@[simp] theorem publishSeed_refused (current : List (Option Value)) (cause : Error) :
    publishSeed current (.error cause) = current := rfl

/-- A later successful preparation publishes exactly its own computed cells. -/
theorem publishSeed_retry (current cells : List (Option Value)) (cause : Error) :
    publishSeed (Error := Error) (publishSeed current (.error cause)) (.ok cells) = cells := rfl

/-- Explicit loop iterations only: the old seed traversal and separate count
traversal each visit the width. The fused setter still checks old-cell presence
and updates metadata; its primitive reads/writes, allocation and GC are not
charged by this deliberately partial traversal model. -/
def seedPreparationLoopSteps (fused : Bool) (width : Nat) : Nat :=
  if fused then width else width + width

/-- Exactly the separate count traversal disappears from this source work model. -/
theorem seed_population_pass_work (width : Nat) :
    seedPreparationLoopSteps false width = seedPreparationLoopSteps true width + width := rfl

/-- Bind an existing site representation to the final successful receiver view.
Only guards and the certified offset are retained; primary cells are untouched. -/
def currentValueSite (view : View Value) (name : String) (index : Nat)
    (indexed : view.names[index]? = some name) : Site :=
  ⟨view.owner, view.revision, view.token, view.names, name, index, indexed⟩

/-- Admit an offset and claimed revision before replacing the current site.
An absent proposal clears the guard. A refusal retains the prior binding. -/
def bindValueOffset (prior : Option Site) (view : View Value) (name : String)
    (proposal : Option Nat) (claimed current : Nat) (stale invalid : Error) :
    Option Site × Except Error Unit :=
  match proposal with
  | none => (none, .ok ())
  | some index =>
    if claimed = view.revision ∧ view.revision = current then
      if indexed : view.names[index]? = some name then
        (some (currentValueSite view name index indexed), .ok ())
      else (prior, .error invalid)
    else (prior, .error stale)

/-- An in-bounds sibling offset and an out-of-bounds offset both refuse without
changing the existing binding. -/
theorem bindValueOffset_refused (prior : Option Site) (view : View Value) (name : String)
    (index : Nat) (stale invalid : Error) (wrong : view.names[index]? ≠ some name) :
    bindValueOffset prior view name (some index) view.revision view.revision stale invalid =
      (prior, .error invalid) := by
  simp [bindValueOffset, wrong]

/-- Claiming the new revision cannot reauthorize a retained old layout. -/
theorem bindValueOffset_retired (prior : Option Site) (view : View Value) (name : String)
    (index claimed current : Nat) (stale invalid : Error) (advanced : view.revision ≠ current) :
    bindValueOffset prior view name (some index) claimed current stale invalid =
      (prior, .error stale) := by
  simp [bindValueOffset, advanced]

/-- An admitted offset on the current layout delivers only the materialized named value. -/
theorem bindValueOffset_read (prior : Option Site) (view : View Value) (name : String)
    (index : Nat) (invalid stale empty : Error) (indexed : view.names[index]? = some name)
    (value : Value) (present : view.fields name = some value) :
    (bindValueOffset prior view name (some index) view.revision view.revision stale invalid).1.map
      (fun site => readBoundOffset site view view.revision stale empty) = some (.ok value) := by
  simp [bindValueOffset, indexed, readBoundOffset, currentValueSite, cell, present]

/-- Cold demand and an evicted warm cell share this metadata publication step.
The supplied view is after ordinary evaluation and its primary value writes.
An error preserves the prior credential and exact cause; no successful site is
fabricated when the name still has no certified offset. -/
def finishIndexedDemand (prior : Option Site) (view : View Value) (name : String)
    (offset : Option { index : Nat // view.names[index]? = some name })
    (outcome : Except Error Value) : Option Site × Except Error Value :=
  match outcome with
  | .error cause => (prior, .error cause)
  | .ok value => (offset.map (fun found => currentValueSite view name found.val found.property), .ok value)

/-- Refused demand leaves credentials unchanged and preserves the original cause.
Any earlier dependency effects are represented by the supplied post-demand view. -/
@[simp] theorem finishIndexedDemand_error (prior : Option Site) (view : View Value) (name : String)
    (offset : Option { index : Nat // view.names[index]? = some name }) (cause : Error) :
    finishIndexedDemand prior view name offset (.error cause) = (prior, .error cause) := rfl

/-- No resolved name means no successful indexed guard, even on value success. -/
@[simp] theorem finishIndexedDemand_unindexed (prior : Option Site) (view : View Value)
    (name : String) (value : Value) :
    finishIndexedDemand (Error := Error) prior view name none (.ok value) = (none, .ok value) := rfl

/-- Successful recovery erases the difference between cold and evicted credentials. -/
theorem finishIndexedDemand_same_success (cold warm : Option Site) (view : View Value) (name : String)
    (offset : Option { index : Nat // view.names[index]? = some name }) (value : Value) :
    finishIndexedDemand (Error := Error) cold view name offset (.ok value) =
      finishIndexedDemand warm view name offset (.ok value) := rfl

/-- The published owner/revision/layout/shape guards describe the FINAL view,
including a shape grown during re-evaluation of an evicted memo cell. -/
theorem currentValueSite_valid (view : View Value) (name : String) (index : Nat)
    (indexed : view.names[index]? = some name) :
    valid (currentValueSite view name index indexed) view := ⟨rfl, rfl, rfl, rfl⟩

/-- Successful recovery retains the exact primary false/Function value; there is
no additional copy or write into a site-local value store. -/
theorem currentValueSite_read (view : View Value) (name : String) (index : Nat)
    (indexed : view.names[index]? = some name) :
    read (currentValueSite view name index indexed) view = view.fields name :=
  read_sound _ _ (currentValueSite_valid view name index indexed)

/-- The next unchanged read needs no named offset resolution after recovery.
This counts one metadata lookup only, not evaluator/guard/GC or wall-clock work. -/
theorem currentValueSite_resolution (view : View Value) (name : String) (index : Nat)
    (indexed : view.names[index]? = some name) :
    resolutionWork (currentValueSite view name index indexed) view = 0 :=
  resolutionWork_shared _ _ rfl

/-- A later supported source revision still rejects the recovered credential. -/
theorem currentValueSite_revised (view : View Value) (name : String) (index : Nat)
    (indexed : view.names[index]? = some name) (next : View Value)
    (changed : view.revision ≠ next.revision) :
    read (currentValueSite view name index indexed) next = none :=
  reject_revision _ _ changed

/-- A still-valid site rebound to the same certified offset is identical.
Proof irrelevance removes the implementation's proof witness. -/
theorem currentValueSite_existing (site : Site) (view : View Value)
    (current : valid site view) :
    currentValueSite view site.name site.index (current.2.2.2 ▸ site.indexed) = site := by
  rcases site with ⟨owner, revision, token, names, name, index, indexed⟩
  rcases current with ⟨ho, hr, ht, hn⟩
  cases ho; cases hr; cases ht; cases hn
  rfl

/-- Successful demand may retain an already-current guard: credential and value
are identical, while primary cells remain the only value authority. -/
theorem finishIndexedDemand_keep (site : Site) (view : View Value)
    (current : valid site view) (value : Value) :
    finishIndexedDemand (Error := Error) (some site) view site.name
      (some ⟨site.index, current.2.2.2 ▸ site.indexed⟩) (.ok value) =
      (some site, .ok value) := by
  simp only [finishIndexedDemand, Option.map_some, currentValueSite_existing site view current]

/-- Canonical single-key insertion splits the old vector at the new key's
certified offset. Bulk copies preserve both segments; none is an uncomputed cell.
Canonical ordering and faithful standard vector copying are refinement premises. -/
def growPrimaryCells (before after : List (Option Value)) (value : Option Value) :=
  before ++ value :: after

/-- Removing the inserted position restores all original cells, including gaps. -/
theorem growPrimaryCells_restore (before after : List (Option Value)) (value : Option Value) :
    (growPrimaryCells before after value).take before.length ++
      (growPrimaryCells before after value).drop (before.length + 1) = before ++ after := by
  simp [growPrimaryCells, List.drop_append]

/-- Occupancy transfers without scanning old cells: only the inserted cell can
add one present value. False and functions are ordinary some payloads. -/
theorem growPrimaryCells_population (before after : List (Option Value)) (value : Option Value) :
    populatedCells (growPrimaryCells before after value) =
      populatedCells (before ++ after) + (if value.isSome then 1 else 0) := by
  cases value <;> simp [growPrimaryCells, populatedCells, List.countP_append] <;> omega

/-- Count old-value named probes only. Bulk copies still visit all old cells;
shape preparation, allocation and physical GC costs remain outside this count. -/
def growthNamedProbes (bulk : Bool) (width : Nat) : Nat := if bulk then 0 else width

/-- Bulk copying removes name probes, not all preparation work or wall time. -/
theorem growthNamedProbes_saved (width : Nat) :
    growthNamedProbes false width = growthNamedProbes true width + width := by simp [growthNamedProbes]


/-- A public runtime name is admitted before observation, preparation or a named
HashTable operation. String keys denote symbol identities, not display spelling.
The host standard contract supplies admission; callbacks here are terminating. -/
def withAdmittedName (admit : RawName → Except Error String)
    (operation : String → State → Except Error Result × State)
    (raw : RawName) (state : State) : Except Error Result × State :=
  match admit raw with
  | .error cause => (.error cause, state)
  | .ok name => operation name state

/-- Refused names preserve the exact entire receiver/cache/observation state.
In particular, no symbolic hash, updater or fallback can run in this model. -/
theorem withAdmittedName_refused (admit : RawName → Except Error String)
    (operation : String → State → Except Error Result × State)
    (raw : RawName) (state : State) (cause : Error)
    (refused : admit raw = .error cause) :
    withAdmittedName admit operation raw state = (.error cause, state) := by
  simp [withAdmittedName, refused]

/-- Accepted symbolic identities delegate unchanged, including offset zero,
missing-name fallback, false/Function values and original callback failures. -/
theorem withAdmittedName_accepted (admit : RawName → Except Error String)
    (operation : String → State → Except Error Result × State)
    (raw : RawName) (state : State) (name : String) (accepted : admit raw = .ok name) :
    withAdmittedName admit operation raw state = operation name state := by
  simp [withAdmittedName, accepted]

/-- Normal and indexed implementations keep their established equivalence when
placed behind the same runtime admission boundary; neither route needs a cache. -/
theorem withAdmittedName_congr (admit : RawName → Except Error String)
    (ordinary indexed : String → State → Except Error Result × State)
    (same : ∀ name state, ordinary name state = indexed name state)
    (raw : RawName) (state : State) :
    withAdmittedName admit ordinary raw state = withAdmittedName admit indexed raw state := by
  cases h : admit raw <;> simp [withAdmittedName, h, same]

/-- Successful dispatch witnesses an admitted symbol and the actual operation's
result/state. Admission cannot turn an unknown name or failed callback into success. -/
theorem withAdmittedName_success (admit : RawName → Except Error String)
    (operation : String → State → Except Error Result × State)
    (raw : RawName) (state final : State) (value : Result) :
    withAdmittedName admit operation raw state = (.ok value, final) ↔
      ∃ name, admit raw = .ok name ∧ operation name state = (.ok value, final) := by
  cases h : admit raw <;> simp [withAdmittedName, h]

/-- Failures distinguish rejected syntax, which leaves the complete state alone,
from an admitted query's own failure and effects. A missing/hidden symbol is not
silently reclassified as malformed syntax. -/
theorem withAdmittedName_failure (admit : RawName → Except Error String)
    (operation : String → State → Except Error Result × State)
    (raw : RawName) (state final : State) (cause : Error) :
    withAdmittedName admit operation raw state = (.error cause, final) ↔
      (admit raw = .error cause ∧ state = final) ∨
      ∃ name, admit raw = .ok name ∧ operation name state = (.error cause, final) := by
  cases h : admit raw <;> simp [withAdmittedName, h]

/-- An admitted presence predicate's false is a successful value. Name admission
neither forces a fallback nor confuses structural absence with an exception. -/
theorem withAdmittedName_false (admit : RawName → Except Error String)
    (operation : String → State → Except Error Bool × State)
    (raw : RawName) (state final : State) (name : String)
    (accepted : admit raw = .ok name) (absent : operation name state = (.ok false, final)) :
    withAdmittedName admit operation raw state = (.ok false, final) := by
  simp [withAdmittedName, accepted, absent]

/-- Standard name admission surrounds the entire receiver-bound preparation and
observation protocol. Rejection suppresses both phases without needing another
cache or a separately admitted internal helper. -/
theorem withAdmittedName_refused_preparation (admit : RawName → Except Error String)
    (prepare : String → State → Except Error Prepared × State)
    (observe : String → Prepared → State → Except Error Result × State)
    (raw : RawName) (state : State) (refused : admit raw = .error cause) :
    withAdmittedName admit (fun name initial =>
      let (result, preparedState) := prepare name initial
      match result with
      | .error error => (.error error, preparedState)
      | .ok prepared => observe name prepared preparedState) raw state = (.error cause, state) := by
  simp [withAdmittedName, refused]

/-- The finite constructor request owns names and entry pairs, while values
remain opaque. In the host this is one shallow capture before source callbacks. -/
structure SeedRequest (Value : Type) where
  names : List String
  entries : List (String × Value)

/-- Source-discovered keys extend the captured request; later caller metadata
cannot retarget its original names or entry identities. -/
def seedRequestNames (request : SeedRequest Value) (discovered : List String) : List String :=
  request.names ++ discovered ++ request.entries.map Prod.fst

/-- Seed values are installed first; captured explicit rows retain last-write
precedence, order and exact payload identity, without equality on Function values. -/
def seedRequestEntries (request : SeedRequest Value) (seed : List (String × Value)) :
    List (String × Value) := seed ++ request.entries

/-- Two standard source enumeration handoffs share an explicit external world.
Allocation/install are the existing private store operations. Their finite,
faithful interpretation is a premise; no callback effects are rolled back. -/
def prepareSeedRequest (request : SeedRequest Value) (world : World)
    (discover : World → Except Error (List String) × World)
    (allocate : List String → Except Error Store)
    (enumerate : World → Except Error (List (String × Value)) × World)
    (install : Store → List (String × Value) → Except Error Store) :
    Except Error Store × World :=
  let (keys, afterDiscovery) := discover world
  match keys with
  | .error cause => (.error cause, afterDiscovery)
  | .ok keys =>
    match allocate (seedRequestNames request keys) with
    | .error cause => (.error cause, afterDiscovery)
    | .ok candidate =>
      let (rows, afterSeed) := enumerate afterDiscovery
      match rows with
      | .error cause => (.error cause, afterSeed)
      | .ok rows => (install candidate (seedRequestEntries request rows), afterSeed)

/-- Capture and install retain the original explicit payloads even when source
callbacks replace the complete externally visible request during enumeration. -/
theorem seedRequest_success (request : SeedRequest Value) (world first last : World)
    (discover : World → Except Error (List String) × World)
    (allocate : List String → Except Error Store)
    (enumerate : World → Except Error (List (String × Value)) × World)
    (install : Store → List (String × Value) → Except Error Store)
    (keys : List String) (rows : List (String × Value)) (candidate : Store)
    (discovered : discover world = (.ok keys, first))
    (allocated : allocate (seedRequestNames request keys) = .ok candidate)
    (seeded : enumerate first = (.ok rows, last)) :
    prepareSeedRequest request world discover allocate enumerate install =
      (install candidate (rows ++ request.entries), last) := by
  simp [prepareSeedRequest, discovered, allocated, seeded, seedRequestEntries]

/-- Discovery refusal wins before allocation, seeding or installation, while
preserving exactly the source effects already performed. -/
theorem seedRequest_discovery_refused (request : SeedRequest Value) (world after : World)
    (discover : World → Except Error (List String) × World)
    (allocate : List String → Except Error Store)
    (enumerate : World → Except Error (List (String × Value)) × World)
    (install : Store → List (String × Value) → Except Error Store) (cause : Error)
    (refused : discover world = (.error cause, after)) :
    prepareSeedRequest request world discover allocate enumerate install = (.error cause, after) := by
  simp [prepareSeedRequest, refused]

/-- Allocation refusal suppresses the second source handoff and all entry writes. -/
theorem seedRequest_allocation_refused (request : SeedRequest Value) (world after : World)
    (discover : World → Except Error (List String) × World)
    (allocate : List String → Except Error Store)
    (enumerate : World → Except Error (List (String × Value)) × World)
    (install : Store → List (String × Value) → Except Error Store)
    (keys : List String) (cause : Error)
    (discovered : discover world = (.ok keys, after))
    (refused : allocate (seedRequestNames request keys) = .error cause) :
    prepareSeedRequest request world discover allocate enumerate install = (.error cause, after) := by
  simp [prepareSeedRequest, discovered, refused]

/-- A seed refusal cannot publish captured rows, but its external effects remain. -/
theorem seedRequest_enumeration_refused (request : SeedRequest Value) (world first after : World)
    (discover : World → Except Error (List String) × World)
    (allocate : List String → Except Error Store)
    (enumerate : World → Except Error (List (String × Value)) × World)
    (install : Store → List (String × Value) → Except Error Store)
    (keys : List String) (candidate : Store) (cause : Error)
    (discovered : discover world = (.ok keys, first))
    (allocated : allocate (seedRequestNames request keys) = .ok candidate)
    (refused : enumerate first = (.error cause, after)) :
    prepareSeedRequest request world discover allocate enumerate install = (.error cause, after) := by
  simp [prepareSeedRequest, discovered, allocated, refused]

/-- Source effects cannot change the explicit suffix installed after seed rows. -/
theorem seedRequest_explicit_suffix (request : SeedRequest Value) (seed : List (String × Value)) :
    (seedRequestEntries request seed).drop seed.length = request.entries := by
  simp [seedRequestEntries]

/-- No new observer or cache is introduced: the conditional capture copies names,
entry-spine cells and entry pairs once. Opaque values and source enumeration,
indexing, vector allocation, primitive/GC and wall-clock costs are excluded. -/
def seedRequestCaptureCells (hasSource : Bool) (names entries : Nat) : Nat :=
  if hasSource then names + 2 * entries else 0

/-- The source-free path performs no additional metadata copying. -/
theorem seedRequestCaptureCells_without_source (names entries : Nat) :
    seedRequestCaptureCells false names entries = 0 := rfl

/-- Capturing a source-backed request is linear in its explicit metadata width. -/
theorem seedRequestCaptureCells_bound (hasSource : Bool) (names entries : Nat) :
    seedRequestCaptureCells hasSource names entries ≤ 2 * (names + entries) := by
  cases hasSource <;> simp [seedRequestCaptureCells] <;> omega

end LeanPoo.Prototype.Representation
