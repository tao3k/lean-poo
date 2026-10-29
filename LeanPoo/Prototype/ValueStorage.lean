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

end LeanPoo.Prototype.Representation
