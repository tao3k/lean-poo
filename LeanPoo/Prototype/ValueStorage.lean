import LeanPoo.Prototype.Representation

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

end LeanPoo.Prototype.Representation
