import LeanPoo.Functional.DependencyAnalysis
import LeanPoo.Object.Ranked
import LeanPoo.Prototype.GeneralizedPrototype

/-! Finite, inspectable generalized component declarations. This advances the
future generalized-prototype protocol: inferred locality, checked scheduling and
actual closure share the existing computation and delayed-inheritance semantics. -/
namespace LeanPoo.Functional.GeneralizedGraph

abbrev Outcome (Key : Type) (Value : Key → Type) (key : Key) :=
  Except (ComputationError Key) (Value key)
abbrev State (Key : Type) (Value : Key → Type) := (key : Key) → Option (Outcome Key Value key)
abbrev Code (Key : Type) (Value : Key → Type) (key : Key) :=
  Computation Unit Key (fun _ dep => Outcome Key Value dep) (fun _ => Outcome Key Value key)

structure Declaration (Key : Type) (Value : Key → Type) where
  keys : List Key
  code : (key : Key) → Option (Code Key Value key)
  base : State Key Value

variable {Key : Type} {Value : Key → Type} [DecidableEq Key]

def setSlot (state : State Key Value) (key : Key) (value : Option (Outcome Key Value key)) : State Key Value :=
  fun query => if same : key = query then same ▸ value else state query

/-- Redefinition adds finite support and replaces one typed declaration. -/
def Declaration.define (spec : Declaration Key Value) (key : Key) (code : Code Key Value key) :
    Declaration Key Value :=
  { spec with
    keys := if key ∈ spec.keys then spec.keys else spec.keys ++ [key]
    code := fun query => if same : key = query then same ▸ some code else spec.code query }

/-- Remove the provider but retain its key as an observable absence. Readers
using `need`, `inspect` and `deny` therefore keep their distinct semantics. -/
def Declaration.remove (spec : Declaration Key Value) (key : Key) : Declaration Key Value :=
  { spec with
    code := fun query => if key = query then none else spec.code query
    base := setSlot spec.base key none }

def Declaration.setBase (spec : Declaration Key Value) (key : Key)
    (value : Option (Outcome Key Value key)) : Declaration Key Value :=
  { spec with base := setSlot spec.base key value }

theorem Declaration.define_at (spec : Declaration Key Value) (key : Key) (code : Code Key Value key) :
    (spec.define key code).code key = some code := by simp [define]

theorem Declaration.define_frame (spec : Declaration Key Value) (key query : Key)
    (code : Code Key Value key) (different : key ≠ query) :
    (spec.define key code).code query = spec.code query := by simp [define, different]

def provider (state : State Key Value) : Provider Unit Key (fun _ key => Outcome Key Value key) :=
  fun key => (state key).map fun value _ => value

def Declaration.footprint (spec : Declaration Key Value) (key : Key) : DependencyFootprint Key :=
  if key ∈ spec.keys then ((spec.code key).map Computation.analyze).getD {} else {}

def Declaration.reads (spec : Declaration Key Value) (key : Key) : List Key :=
  (spec.footprint key).values ++ (spec.footprint key).presences

/-- Flatten evaluation and component failures without dropping either error. -/
def Declaration.resolve (spec : Declaration Key Value) (key : Key) (self : State Key Value) :
    Option (Outcome Key Value key) :=
  if key ∈ spec.keys then
    match spec.code key with
    | none => spec.base key
    | some code => some ((code.evaluate (provider self) ()).bind id)
  else spec.base key

/-- A typed source edit cannot silently change another slot's resolver. -/
theorem Declaration.define_resolve_frame (spec : Declaration Key Value) (key query : Key)
    (code : Code Key Value key) (different : key ≠ query) (self : State Key Value) :
    (spec.define key code).resolve query self = spec.resolve query self := by
  by_cases active : key ∈ spec.keys
  · simp [resolve, define, active, different]
  · simp [resolve, define, active, different, Ne.symm different]

theorem Declaration.remove_resolve_frame (spec : Declaration Key Value) (key query : Key)
    (different : key ≠ query) (self : State Key Value) :
    (spec.remove key).resolve query self = spec.resolve query self := by
  simp [resolve, remove, setSlot, different]

theorem Declaration.setBase_resolve_frame (spec : Declaration Key Value) (key query : Key)
    (value : Option (Outcome Key Value key)) (different : key ≠ query) (self : State Key Value) :
    (spec.setBase key value).resolve query self = spec.resolve query self := by
  simp [resolve, setBase, setSlot, different]

/-- A fragment updates exactly its own slot; the inherited dictionary is framed. -/
def Declaration.protocol (spec : Declaration Key Value) :
    Prototype.Generalized.Protocol (State Key Value) (State Key Value) Key :=
  ⟨id, fun key => Prototype.lensGen (fun raw (_ : Unit) => raw key)
    (fun value raw query => if same : key = query then same ▸ value () else raw query)
    (fun (_ : Unit) self _ (_ : Unit) => spec.resolve key self.get) ()⟩

theorem Declaration.assemble_apply (spec : Declaration Key Value) (fragments : List Key)
    (self parent : State Key Value) (key : Key) :
    spec.protocol.step fragments self parent key =
      if key ∈ fragments then spec.resolve key self else parent key := by
  induction fragments with
  | nil => rfl
  | cons first rest ih =>
    change setSlot (spec.protocol.step rest self parent) first (spec.resolve first self) key = _
    by_cases same : first = key
    · subst key; simp [setSlot]
    · simp [setSlot, same, ih, Ne.symm same]

theorem Declaration.step_eq (spec : Declaration Key Value) (self : State Key Value) :
    spec.protocol.step spec.keys self spec.base = fun key => spec.resolve key self := by
  funext key
  rw [spec.assemble_apply]
  split
  · rfl
  · simp_all [resolve]

theorem Declaration.locality (spec : Declaration Key Value) (key : Key)
    (known : (spec.footprint key).unknown = false) (left right : State Key Value)
    (same : ∀ dep ∈ spec.reads key, left dep = right dep) :
    spec.resolve key left = spec.resolve key right := by
  unfold resolve
  split <;> rename_i active
  · cases codeEq : spec.code key with
    | none => rfl
    | some code =>
      have footprintEq : spec.footprint key = code.analyze := by
        simp [footprint, active, codeEq]
      have evaluates := code.evaluate_congr (provider left) (provider right)
        (by simpa [footprintEq] using known)
        (by
          intro dep member
          unfold provider
          rw [same dep (by simp [reads, footprintEq, member])])
        (by
          intro dep member
          unfold provider
          rw [same dep (by simp [reads, footprintEq, member])]) ()
      simp only [evaluates]
  · rfl

inductive Error (Key : Type) where
  | opaque (key : Key)
  | dependency (error : Object.DependencyError Key)
  deriving Repr

/-- The schedule is executable metadata; its rank proof certifies every read. -/
structure Scheduled (spec : Declaration Key Value) where
  order : List Key
  resolver : Prototype.RankedResolver spec.resolve
  edgeLower : ∀ key dep, dep ∈ spec.reads key → resolver.rank dep < resolver.rank key
  known : ∀ key, (spec.footprint key).unknown = false

/-- Transfer a checked schedule across a revision with the same complete read
footprint. Resolver bodies and base values may change; their closure is rebuilt
at the retained ranks. This does not reuse resolved values. -/
def Scheduled.rebase {old spec : Declaration Key Value} (prior : Scheduled old)
    (reads : ∀ key, spec.reads key = old.reads key)
    (known : ∀ key, (spec.footprint key).unknown = false) : Scheduled spec where
  order := prior.order
  resolver := ⟨prior.resolver.rank, by
    intro key left right lower
    apply spec.locality key (known key)
    intro dep member
    exact lower dep (prior.edgeLower key dep (by simpa [reads key] using member))⟩
  edgeLower := by intro key dep member; exact prior.edgeLower key dep (by simpa [reads key] using member)
  known := known

theorem Scheduled.rebase_order {old spec : Declaration Key Value} (prior : Scheduled old)
    (reads known) : (prior.rebase (spec := spec) reads known).order = prior.order := rfl

theorem Scheduled.rebase_rank {old spec : Declaration Key Value} (prior : Scheduled old)
    (reads known) : (prior.rebase (spec := spec) reads known).resolver.rank = prior.resolver.rank := rfl

variable [BEq Key] [LawfulBEq Key] [Hashable Key]

def Declaration.schedule (spec : Declaration Key Value) : Except (Error Key) (Scheduled spec) := do
  if known : spec.keys.all (fun key => !(spec.footprint key).unknown) = true then
    let order ← (Object.dependencyOrder spec.keys spec.reads).mapError Error.dependency
    let rank := fun key => order.idxOf key
    if checked : spec.keys.all (fun key => (spec.reads key).all
        (fun dep => decide (rank dep < rank key))) = true then
      have supported : ∀ key dep, dep ∈ spec.reads key → key ∈ spec.keys := by
        intro key dep member
        by_cases active : key ∈ spec.keys
        · exact active
        · simp [reads, footprint, active] at member
      have edge : ∀ key dep, dep ∈ spec.reads key → rank dep < rank key := by
        intro key dep member
        exact of_decide_eq_true (List.all_eq_true.mp
          (List.all_eq_true.mp checked key (supported key dep member)) dep member)
      return ⟨order, ⟨rank, by
        intro key left right lower
        apply spec.locality key
        · by_cases active : key ∈ spec.keys
          · have h := List.all_eq_true.mp known key active
            simpa using h
          · simp [footprint, active]
        · intro dep member
          exact lower dep (edge key dep member)⟩, edge, by
        intro key
        by_cases active : key ∈ spec.keys
        · have h := List.all_eq_true.mp known key active
          simpa using h
        · simp [footprint, active]⟩
    else throw (.dependency (.invalidOrder order))
  else
    match spec.keys.find? (fun key => (spec.footprint key).unknown) with
    | some key => throw (Error.opaque key)
    | none => throw (.dependency (.invalidOrder spec.keys))

def Scheduled.closed {spec : Declaration Key Value} (scheduled : Scheduled spec) :
    Prototype.Generalized.Closed spec.protocol spec.keys spec.base :=
  ⟨scheduled.resolver.close, by
    rw [spec.step_eq]
    funext key
    exact scheduled.resolver.closed key⟩

/-- No caller supplies a cooked result, a final provider, or a stability proof. -/
def Declaration.close (spec : Declaration Key Value) :
    Except (Error Key) (Prototype.Generalized.Closed spec.protocol spec.keys spec.base) :=
  spec.schedule.map Scheduled.closed

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
theorem Scheduled.unique {spec : Declaration Key Value} (scheduled : Scheduled spec)
    (other : Prototype.Generalized.Closed spec.protocol spec.keys spec.base) :
    other.raw = scheduled.closed.raw := by
  funext key
  apply scheduled.resolver.unique other.raw
  intro query
  have fixed := congrFun other.fixed query
  rw [spec.step_eq] at fixed
  exact fixed

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Inferred invalidation covers values and availability, including both branches. -/
theorem Declaration.retained (spec : Declaration Key Value) (key : Key)
    (known : (spec.footprint key).unknown = false) (left right : State Key Value)
    (same : ∀ dep ∈ spec.reads key, left dep = right dep) :
    spec.resolve key left = spec.resolve key right := spec.locality key known left right same

/-- Transitive invalidation includes availability observations. The schedule's
rank, rather than an arbitrary fuel bound, makes this computation total. -/
def Scheduled.invalidates {spec : Declaration Key Value} (scheduled : Scheduled spec)
    (changed : Key → Bool) (key : Key) : Bool :=
  changed key || (spec.reads key).any (fun dep =>
    if _lower : scheduled.resolver.rank dep < scheduled.resolver.rank key then
      scheduled.invalidates changed dep else true)
termination_by scheduled.resolver.rank key

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
theorem Scheduled.invalidates_eq {spec : Declaration Key Value} (scheduled : Scheduled spec)
    (changed : Key → Bool) (key : Key) :
    scheduled.invalidates changed key =
      (changed key || (spec.reads key).any (scheduled.invalidates changed)) := by
  rw [invalidates]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨dep, member, value⟩
    exact ⟨dep, member, by simpa [scheduled.edgeLower key dep member] using value⟩
  · rintro ⟨dep, member, value⟩
    exact ⟨dep, member, by simpa [scheduled.edgeLower key dep member] using value⟩

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Invalidation reaches each actual reader of a shared value or presence,
including reads inferred from an unselected conditional branch. -/
theorem Scheduled.invalidates_reader {spec : Declaration Key Value} (scheduled : Scheduled spec)
    (changed : Key → Bool) (reader dependency : Key) (reads : dependency ∈ spec.reads reader)
    (dirty : scheduled.invalidates changed dependency = true) :
    scheduled.invalidates changed reader = true := by
  rw [scheduled.invalidates_eq]
  apply Bool.or_eq_true_iff.mpr
  exact .inr (List.any_eq_true.mpr ⟨dependency,reads,dirty⟩)

omit [BEq Key] [LawfulBEq Key] [Hashable Key] in
/-- Invalidation is sufficient for reuse only when unchanged source resolvers
are actually equal. A version label is never an equality certificate. -/
theorem Scheduled.unaffected {spec next : Declaration Key Value} (scheduled : Scheduled spec)
    (changed : Key → Bool)
    (unchanged : ∀ key, changed key = false → ∀ self, next.resolve key self = spec.resolve key self)
    (candidate : Prototype.Generalized.Closed next.protocol next.keys next.base) (key : Key)
    (safe : scheduled.invalidates changed key = false) :
    candidate.raw key = scheduled.closed.raw key := by
  have agree : ∀ n key, scheduled.resolver.rank key = n →
      scheduled.invalidates changed key = false → candidate.raw key = scheduled.closed.raw key := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro query ranked safe
      rw [scheduled.invalidates_eq] at safe
      have sourceSafe : changed query = false := by simpa using (Bool.or_eq_false_iff.mp safe).1
      have depsSafe : (spec.reads query).any (scheduled.invalidates changed) = false :=
        (Bool.or_eq_false_iff.mp safe).2
      have fixed := congrFun candidate.fixed query
      rw [next.step_eq] at fixed
      dsimp only at fixed
      rw [← fixed, unchanged query sourceSafe]
      calc
        spec.resolve query candidate.raw = spec.resolve query scheduled.closed.raw := by
          apply spec.locality query (scheduled.known query)
          intro dep member
          apply ih (scheduled.resolver.rank dep) (by simpa [ranked] using scheduled.edgeLower query dep member)
            dep rfl
          have h := List.any_eq_false.mp depsSafe dep member
          simpa using h
        _ = scheduled.closed.raw query := scheduled.resolver.closed query
  exact agree _ key rfl safe

end LeanPoo.Functional.GeneralizedGraph
