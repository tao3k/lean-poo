import LeanPoo.Functional.PrototypeTypes

/-! Observational structural row replacement. Field relations are parameters so
existing scalar/Function proofs and nested row proofs can be composed. Mutable
write variance and arbitrary predicate implication are not inferred. -/
namespace LeanPoo.Functional.RowTypes

/-- Closed rows restrict visible keys; open rows promise only their listed fields. -/
structure Row (Key Field : Type) where
  fields : List (Key × Field)
  closed : Bool
  deriving Repr, DecidableEq
/-- First named field lookup; the Scheme syntax admission also rejects duplicates. -/
def lookup [DecidableEq Key] : List (Key × Field) → Key → Option Field
  | [], _ => none
  | (key, type) :: rest, name => if key = name then some type else lookup rest name

/-- Successful lookup names a real declared field, rather than a zip prefix. -/
theorem lookup_mem [DecidableEq Key] (fields : List (Key × Field)) (name type)
    (found : lookup fields name = some type) : (name, type) ∈ fields := by
  induction fields with
  | nil => simp [lookup] at found
  | cons head rest ih =>
    rcases head with ⟨key, value⟩
    by_cases same : key = name
    · subst key; simp [lookup] at found; subst value; simp
    · simp [lookup, same] at found
      exact List.mem_cons.mpr (.inr (ih found))

/-- Closed target shape refuses open source rows and extra declared source keys. -/
def shape [DecidableEq Key] (source target : Row Key Field) : Bool :=
  !target.closed || (source.closed && source.fields.all fun field => (lookup target.fields field.1).isSome)
/-- Exact field presence is required before the supplied replacement comparison. -/
def check [DecidableEq Key] (test : Field → Field → Bool) (source target : Row Key Field) : Bool :=
  shape source target && target.fields.all fun field =>
    match lookup source.fields field.1 with
    | none => false
    | some actual => test actual field.2

/-- Declarative row replacement: exact closed shape and covariant read-only fields. -/
def Replaces [DecidableEq Key] (relation : Field → Field → Prop) (source target : Row Key Field) : Prop :=
  (target.closed = true → source.closed = true ∧
    ∀ name type, lookup source.fields name = some type → ∃ expected, lookup target.fields name = some expected) ∧
  (∀ name expected, lookup target.fields name = some expected →
    ∃ actual, lookup source.fields name = some actual ∧ relation actual expected)

/-- The executable shape test enforces exact closure without depending on ordering. -/
theorem shape_sound [DecidableEq Key] (source target : Row Key Field)
    (accepted : shape source target = true) (closed : target.closed = true) :
    source.closed = true ∧ ∀ name type, lookup source.fields name = some type →
      ∃ expected, lookup target.fields name = some expected := by
  simp only [shape, closed, Bool.not_true, Bool.false_or, Bool.and_eq_true] at accepted
  refine ⟨accepted.1, ?_⟩
  intro name type found
  have present := List.all_eq_true.mp accepted.2 (name, type) (lookup_mem _ _ _ found)
  cases h : lookup target.fields name with
  | none => simp [h] at present
  | some expected => exact ⟨expected, rfl⟩

/-- Row checking is sound whenever the reused field checker is sound. Nested
Function/row semantics are obligations of that supplied relation, not procedure?. -/
theorem check_sound [DecidableEq Key] (test : Field → Field → Bool) (relation : Field → Field → Prop)
    (sound : ∀ a b, test a b = true → relation a b) (source target : Row Key Field)
    (accepted : check test source target = true) : Replaces relation source target := by
  simp only [check, Bool.and_eq_true] at accepted
  refine ⟨shape_sound source target accepted.1, ?_⟩
  intro name expected found
  have valid := List.all_eq_true.mp accepted.2 (name, expected) (lookup_mem _ _ _ found)
  cases h : lookup source.fields name with
  | none => simp [h] at valid
  | some actual => exact ⟨actual, rfl, sound _ _ (by simpa [h] using valid)⟩

/-- Observation semantics separates required reads from closed-key restrictions. -/
def Admits [DecidableEq Key] (accepts : Field → Value → Prop) (row : Row Key Field)
    (observe : Key → Option Value) : Prop :=
  (∀ name type, lookup row.fields name = some type →
    ∃ value, observe name = some value ∧ accepts type value) ∧
  (row.closed = true → ∀ name value, observe name = some value →
    ∃ type, lookup row.fields name = some type)

/-- A source value can replace the target under explicit field-behavior inclusion.
No field write, authorization reuse, or identity-preserving normalization follows. -/
theorem replacement [DecidableEq Key] (accepts : Field → Value → Prop)
    (relation : Field → Field → Prop)
    (sound : ∀ a b, relation a b → ∀ value, accepts a value → accepts b value)
    (source target : Row Key Field) (replaces : Replaces relation source target)
    (observe : Key → Option Value) (valid : Admits accepts source observe) :
    Admits accepts target observe := by
  constructor
  · intro name expected found
    obtain ⟨actual, present, included⟩ := replaces.2 name expected found
    obtain ⟨value, observation, admitted⟩ := valid.1 name actual present
    exact ⟨value, observation, sound _ _ included _ admitted⟩
  · intro closed name value observed
    have sourceClosed := (replaces.1 closed).1
    obtain ⟨actual, present⟩ := valid.2 sourceClosed name value observed
    exact (replaces.1 closed).2 name actual present

/-- Explicit row extension copies named fields and retains the extension's tail. -/
def splice [DecidableEq Key] (explicit extension : Row Key Field) : Except Unit (Row Key Field) :=
  if explicit.fields.all (fun field => (lookup extension.fields field.1).isNone) then
    .ok ⟨explicit.fields ++ extension.fields, extension.closed⟩ else .error ()

/-- Existing explicit fields are never silently overridden during row substitution. -/
theorem splice_disjoint [DecidableEq Key] (explicit extension result : Row Key Field)
    (accepted : splice explicit extension = .ok result) (name type)
    (present : (name, type) ∈ explicit.fields) : lookup extension.fields name = none := by
  unfold splice at accepted
  split at accepted
  next disjoint =>
    have absent := List.all_eq_true.mp disjoint (name, type) present
    cases h : lookup extension.fields name <;> simp_all
  next => contradiction

/-- Successful row splicing retains both field order and the extension's tail. -/
theorem splice_result [DecidableEq Key] (explicit extension result : Row Key Field)
    (accepted : splice explicit extension = .ok result) :
    result.fields = explicit.fields ++ extension.fields ∧ result.closed = extension.closed := by
  unfold splice at accepted
  split at accepted
  · cases Except.ok.inj accepted
    exact ⟨rfl, rfl⟩
  · contradiction

/-- Named lookup through a persistent extension preserves the explicit prefix. -/
theorem lookup_append [DecidableEq Key] (front back : List (Key × Field)) (name : Key) :
    lookup (front ++ back) name = (lookup front name).orElse (fun _ => lookup back name) := by
  induction front with
  | nil => rfl
  | cons field rest ih =>
    rcases field with ⟨key, type⟩
    by_cases same : key = name <;> simp [lookup, same, ih]

/-- Row substitution cannot change an explicit field, even when its label has the
same spelling as a type variable. Labels are not substitution expressions. -/
theorem splice_preserves [DecidableEq Key] (explicit extension result : Row Key Field)
    (accepted : splice explicit extension = .ok result) (name type)
    (found : lookup explicit.fields name = some type) : lookup result.fields name = some type := by
  rw [(splice_result _ _ _ accepted).1, lookup_append, found]
  rfl

/-- Ill-kinded/overlapping candidate assignments are filtered with constraints;
resource errors are outside this total Boolean predicate and cannot mean false. -/
def assignmentValid (wellFormed constraints : Assignment → Bool) (assignment : Assignment) : Bool :=
  wellFormed assignment && constraints assignment

/-- Reuse the existing complete finite solver: a unique instance is both well
formed after row substitution and satisfies every supplied declaration constraint. -/
theorem inferred_valid (wellFormed constraints : Assignment → Bool) (candidates : List Assignment)
    (accepted : PrototypeTypes.infer (assignmentValid wellFormed constraints) candidates = .unique assignment) :
    assignment ∈ candidates ∧ wellFormed assignment = true ∧ constraints assignment = true := by
  obtain ⟨member, good⟩ := PrototypeTypes.infer_unique _ _ accepted
  exact ⟨member, by simpa [assignmentValid] using good⟩
end LeanPoo.Functional.RowTypes
