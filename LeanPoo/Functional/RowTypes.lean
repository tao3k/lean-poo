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

/-- The existing Class field representation is (child Type, optional flag).
Required target reads need required source fields. Missing optional targets need
closed-source evidence; an open row may hide an incompatible value at that name. -/
def recordFieldCheck [DecidableEq Key] (test : Field → Field → Bool)
    (source : Row Key (Field × Bool)) (name : Key) (expected : Field × Bool) : Bool :=
  match lookup source.fields name with
  | none => source.closed && expected.2
  | some actual => (!actual.2 || expected.2) && test actual.1 expected.1

/-- Records and Object rows reuse one closed-key shape. Runtime field order is
preserved; this check decides readable named coverage, not construction order. -/
def recordCheck [DecidableEq Key] (test : Field → Field → Bool)
    (source target : Row Key (Field × Bool)) : Bool :=
  shape source target && target.fields.all fun field => recordFieldCheck test source field.1 field.2

/-- Named record replacement retains sealedness, presence and child relations.
Unlike an ordered snapshot, a named view may forget/reorder readable fields. -/
def RecordReplaces [DecidableEq Key] (relation : Field → Field → Prop)
    (source target : Row Key (Field × Bool)) : Prop :=
  (target.closed = true → source.closed = true ∧
    ∀ name type, lookup source.fields name = some type → ∃ expected, lookup target.fields name = some expected) ∧
  (∀ name expected, lookup target.fields name = some expected →
    match lookup source.fields name with
    | none => source.closed = true ∧ expected.2 = true
    | some actual => (actual.2 = true → expected.2 = true) ∧ relation actual.1 expected.1)

/-- The executable check derives the complete named relation, reusing the same
shape soundness proof as Object rows and any supplied child relation checker. -/
theorem recordCheck_derives [DecidableEq Key] (test : Field → Field → Bool)
    (relation : Field → Field → Prop) (sound : ∀ a b, test a b = true → relation a b)
    (source target : Row Key (Field × Bool)) (accepted : recordCheck test source target = true) :
    RecordReplaces relation source target := by
  simp only [recordCheck, Bool.and_eq_true] at accepted
  refine ⟨shape_sound source target accepted.1, ?_⟩
  intro name expected found
  have good := List.all_eq_true.mp accepted.2 (name, expected) (lookup_mem _ _ _ found)
  cases h : lookup source.fields name with
  | none => simpa [recordFieldCheck, h] using good
  | some actual =>
    simp only [recordFieldCheck, h, Bool.and_eq_true] at good
    refine ⟨?_, sound _ _ good.2⟩
    intro optional
    simpa [optional] using good.1

/-- The common Slot observation law: optional absence invents no default. -/
def slotAdmits (accepts : Field → Value → Prop) (type : Field) (optional : Bool) : Option Value → Prop
  | none => optional = true
  | some value => accepts type value

/-- Presence and child behavior compose independently for a single observation. -/
theorem slot_replacement (accepts : Field → Value → Prop) (source target : Field)
    (optional optional' : Bool) (presence : optional = true → optional' = true)
    (included : ∀ value, accepts source value → accepts target value) (observe : Option Value)
    (valid : slotAdmits accepts source optional observe) : slotAdmits accepts target optional' observe := by
  cases observe with
  | none => exact presence valid
  | some value => exact included value valid

/-- Named observations reuse the same Slot predicate as Class snapshots. Closed
rows exclude undeclared observations; no mutable-write relation is introduced. -/
def RecordAdmits [DecidableEq Key] (accepts : Field → Value → Prop)
    (row : Row Key (Field × Bool)) (observe : Key → Option Value) : Prop :=
  (∀ name field, lookup row.fields name = some field → slotAdmits accepts field.1 field.2 (observe name)) ∧
  (row.closed = true → ∀ name value, observe name = some value →
    ∃ field, lookup row.fields name = some field)

/-- A named read view preserves all observations through the existing per-Slot
law. Missing optional targets are absent by closed-source evidence, never guessed. -/
theorem record_replacement [DecidableEq Key] (accepts : Field → Value → Prop)
    (relation : Field → Field → Prop)
    (sound : ∀ a b, relation a b → ∀ value, accepts a value → accepts b value)
    (source target : Row Key (Field × Bool)) (replaces : RecordReplaces relation source target)
    (observe : Key → Option Value) (valid : RecordAdmits accepts source observe) :
    RecordAdmits accepts target observe := by
  constructor
  · intro name expected found
    have good := replaces.2 name expected found
    cases h : lookup source.fields name with
    | none =>
      simp only [h] at good
      cases observed : observe name with
      | none => exact good.2
      | some value =>
        obtain ⟨actual, present⟩ := valid.2 good.1 name value observed
        simp [h] at present
    | some actual =>
      simp only [h] at good
      exact slot_replacement accepts actual.1 expected.1 actual.2 expected.2 good.1
        (sound _ _ good.2) (observe name) (valid.1 name actual h)
  · intro closed name value observed
    have constraints := replaces.1 closed
    obtain ⟨actual, present⟩ := valid.2 constraints.1 name value observed
    exact constraints.2 name actual present

/-- Checker soundness composes derivation with observation preservation. Child
Function interpretation remains a premise, not host procedure recognition. -/
theorem recordCheck_sound [DecidableEq Key] (test : Field → Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (source target : Row Key (Field × Bool)) (checked : recordCheck test source target = true)
    (observe : Key → Option Value) (valid : RecordAdmits accepts source observe) :
    RecordAdmits accepts target observe :=
  record_replacement accepts (fun a b => test a b = true) sound source target
    (recordCheck_derives test _ (fun _ _ h => h) source target checked) observe valid

/-- Absence evidence forces both closed-source and optional-target metadata. -/
theorem recordFieldCheck_missing [DecidableEq Key] (test : Field → Field → Bool)
    (source : Row Key (Field × Bool)) (name : Key) (expected : Field × Bool)
    (missing : lookup source.fields name = none)
    (accepted : recordFieldCheck test source name expected = true) :
    source.closed = true ∧ expected.2 = true := by
  simpa [recordFieldCheck, missing] using accepted

/-- Reuse complete finite inference: a unique assignment retains the named
record observation law, with no independent field solver or partial success. -/
theorem inferred_record_sound [DecidableEq Key] (test : Field → Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (layout : Assignment → Row Key (Field × Bool)) (target : Row Key (Field × Bool))
    (candidates : List Assignment)
    (inferred : PrototypeTypes.infer (fun a => recordCheck test (layout a) target) candidates = .unique assignment)
    (observe : Key → Option Value) (valid : RecordAdmits accepts (layout assignment) observe) :
    assignment ∈ candidates ∧ RecordAdmits accepts target observe := by
  have accepted := PrototypeTypes.infer_unique _ _ inferred
  exact ⟨accepted.1, recordCheck_sound test accepts sound _ _ accepted.2 observe valid⟩

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
