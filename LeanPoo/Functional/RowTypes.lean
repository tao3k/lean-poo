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

/-- Only optional presence and a positive empty-child witness prove absence.
An empty collection, sentinel or failed witness is not evidence of no value. -/
def absentField (empty : Field → Bool) (field : Field × Bool) : Bool := field.2 && empty field.1

/-- Closed targets may forget only source keys proved absent. Runtime keys and
original declaration order remain unchanged; open sources still cannot close. -/
def recordShape [DecidableEq Key] (empty : Field → Bool) (source target : Row Key (Field × Bool)) : Bool :=
  !target.closed || (source.closed && source.fields.all fun field =>
    (lookup target.fields field.1).isSome || absentField empty field.2)

/-- Required target fields still require required sources. An optional source
proved absent needs no child replacement, since neither child can be demanded. -/
def recordFieldCheck [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (source : Row Key (Field × Bool)) (name : Key) (expected : Field × Bool) : Bool :=
  match lookup source.fields name with
  | none => source.closed && expected.2
  | some actual => (!actual.2 || expected.2) && (absentField empty actual || test actual.1 expected.1)

/-- One complete named check combines closure, proved absence and child inclusion.
The witness is explicit; no implicit predicate or arbitrary callback is queried. -/
def recordCheck [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (source target : Row Key (Field × Bool)) : Bool :=
  recordShape empty source target && target.fields.all fun field => recordFieldCheck test empty source field.1 field.2

/-- Named read replacement retains presence, closure and the original fields.
Any forgotten key or bypassed child needs explicit positive absence evidence. -/
def RecordReplaces [DecidableEq Key] (relation : Field → Field → Prop) (empty : Field → Bool)
    (source target : Row Key (Field × Bool)) : Prop :=
  (target.closed = true → source.closed = true ∧
    ∀ name type, lookup source.fields name = some type →
      (∃ expected, lookup target.fields name = some expected) ∨ absentField empty type = true) ∧
  (∀ name expected, lookup target.fields name = some expected →
    match lookup source.fields name with
    | none => source.closed = true ∧ expected.2 = true
    | some actual => (actual.2 = true → expected.2 = true) ∧
      (absentField empty actual = true ∨ relation actual.1 expected.1))

/-- Successful shape checks retain a target key or its exact absence witness. -/
theorem recordShape_sound [DecidableEq Key] (empty : Field → Bool) (source target : Row Key (Field × Bool))
    (accepted : recordShape empty source target = true) (closed : target.closed = true) :
    source.closed = true ∧ ∀ name type, lookup source.fields name = some type →
      (∃ expected, lookup target.fields name = some expected) ∨ absentField empty type = true := by
  simp only [recordShape, closed, Bool.not_true, Bool.false_or, Bool.and_eq_true] at accepted
  refine ⟨accepted.1, ?_⟩
  intro name type found
  have good := List.all_eq_true.mp accepted.2 (name, type) (lookup_mem _ _ _ found)
  simp only [Bool.or_eq_true] at good
  rcases good with present | absent
  · cases h : lookup target.fields name with
    | none => simp [h] at present
    | some expected => exact .inl ⟨expected, rfl⟩
  · exact .inr absent

/-- All Boolean branch obligations become one declarative named relation. This
requires only child derivation; semantic witness soundness is used at observation. -/
theorem recordCheck_derives [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (relation : Field → Field → Prop) (sound : ∀ a b, test a b = true → relation a b)
    (source target : Row Key (Field × Bool)) (accepted : recordCheck test empty source target = true) :
    RecordReplaces relation empty source target := by
  simp only [recordCheck, Bool.and_eq_true] at accepted
  refine ⟨recordShape_sound empty source target accepted.1, ?_⟩
  intro name expected found
  have good := List.all_eq_true.mp accepted.2 (name, expected) (lookup_mem _ _ _ found)
  cases h : lookup source.fields name with
  | none => simpa [recordFieldCheck, h] using good
  | some actual =>
    simp only [recordFieldCheck, h, Bool.and_eq_true, Bool.or_eq_true] at good
    refine ⟨?_, good.2.imp_right (sound _ _)⟩
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

/-- A sound empty-child witness forces the actual Slot observation to be absent,
not merely optional. It grants no accepted value to an impossible child Type. -/
theorem absentField_observe (empty : Field → Bool) (accepts : Field → Value → Prop)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (field : Field × Bool) (observe : Option Value)
    (absent : absentField empty field = true) (valid : slotAdmits accepts field.1 field.2 observe) : observe = none := by
  have parts : field.2 = true ∧ empty field.1 = true := by simpa [absentField, Bool.and_eq_true] using absent
  have impossible := parts.2
  cases observed : observe with
  | none => rfl
  | some value => exact False.elim (emptySound field.1 impossible value (by simpa [slotAdmits, observed] using valid))

/-- Named observations reuse the same Slot predicate as Class snapshots. Closed
rows exclude undeclared observations; no mutable-write relation is introduced. -/
def RecordAdmits [DecidableEq Key] (accepts : Field → Value → Prop)
    (row : Row Key (Field × Bool)) (observe : Key → Option Value) : Prop :=
  (∀ name field, lookup row.fields name = some field → slotAdmits accepts field.1 field.2 (observe name)) ∧
  (row.closed = true → ∀ name value, observe name = some value → ∃ field, lookup row.fields name = some field)

/-- Read replacement uses the actual absence observation to forget a field or
bypass its child, while retaining required reads and closed-source guarantees. -/
theorem record_replacement [DecidableEq Key] (accepts : Field → Value → Prop)
    (relation : Field → Field → Prop) (empty : Field → Bool)
    (sound : ∀ a b, relation a b → ∀ value, accepts a value → accepts b value)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (source target : Row Key (Field × Bool)) (replaces : RecordReplaces relation empty source target)
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
      rcases good.2 with absent | included
      · have missing := absentField_observe empty accepts emptySound actual (observe name) absent (valid.1 name actual h)
        have optional : actual.2 = true := (by simpa [absentField, Bool.and_eq_true] using absent : actual.2 = true ∧ empty actual.1 = true).1
        simpa [slotAdmits, missing] using good.1 optional
      · exact slot_replacement accepts actual.1 expected.1 actual.2 expected.2 good.1
          (sound _ _ included) (observe name) (valid.1 name actual h)
  · intro closed name value observed
    have constraints := replaces.1 closed
    obtain ⟨actual, present⟩ := valid.2 constraints.1 name value observed
    rcases constraints.2 name actual present with declared | absent
    · exact declared
    · have missing := absentField_observe empty accepts emptySound actual (observe name) absent (valid.1 name actual present)
      simp [observed] at missing

/-- Both supplied laws are explicit: child inclusion and positive emptiness.
A failed emptiness check never authorizes field erasure or target admission. -/
theorem recordCheck_sound [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (source target : Row Key (Field × Bool)) (checked : recordCheck test empty source target = true)
    (observe : Key → Option Value) (valid : RecordAdmits accepts source observe) : RecordAdmits accepts target observe :=
  record_replacement accepts (fun a b => test a b = true) empty sound emptySound source target
    (recordCheck_derives test empty _ (fun _ _ h => h) source target checked) observe valid

/-- A missing target name still needs both closed-source and optional-target evidence. -/
theorem recordFieldCheck_missing [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (source : Row Key (Field × Bool)) (name : Key) (expected : Field × Bool)
    (missing : lookup source.fields name = none)
    (accepted : recordFieldCheck test empty source name expected = true) : source.closed = true ∧ expected.2 = true := by
  simpa [recordFieldCheck, missing] using accepted

/-- Complete finite inference retains universal target observations and candidate
provenance, using the same absence-aware row checker as declaration publication. -/
theorem inferred_record_sound [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (layout : Assignment → Row Key (Field × Bool)) (target : Row Key (Field × Bool)) (candidates : List Assignment)
    (inferred : PrototypeTypes.infer (fun a => recordCheck test empty (layout a) target) candidates = .unique assignment)
    (observe : Key → Option Value) (valid : RecordAdmits accepts (layout assignment) observe) :
    assignment ∈ candidates ∧ RecordAdmits accepts target observe := by
  have accepted := PrototypeTypes.infer_unique _ _ inferred
  exact ⟨accepted.1, recordCheck_sound test empty accepts sound emptySound _ _ accepted.2 observe valid⟩

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

/-- Object fields have required presence. This private observation view adds
flags without changing keys, field Types, ordering, closure or runtime values. -/
def requiredRow (row : Row Key Field) : Row Key (Field × Bool) :=
  ⟨row.fields.map (fun field => (field.1, (field.2, false))), row.closed⟩

/-- Presence projection retains the very same named lookup and selected Type. -/
theorem lookup_required [DecidableEq Key] (fields : List (Key × Field)) (name : Key) :
    lookup (fields.map (fun field => (field.1, (field.2, false)))) name =
      (lookup fields name).map (fun type => (type, false)) := by
  induction fields with
  | nil => rfl
  | cons head rest ih =>
    rcases head with ⟨key, type⟩
    by_cases same : key = name <;> simp [lookup, same, ih]

/-- Required-field Object observations and required Slot observations agree on
both successful reads and closed-key restrictions. No normalization is inferred. -/
theorem requiredRow_admits [DecidableEq Key] (accepts : Field → Value → Prop)
    (row : Row Key Field) (observe : Key → Option Value) :
    RecordAdmits accepts (requiredRow row) observe ↔ Admits accepts row observe := by
  constructor
  · rintro ⟨fields, closed⟩
    constructor
    · intro name type found
      have good := fields name (type, false) (by simp [requiredRow, lookup_required, found])
      cases observed : observe name with
      | none => simp [slotAdmits, observed] at good
      | some value => exact ⟨value, rfl, by simpa [slotAdmits, observed] using good⟩
    · intro isClosed name value observed
      obtain ⟨field, found⟩ := closed isClosed name value observed
      cases original : lookup row.fields name with
      | none => simp [requiredRow, lookup_required, original] at found
      | some type => exact ⟨type, rfl⟩
  · rintro ⟨fields, closed⟩
    constructor
    · intro name field found
      cases original : lookup row.fields name with
      | none => simp [requiredRow, lookup_required, original] at found
      | some type =>
        have same : (type, false) = field := by simpa [requiredRow, lookup_required, original] using found
        subst field
        obtain ⟨value, observed, valid⟩ := fields name type original
        simpa [slotAdmits, observed] using valid
    · intro isClosed name value observed
      obtain ⟨type, found⟩ := closed isClosed name value observed
      exact ⟨(type, false), by simp [requiredRow, lookup_required, found]⟩

/-- A finite Record replaces an Object interface through the existing complete
record checker. Required target reads cannot be supplied by optional fields. -/
theorem recordToObject_sound [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (source : Row Key (Field × Bool)) (target : Row Key Field)
    (checked : recordCheck test empty source (requiredRow target) = true)
    (observe : Key → Option Value) (valid : RecordAdmits accepts source observe) : Admits accepts target observe :=
  (requiredRow_admits accepts target observe).mp
    (recordCheck_sound test empty accepts sound emptySound source (requiredRow target) checked observe valid)

/-- A closed Object can establish absence of missing optional Record fields;
open sources retain the original refusal. No defaults or slots are fabricated. -/
theorem objectToRecord_sound [DecidableEq Key] (test : Field → Field → Bool) (empty : Field → Bool)
    (accepts : Field → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, accepts a value → accepts b value)
    (emptySound : ∀ field, empty field = true → ∀ value, ¬ accepts field value)
    (source : Row Key Field) (target : Row Key (Field × Bool))
    (checked : recordCheck test empty (requiredRow source) target = true)
    (observe : Key → Option Value) (valid : Admits accepts source observe) : RecordAdmits accepts target observe :=
  recordCheck_sound test empty accepts sound emptySound (requiredRow source) target checked observe
    ((requiredRow_admits accepts source observe).mpr valid)

end LeanPoo.Functional.RowTypes
