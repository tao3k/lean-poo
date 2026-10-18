import LeanPoo.Functional.ObjectContractValidation

/-! Finite effective Slot validation and checked Class initialization. Resolution
of inherited metadata and provision of prototype defaults are supplied by the
existing Class construction. These laws do not certify C3, host mutation,
computed-slot rebinding, identity, or arbitrary recursive termination. -/
namespace LeanPoo.Functional.ClassValidation

/-- A selected Slot owns required/optional presence, its child normalizer and
constant equality. The predicate represents the host's supplied equality policy. -/
structure Slot (Value Error : Type) where
  optional : Bool
  constant : Value → Bool
  check : Value → Except Error Value

/-- Absence bypasses the child; present constants must hold before and after
normalization. Wrapping a constant function may fail this exact equality gate. -/
def normalize (slot : Slot Value Error) (missing invalid : Error)
    (source : Option Value) : Except Error (Option Value) :=
  match source with
  | none => if slot.optional then .ok none else .error missing
  | some value =>
    if slot.constant value then (slot.check value).bind fun checked =>
      if slot.constant checked then .ok (some checked) else .error invalid
    else .error invalid

/-- Optional absence neither looks up a child nor invents a default value. -/
theorem optional_absent (slot : Slot Value Error) (missing invalid : Error)
    (optional : slot.optional = true) : normalize slot missing invalid none = .ok none := by
  simp [normalize, optional]

/-- Required absence fails even if the child could otherwise create a value. -/
theorem required_absent (slot : Slot Value Error) (missing invalid : Error)
    (required : slot.optional = false) : normalize slot missing invalid none = .error missing := by
  simp [normalize, required]

/-- An original constant mismatch suppresses child normalization. -/
theorem raw_constant_error (slot : Slot Value Error) (missing invalid : Error) (source : Value)
    (mismatch : slot.constant source = false) :
    normalize slot missing invalid (some source) = .error invalid := by
  simp [normalize, mismatch]

/-- Present child errors preserve their exact cause. -/
theorem child_error (slot : Slot Value Error) (missing invalid cause : Error) (source : Value)
    (before : slot.constant source = true) (failed : slot.check source = .error cause) :
    normalize slot missing invalid (some source) = .error cause := by
  simp [normalize, before, failed, Except.bind]

/-- Replacing a constant by a different wrapper cannot silently weaken equality. -/
theorem checked_constant_error (slot : Slot Value Error) (missing invalid : Error) (source checked : Value)
    (before : slot.constant source = true) (called : slot.check source = .ok checked)
    (after : slot.constant checked = false) :
    normalize slot missing invalid (some source) = .error invalid := by
  simp [normalize, before, called, after, Except.bind]

/-- Successful present normalization installs the actual checked child. -/
theorem present_success (slot : Slot Value Error) (missing invalid : Error) (source checked : Value)
    (before : slot.constant source = true) (called : slot.check source = .ok checked)
    (after : slot.constant checked = true) :
    normalize slot missing invalid (some source) = .ok (some checked) := by
  simp [normalize, before, called, after, Except.bind]

/-- Ordered effective metadata prefers the child's selected override. Parent
linearization is an input; this lookup law does not implement or prove C3. -/
def resolve [DecidableEq Key] (name : Key) : List (Key × Spec) → Option Spec
  | [] => none
  | (key, spec) :: rest => if name = key then some spec else resolve name rest

/-- A child's override governs even after the parent descriptor was observed. -/
theorem override_selected [DecidableEq Key] (key : Key) (child : Spec) (parents : List (Key × Spec)) :
    resolve key ((key, child) :: parents) = some child := by simp [resolve]

/-- Unrelated local fields preserve the supplied inherited selection. -/
theorem inherited_selected [DecidableEq Key] (key other : Key) (spec : Spec) (parents : List (Key × Spec))
    (different : key ≠ other) : resolve key ((other, spec) :: parents) = resolve key parents := by
  simp [resolve, different]

/-- Checked initialization validates defaults/overrides, invokes the optional
hook with that checked instance, then revalidates every returned instance. There
is deliberately no identity shortcut after a possibly mutating host hook. -/
def instantiate (validate : Carrier → Except Error Carrier)
    (hook : Option (Carrier → Except Error Carrier)) (source : Carrier) : Except Error Carrier :=
  (validate source).bind fun checked =>
    match hook with
    | none => .ok checked
    | some applyHook => (applyHook checked).bind validate

/-- Initial validation failure prevents hooks and preserves the first error. -/
theorem initial_error (validate : Carrier → Except Error Carrier)
    (hook : Option (Carrier → Except Error Carrier)) (source : Carrier) (cause : Error)
    (failed : validate source = .error cause) : instantiate validate hook source = .error cause := by
  simp [instantiate, failed, Except.bind]

/-- Without a hook initialization is exactly ordinary validation. -/
theorem no_hook (validate : Carrier → Except Error Carrier) (source : Carrier) :
    instantiate validate none source = validate source := by
  cases h : validate source <;> simp [instantiate, h, Except.bind]

/-- The hook observes the normalized instance and its replacement is rechecked. -/
theorem hook_sequence (validate : Carrier → Except Error Carrier)
    (hook : Carrier → Except Error Carrier) (source checked replacement : Carrier)
    (first : validate source = .ok checked) (called : hook checked = .ok replacement) :
    instantiate validate (some hook) source = validate replacement := by
  simp [instantiate, first, called, Except.bind]

/-- Hook failure cannot expose an initialized result. Effect rollback is outside
this pure equation; the caller owns its publication/state boundary. -/
theorem hook_error (validate : Carrier → Except Error Carrier)
    (hook : Carrier → Except Error Carrier) (source checked : Carrier) (cause : Error)
    (first : validate source = .ok checked) (failed : hook checked = .error cause) :
    instantiate validate (some hook) source = .error cause := by
  simp [instantiate, first, failed, Except.bind]

/-- Successful hooked construction has a final validation on the actual returned
instance, even when the hook returns the same host reference. -/
theorem initialized_final (validate : Carrier → Except Error Carrier)
    (hook : Carrier → Except Error Carrier) (source result : Carrier)
    (success : instantiate validate (some hook) source = .ok result) :
    ∃ checked replacement, validate source = .ok checked ∧ hook checked = .ok replacement ∧
      validate replacement = .ok result := by
  cases first : validate source with
  | error cause => simp [instantiate, first, Except.bind] at success
  | ok checked =>
    cases called : hook checked with
    | error cause => simp [instantiate, first, called, Except.bind] at success
    | ok replacement => exact ⟨checked, replacement, rfl, called,
        by simpa [instantiate, first, called, Except.bind] using success⟩

/-- Combining initialization with the existing finite object validator forces
final Class/Slot membership on the returned instance. -/
theorem initialized_membership (shape : Carrier → Except Error Unit)
    (fields : Carrier → Except Error Carrier) (final : Carrier → Except Error Unit)
    (hook : Carrier → Except Error Carrier) (source result : Carrier)
    (success : instantiate (ObjectContract.validateObject shape fields final) (some hook) source = .ok result) :
    final result = .ok () := by
  obtain ⟨_, replacement, _, _, validated⟩ := initialized_final _ _ _ _ success
  exact ((ObjectContract.validateObject_success shape fields final replacement result).mp validated).2.2

/-- Refinement after initialization retains both inherited contract obligations
and the added service relation on the exact final returned record. -/
theorem initialized_refinement [DecidableEq Key]
    (contract : ObjectContract.Contract Carrier Key Value Detail)
    (additional : Carrier → List Key → List (ObjectContract.Issue Key Detail)) (path : List Key)
    (shape : Carrier → Except (List (ObjectContract.Issue Key Detail)) Unit)
    (fields : Carrier → Except (List (ObjectContract.Issue Key Detail)) Carrier)
    (hook : Carrier → Except (List (ObjectContract.Issue Key Detail)) Carrier) (source result : Carrier)
    (success : instantiate (ObjectContract.validateObject shape fields
      (ObjectContract.reportGate (fun value => ObjectContract.diagnose
        (ObjectContract.refine contract additional) value path))) (some hook) source = .ok result) :
    ObjectContract.diagnose contract result path = [] ∧ additional result path = [] := by
  have final := initialized_membership _ _ _ hook source result success
  have empty : ObjectContract.diagnose (ObjectContract.refine contract additional) result path = [] := by
    cases h : ObjectContract.diagnose (ObjectContract.refine contract additional) result path <;>
      simp_all [ObjectContract.reportGate]
  exact (ObjectContract.refine_accepts_iff contract additional result path).mp empty


/-- Finite record Types describe presence separately from the child Type.
The schema is explicit: defaults, computed fields, hooks and C3 are host policies. -/
structure RecordType (Key Field : Type) where
  fields : List (Key × Field × Bool)
  closed : Bool
  deriving Repr

/-- Exact ordered field matching is deliberately conservative. Required source
fields may replace optional targets; optional sources cannot promise presence. -/
def recordFieldsCheck [DecidableEq Key] (test : Field → Field → Bool) :
    List (Key × Field × Bool) → List (Key × Field × Bool) → Bool
  | [], [] => true
  | (key, type, optional) :: rest, (key', type', optional') :: rest' =>
      decide (key = key') && (!optional || optional') && test type type' && recordFieldsCheck test rest rest'
  | _, _ => false

/-- Sealed targets require a sealed source. This does not grant mutable writes. -/
def recordCheck [DecidableEq Key] (test : Field → Field → Bool)
    (source target : RecordType Key Field) : Bool :=
  (!target.closed || source.closed) && recordFieldsCheck test source.fields target.fields

/-- The declarative relation retains exact names and presence obligations. -/
def RecordFieldsReplace (relation : Field → Field → Prop) :
    List (Key × Field × Bool) → List (Key × Field × Bool) → Prop
  | [], [] => True
  | source :: rest, target :: rest' => source.1 = target.1 ∧
      (source.2.2 = true → target.2.2 = true) ∧ relation source.2.1 target.2.1 ∧
      RecordFieldsReplace relation rest rest'
  | _, _ => False

/-- Every finite field comparison has the stated declarative derivation. -/
theorem recordFieldsCheck_sound [DecidableEq Key] (test : Field → Field → Bool)
    (relation : Field → Field → Prop) (sound : ∀ a b, test a b = true → relation a b)
    (source target : List (Key × Field × Bool))
    (accepted : recordFieldsCheck test source target = true) : RecordFieldsReplace relation source target := by
  induction source generalizing target with
  | nil => cases target with
    | nil => trivial
    | cons head rest => simp [recordFieldsCheck] at accepted
  | cons head rest ih =>
    cases target with
    | nil => simp [recordFieldsCheck] at accepted
    | cons head' rest' =>
      rcases head with ⟨key, type, optional⟩
      rcases head' with ⟨key', type', optional'⟩
      have parts : ((key = key' ∧ (!optional || optional') = true) ∧ test type type' = true) ∧
          recordFieldsCheck test rest rest' = true := by
        simpa only [recordFieldsCheck, Bool.and_eq_true, decide_eq_true_eq] using accepted
      refine ⟨parts.1.1.1, ?_, sound _ _ parts.1.2, ih rest' parts.2⟩
      intro absent
      change optional = true at absent
      simpa [absent] using parts.1.1.2

/-- Success simultaneously preserves sealedness and all field laws. -/
theorem recordCheck_sound [DecidableEq Key] (test : Field → Field → Bool)
    (relation : Field → Field → Prop) (sound : ∀ a b, test a b = true → relation a b)
    (source target : RecordType Key Field) (accepted : recordCheck test source target = true) :
    (target.closed = true → source.closed = true) ∧ RecordFieldsReplace relation source.fields target.fields := by
  have both : (!target.closed || source.closed) = true ∧ recordFieldsCheck test source.fields target.fields = true := by
    simpa only [recordCheck, Bool.and_eq_true] using accepted
  exact ⟨fun closed => by simpa [closed] using both.1,
    recordFieldsCheck_sound test relation sound _ _ both.2⟩

/-- Optional absence is an observation, never a request to invent a default. -/
def slotAdmits (accepts : Field → Value → Prop) (type : Field) (optional : Bool) : Option Value → Prop
  | none => optional = true
  | some value => accepts type value

/-- Read replacement composes field behavior with required/optional presence. -/
theorem slot_replacement (accepts : Field → Value → Prop) (source target : Field)
    (optional optional' : Bool) (presence : optional = true → optional' = true)
    (included : ∀ value, accepts source value → accepts target value) (observe : Option Value)
    (valid : slotAdmits accepts source optional observe) : slotAdmits accepts target optional' observe := by
  cases observe with
  | none => exact presence valid
  | some value => exact included value valid

/-- A finite normalized field snapshot retains exact position count. These are
observed values, not an initialization algorithm or an inferred default source. -/
def recordValuesAdmit (accepts : Field → Value → Prop) :
    List (Key × Field × Bool) → List (Option Value) → Prop
  | [], [] => True
  | field :: rest, value :: values => slotAdmits accepts field.2.1 field.2.2 value ∧
      recordValuesAdmit accepts rest values
  | _, _ => False

/-- Accepted record fields reuse the SAME observed snapshot, including absence.
Behavioral inclusion is a supplied Type interpretation premise. The source and
result are not claimed to share mutable identity or arbitrary host callbacks. -/
theorem record_field_replacement [DecidableEq Key] (test : Field → Field → Bool)
    (relation : Field → Field → Prop) (sound : ∀ a b, test a b = true → relation a b)
    (accepts : Field → Value → Prop)
    (behavior : ∀ a b, relation a b → ∀ value, accepts a value → accepts b value)
    (source target : List (Key × Field × Bool)) (accepted : recordFieldsCheck test source target = true)
    (observed : List (Option Value)) (valid : recordValuesAdmit accepts source observed) :
    recordValuesAdmit accepts target observed := by
  have derived := recordFieldsCheck_sound test relation sound source target accepted
  clear accepted
  induction source generalizing target observed with
  | nil => cases target <;> cases observed <;> simp_all [recordValuesAdmit, RecordFieldsReplace]
  | cons head rest ih =>
    cases target with
    | nil => simp [RecordFieldsReplace] at derived
    | cons head' rest' =>
      cases observed with
      | nil => simp [recordValuesAdmit] at valid
      | cons value values =>
        exact ⟨slot_replacement accepts _ _ _ _ derived.2.1 (behavior _ _ derived.2.2.1) value valid.1,
          ih rest' values valid.2 derived.2.2.2⟩

end LeanPoo.Functional.ClassValidation
