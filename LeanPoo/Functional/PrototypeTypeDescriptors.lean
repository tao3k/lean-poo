import LeanPoo.Functional.PrototypeTypes
import LeanPoo.Functional.MethodDeclarations

/-! Literal intrinsic descriptors extend the type-protocol future work. Carrier
identity is retained separately from interval observations; byte length is not
an integer value conversion. Host recognizers and serialization are premises. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- Existing runtime descriptor families, with immutable width metadata. -/
inductive Intrinsic where
  | null | emptyTuple | unit | bytes (length : Option Nat) | unsigned (bits : Nat) | signed (bits : Nat)
  | uint256 | jsInt | bytes32 | bytes64
  deriving Repr, DecidableEq
/-- Distinct value carriers prevent byte-length projections becoming integers. -/
inductive IntrinsicCarrier where
  | null | vector | unit | bytes | integer
  deriving Repr, DecidableEq
/-- Abstract observations preserve the empty-list/void distinction and byte length.
No mutable byte contents or descriptor callbacks enter a literal value cache. -/
inductive IntrinsicValue where
  | null | vector (length : Nat) | unit | bytes (length : Nat) | integer (value : Int)
  deriving Repr, DecidableEq
/-- Carrier identity is independent of any numeric/length inclusion proof. -/
def Intrinsic.carrier : Intrinsic → IntrinsicCarrier
  | .null => .null | .emptyTuple => .vector | .unit => .unit | .bytes _ | .bytes32 | .bytes64 => .bytes
  | .unsigned _ | .signed _ | .uint256 | .jsInt => .integer
/-- A singleton has observation zero; a vector carries its nonnegative length. -/
def IntrinsicValue.observation : IntrinsicValue → IntrinsicCarrier × Int
  | .null => (.null, 0) | .vector length => (.vector, length) | .unit => (.unit, 0)
  | .bytes length => (.bytes, length) | .integer value => (.integer, value)
/-- Unsigned width is an interval observation, not normalization/modular arithmetic. -/
def IntegerRange.forUnsigned (bits : Nat) : IntegerRange :=
  ⟨some 0, some ((2 : Int) ^ bits - 1)⟩
/-- Signed width includes the negative power endpoint and excludes positive overflow. -/
def IntegerRange.forSigned (bits : Nat) : IntegerRange :=
  ⟨some (-((2 : Int) ^ (bits - 1))), some ((2 : Int) ^ (bits - 1) - 1)⟩
/-- Exact inclusive bounds reuse the existing interval algebra. UIntN zero has
one integer, zero; IntN requires at least one bit at admission. -/
def Intrinsic.range : Intrinsic → IntegerRange
  | .null | .emptyTuple | .unit => ⟨some 0, some 0⟩
  | .bytes none => ⟨some 0, none⟩
  | .bytes (some length) => ⟨some length, some length⟩
  | .unsigned bits => .forUnsigned bits
  | .signed bits => .forSigned bits
  | .uint256 => .forUnsigned 256 | .jsInt => .forSigned 54
  | .bytes32 => ⟨some 32, some 32⟩ | .bytes64 => ⟨some 64, some 64⟩
/-- Decidable literal limits match Scheme admission before exponentiation or
cached descriptor construction. This is not a host allocator cost theorem. -/
def Intrinsic.admitted : Intrinsic → Bool
  | .null | .emptyTuple | .unit | .bytes none | .uint256 | .jsInt | .bytes32 | .bytes64 => true
  | .bytes (some length) => decide (length ≤ 65536)
  | .unsigned bits => decide (bits ≤ 4096)
  | .signed bits => decide (1 ≤ bits ∧ bits ≤ 4096)
/-- An accepted observation has both the correct carrier and exact interval. -/
def Intrinsic.Accepts (type : Intrinsic) (value : IntrinsicValue) : Prop :=
  value.observation.1 = type.carrier ∧ type.range.Contains value.observation.2
/-- Checked inclusion retains descriptor identity in the artifact, using only a
same-carrier interval view for the semantic judgment. No Any is introduced. -/
def intrinsicCheck (source target : Intrinsic) : Bool :=
  if source.admitted then if target.admitted then
    decide (source.carrier = target.carrier) && source.range.includes target.range
  else false else false
/-- Successful comparisons cannot bypass either side's literal admission. -/
theorem intrinsicCheck_admitted (source target)
    (accepted : intrinsicCheck source target = true) :
    source.admitted = true ∧ target.admitted = true := by
  unfold intrinsicCheck at accepted
  split at accepted
  · split at accepted
    · exact ⟨by assumption, by assumption⟩
    · contradiction
  · contradiction
/-- Universal observation inclusion follows from existing interval replacement;
no finite sampling, unchecked cross-carrier conversion or host inference is used. -/
theorem intrinsicCheck_sound (source target : Intrinsic)
    (accepted : intrinsicCheck source target = true) :
    ∀ value, source.Accepts value → target.Accepts value := by
  unfold intrinsicCheck at accepted
  split at accepted
  · split at accepted
    · simp only [Bool.and_eq_true] at accepted
      have same := of_decide_eq_true accepted.1
      intro value valid
      exact ⟨valid.1.trans same, IntegerRange.replacement _ _ accepted.2 _ valid.2⟩
    · contradiction
  · contradiction
/-- Replacement never changes the observed carrier even for equal numeric
projections. In particular BytesN 0 does not become Null or UIntN 0. -/
theorem intrinsicCheck_carrier (source target)
    (accepted : intrinsicCheck source target = true) : source.carrier = target.carrier := by
  unfold intrinsicCheck at accepted
  split at accepted
  · split at accepted
    · simp only [Bool.and_eq_true] at accepted
      exact of_decide_eq_true accepted.1
    · contradiction
  · contradiction
/-- Width aliases are observational views only, retaining source-kind identity
for invariant Map keys and exact declaration metadata. -/
def Intrinsic.numericView : Intrinsic → Option Ty
  | .unsigned bits => some (.integerRange (Intrinsic.unsigned bits).range)
  | .signed bits => some (.integerRange (Intrinsic.signed bits).range)
  | .uint256 => some (.integerRange Intrinsic.uint256.range)
  | .jsInt => some (.integerRange Intrinsic.jsInt.range)
  | _ => none
/-- Numeric observations of either width family use precisely the same interval
judgment as the existing inferred range protocol, with no normalization of data. -/
theorem numericView_exact (type : Intrinsic) (range : IntegerRange)
    (projected : type.numericView = some (.integerRange range))
    (value : Int) : type.Accepts (.integer value) ↔ range.Contains value := by
  cases type <;> simp [Intrinsic.numericView] at projected
  all_goals cases projected
  all_goals simp [Intrinsic.Accepts, IntrinsicValue.observation, Intrinsic.carrier]
/-- Required data/callback bounds share one captured assignment and builder. -/
def inferIntrinsic (input expected : Intrinsic) (candidates : List Intrinsic) :=
  LeanPoo.Functional.DeclarativeMetadata.inferDeclared candidates.length
    (fun output => intrinsicCheck output input && intrinsicCheck output expected)
    candidates (fun output => (Except.ok (input, output) : Except String (Intrinsic × Intrinsic)))
/-- Whole declaration completion preserves both original obligations and the
exact pair of descriptors. Equal interval views cannot substitute artifact kinds. -/
theorem inferIntrinsic_sound (input expected candidates output artifact)
    (published : inferIntrinsic input expected candidates = .ok (.unique output, some artifact)) :
    intrinsicCheck output input = true ∧ intrinsicCheck output expected = true ∧
      artifact = (input, output) := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique candidates.length
    (fun output => intrinsicCheck output input && intrinsicCheck output expected)
    candidates (fun output => (Except.ok (input, output) : Except String (Intrinsic × Intrinsic))) published
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.1, valid.2, (Except.ok.inj built).symm⟩

/-- Admission charges at least one work unit for each literal width, matching
Scheme's chunks of 64 before bounds arithmetic. Parser/search costs are separate. -/
def Intrinsic.metadataUnits : Intrinsic → Nat
  | .unsigned bits | .signed bits => max 1 ((bits + 63) / 64)
  | .bytes (some length) => max 1 ((length + 63) / 64)
  | .uint256 => 4 | .jsInt | .bytes32 | .bytes64 => 1
  | _ => 0
/-- Admitted width preparation is bounded independently of value enumeration. -/
theorem metadataUnits_bounded (type : Intrinsic) (admitted : type.admitted = true) :
    type.metadataUnits ≤ 1024 := by
  cases type <;> simp_all [Intrinsic.admitted, Intrinsic.metadataUnits]
  all_goals
    first
    | omega
    | split <;> simp_all <;> omega
/-- Maybe's void sentinel can satisfy its protocol without evaluating a payload.
This observation law grants no Function callback wrapping permission by itself. -/
theorem unit_optional (payload : Intrinsic) :
    IntrinsicValue.unit.observation.1 = IntrinsicCarrier.unit ∨ payload.Accepts .unit := .inl rfl

/-- The empty list and empty vector remain disjoint despite equal length zero. -/
theorem null_tuple_disjoint (value : IntrinsicValue) :
    ¬ (Intrinsic.null.Accepts value ∧ Intrinsic.emptyTuple.Accepts value) := by
  intro both
  have impossible := both.1.1.symm.trans both.2.1
  cases impossible

/-- Finite list spines retain the original head Types and a homogeneous tail.
This represents Null, List and Pair spines; vectors are a different carrier. -/
inductive ProperListShape (Key : Type) where
  | empty
  | elements (type : Key)
  | cons (head : Key) (tail : ProperListShape Key)
  deriving Repr, DecidableEq

/-- Membership uses the actual proper-list carrier, never tuple/vector length. -/
def ProperListShape.Accepts (member : Key → Value → Prop) : ProperListShape Key → List Value → Prop
  | .empty, values => values = []
  | .elements type, values => ∀ value ∈ values, member type value
  | .cons head tail, values => match values with
    | [] => False
    | value :: rest => member head value ∧ tail.Accepts member rest

/-- Structural inclusion checks every mandatory head and the entire remaining
tail using the original child relation; no top Type or sampled values are used. -/
def properListCheck (test : Key → Key → Bool) : ProperListShape Key → Key → Bool
  | .empty, _ => true
  | .elements type, target => test type target
  | .cons head tail, target => test head target && properListCheck test tail target

/-- Universal readable inclusion follows from child inclusion for every element.
The runtime projection into a proper-list spine is an explicit host premise. -/
theorem properListCheck_sound (test : Key → Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ a b, test a b = true → ∀ value, member a value → member b value)
    (shape : ProperListShape Key) (target : Key) (accepted : properListCheck test shape target = true) :
    ∀ values, shape.Accepts member values → ∀ value ∈ values, member target value := by
  induction shape with
  | empty =>
    intro values valid value present
    subst values
    simp at present
  | elements type =>
    intro values valid value present
    exact sound type target accepted value (valid value present)
  | cons head tail ih =>
    simp only [properListCheck, Bool.and_eq_true] at accepted
    intro values valid value present
    cases values with
    | nil => simp [ProperListShape.Accepts] at valid
    | cons first rest =>
      rcases valid with ⟨firstValid, restValid⟩
      rcases List.mem_cons.mp present with same | later
      · subst value
        exact sound head target accepted.1 first firstValid
      · exact ih accepted.2 rest restValid value later

/-- Existing complete declaration inference selects one original list shape.
Ambiguous/no-solution requests cannot enter the builder. -/
def inferProperList (test : Key → Key → Bool) (target : Key) (candidates : List (ProperListShape Key)) :=
  LeanPoo.Functional.DeclarativeMetadata.inferDeclared candidates.length
    (fun shape => properListCheck test shape target) candidates
    (fun shape => (Except.ok (target, shape) : Except String (Key × ProperListShape Key)))

/-- A completed declaration retains the exact checked shape and target, rather
than converting a list into a tuple or changing the original inferred artifact. -/
theorem inferProperList_sound (test : Key → Key → Bool) (target candidates shape artifact)
    (published : inferProperList test target candidates = .ok (.unique shape, some artifact)) :
    properListCheck test shape target = true ∧ artifact = (target, shape) := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique candidates.length
    (fun shape => properListCheck test shape target) candidates
    (fun shape => (Except.ok (target, shape) : Except String (Key × ProperListShape Key))) published
  exact ⟨valid, (Except.ok.inj built).symm⟩

/-- A finite empty-element witness gives a List exactly its empty-list value.
It never declares List itself empty, and never treats vectors as list spines. -/
def emptyListCheck (empty : Key → Bool) : ProperListShape Key → Bool
  | .empty => true
  | .elements type => empty type
  | .cons _ _ => false

/-- Successful empty-list admission implies readable inclusion in Null for all
values. Child emptiness is an explicit sound witness, not failed inhabitation. -/
theorem emptyListCheck_sound (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (shape : ProperListShape Key) (accepted : emptyListCheck empty shape = true) :
    ∀ values, shape.Accepts member values → values = [] := by
  cases shape with
  | empty => intro values valid; exact valid
  | elements type =>
    intro values valid
    cases values with
    | nil => rfl
    | cons first rest => exact False.elim (sound type accepted first (valid first (by simp)))
  | cons head tail => simp [emptyListCheck] at accepted

/-- The admitted list Type is inhabited by nil, even when no payload can exist.
This prevents confusing empty containers with empty Types in further reasoning. -/
theorem emptyListCheck_inhabited (empty : Key → Bool) (member : Key → Value → Prop)
    (shape : ProperListShape Key) (accepted : emptyListCheck empty shape = true) :
    shape.Accepts member [] := by
  cases shape with
  | empty => rfl
  | elements type => simp [ProperListShape.Accepts]
  | cons head tail => simp [emptyListCheck] at accepted

/-- Once a proper List has exactly nil, covering nil is necessary and sufficient
for universal readable replacement. This reuses the target's existing intrinsic
judgment, rather than dropping an inhabited container as if it were bottom. -/
theorem emptyListCheck_into_iff (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (shape : ProperListShape Key) (accepted : emptyListCheck empty shape = true)
    (target : List Value → Prop) :
    (∀ values, shape.Accepts member values → target values) ↔ target [] := by
  constructor
  · intro included
    exact included [] (emptyListCheck_inhabited empty member shape accepted)
  · intro covered values valid
    have onlyNil := emptyListCheck_sound empty member sound shape accepted values valid
    simpa [onlyNil] using covered

/-- Identity validation on nil preserves the exact source value and target
membership. No child validator runs on this carrier. A target with arbitrary
normalization effects cannot borrow the identity premise of the flat fragment. -/
theorem emptyListCheck_normalized (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (shape : ProperListShape Key) (accepted : emptyListCheck empty shape = true)
    (target : List Value → Prop) (covered : target [])
    (normalize : List Value → Except Error (List Value))
    (identityNil : normalize [] = .ok [])
    (values : List Value) (valid : shape.Accepts member values) :
    normalize values = .ok values ∧ target values := by
  have onlyNil := emptyListCheck_sound empty member sound shape accepted values valid
  subst values
  exact ⟨identityNil, covered⟩

/-- A Pair with an admitted empty-list tail has exactly one original head.
The theorem preserves its value and membership, without a vector conversion. -/
theorem singleton_tail (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (head : Key) (tail : ProperListShape Key) (accepted : emptyListCheck empty tail = true)
    (values : List Value) (valid : (ProperListShape.cons head tail).Accepts member values) :
    ∃ value, values = [value] ∧ member head value := by
  cases values with
  | nil => simp [ProperListShape.Accepts] at valid
  | cons first rest =>
    have onlyNil := emptyListCheck_sound empty member sound tail accepted rest valid.2
    exact ⟨first, by simp [onlyNil], valid.1⟩

/-- The existing complete declaration search preserves original empty-list shape
candidates, including genuinely ambiguous representations of the same value set. -/
def inferEmptyList (empty : Key → Bool) (candidates : List (ProperListShape Key)) :=
  LeanPoo.Functional.DeclarativeMetadata.inferDeclared candidates.length
    (emptyListCheck empty) candidates
    (fun shape => (Except.ok shape : Except String (ProperListShape Key)))

/-- Accepted inference keeps exact source metadata and universally rejects any
nonempty result under the original empty-element interpretation premise. -/
theorem inferEmptyList_sound (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (candidates : List (ProperListShape Key)) (shape artifact : ProperListShape Key)
    (published : inferEmptyList empty candidates = .ok (.unique shape, some artifact)) :
    artifact = shape ∧ (∀ values, shape.Accepts member values → values = []) := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique candidates.length
    (emptyListCheck empty) candidates
    (fun shape => (Except.ok shape : Except String (ProperListShape Key))) published
  exact ⟨(Except.ok.inj built).symm, emptyListCheck_sound empty member sound shape valid⟩

/-- Completed unique inference retains the original List artifact while the
existing target's nil judgment transfers every actual source value. Neither
equivalent candidate metadata nor ordered alternatives are canonicalized away. -/
theorem inferEmptyList_into (empty : Key → Bool) (member : Key → Value → Prop)
    (sound : ∀ key, empty key = true → ∀ value, ¬ member key value)
    (candidates : List (ProperListShape Key)) (shape artifact : ProperListShape Key)
    (published : inferEmptyList empty candidates = .ok (.unique shape, some artifact))
    (target : List Value → Prop) (covered : target []) :
    artifact = shape ∧ ∀ values, shape.Accepts member values → target values := by
  obtain ⟨original, onlyNil⟩ := inferEmptyList_sound empty member sound candidates shape artifact published
  refine ⟨original, ?_⟩
  intro values valid
  simpa [onlyNil values valid] using covered

/-- Intrinsic numeric families use host predicates, not prototype ancestry.
Integer intervals reuse the existing exact endpoint algebra. -/
inductive NumericFamily where
  | number | real | rational | float | integer (range : IntegerRange)
  deriving Repr, DecidableEq
/-- Observations distinguish exact integers, other exact rationals, finite/exceptional flonums and
nonreal numbers. IDs carry no arithmetic or floating-point correctness claim. -/
inductive NumericObservation where
  | integer (value : Int) | exactReal (id : Nat) | float (id : Nat)
  | exceptionalFloat (id : Nat) | nonreal (id : Nat) | other
  deriving Repr, DecidableEq
/-- Every observation retains its original value class; no cast is performed. -/
def NumericFamily.Accepts : NumericFamily → NumericObservation → Prop
  | .number, .other => False
  | .number, _ => True
  | .real, .integer _ | .real, .exactReal _ | .real, .float _ | .real, .exceptionalFloat _ => True
  | .rational, .integer _ | .rational, .exactReal _ | .rational, .float _ => True
  | .float, .float _ | .float, .exceptionalFloat _ => True
  | .integer range, .integer value => range.Contains value
  | _, _ => False
/-- The admitted numeric comparison is independent of mutable host descriptors.
Finite literal or ordered-Union lifting remains a separate existing obligation. -/
def numericFamilyCheck : NumericFamily → NumericFamily → Bool
  | _, .number => true
  | .real, .real | .rational, .real | .float, .real | .integer _, .real | .float, .float => true
  | .rational, .rational | .integer _, .rational => true
  | .integer source, .integer target => source.includes target
  | _, _ => false
/-- Accepted numeric replacement preserves every observation, including exact
rationals and nonreal numbers that cannot be identified with flonums. -/
theorem numericFamilyCheck_sound (source target : NumericFamily)
    (accepted : numericFamilyCheck source target = true) :
    ∀ value, source.Accepts value → target.Accepts value := by
  cases source <;> cases target <;> simp only [numericFamilyCheck] at accepted
  all_goals try contradiction
  all_goals intro value valid
  all_goals cases value <;> simp_all [NumericFamily.Accepts]
  exact IntegerRange.replacement _ _ accepted _ valid
/-- Numeric input contravariance and output covariance reuse the existing
universal arrow theorem; valid host behavior remains an explicit premise. -/
theorem numericFunction_replacement (sourceIn targetIn sourceOut targetOut : NumericFamily)
    (inputs : numericFamilyCheck targetIn sourceIn = true)
    (outputs : numericFamilyCheck sourceOut targetOut = true)
    (f : NumericObservation → NumericObservation)
    (behavior : ∀ v, sourceIn.Accepts v → sourceOut.Accepts (f v)) :
    ∀ v, targetIn.Accepts v → targetOut.Accepts (f v) :=
  function_replacement _ _ _ _ (numericFamilyCheck_sound _ _ inputs)
    (numericFamilyCheck_sound _ _ outputs) f behavior
/-- The existing complete finite declaration solver publishes original kinds;
source-specific numeric comparison never replaces the whole inference protocol. -/
def inferNumericFamily (input expected : NumericFamily) (candidates : List NumericFamily) :=
  LeanPoo.Functional.DeclarativeMetadata.inferDeclared candidates.length
    (fun output => numericFamilyCheck output input && numericFamilyCheck output expected)
    candidates (fun output => (Except.ok (input, output) : Except String (NumericFamily × NumericFamily)))
/-- A unique published numeric artifact satisfies every original bound, with
universal value inclusion supplied by the intrinsic numeric relation. -/
theorem inferNumericFamily_sound (input expected candidates output artifact)
    (published : inferNumericFamily input expected candidates = .ok (.unique output, some artifact)) :
    artifact = (input, output) ∧
      (∀ value, output.Accepts value → input.Accepts value) ∧
      (∀ value, output.Accepts value → expected.Accepts value) := by
  obtain ⟨_, valid, built⟩ := LeanPoo.Functional.DeclarativeMetadata.inferDeclared_unique candidates.length
    (fun output => numericFamilyCheck output input && numericFamilyCheck output expected)
    candidates (fun output => (Except.ok (input, output) : Except String (NumericFamily × NumericFamily))) published
  simp only [Bool.and_eq_true] at valid
  cases built
  exact ⟨rfl, numericFamilyCheck_sound _ _ valid.1, numericFamilyCheck_sound _ _ valid.2⟩

/-- Every Scheme real lies in Rational or Float; NaN/infinities take only the
Float branch. Host classification is a premise, not an arithmetic theorem. -/
theorem real_numeric_split (value : NumericObservation)
    (valid : NumericFamily.real.Accepts value) :
    NumericFamily.rational.Accepts value ∨ NumericFamily.float.Accepts value := by
  cases value <;> simp_all [NumericFamily.Accepts]
/-- Ordered finite numeric targets retain their original branches. Only Real
has this additional two-family decomposition; nothing is reordered or coerced. -/
def numericFamilyUnionCheck (source : NumericFamily) (targets : List NumericFamily) : Bool :=
  targets.any (numericFamilyCheck source) ||
    (decide (source = .real) && targets.any (numericFamilyCheck .rational) &&
      targets.any (numericFamilyCheck .float))
/-- A successful joint view covers every original real observation, including
exceptional flonums, with an actual member of the original target list. -/
theorem numericFamilyUnionCheck_sound (source targets)
    (accepted : numericFamilyUnionCheck source targets = true) :
    ∀ value, source.Accepts value → ∃ target ∈ targets, target.Accepts value := by
  simp only [numericFamilyUnionCheck, Bool.or_eq_true, Bool.and_eq_true] at accepted
  rcases accepted with direct | ⟨⟨sourceReal, rationals⟩, floats⟩
  · obtain ⟨target, member, valid⟩ := List.any_eq_true.mp direct
    exact fun value sourceValid => ⟨target, member, numericFamilyCheck_sound _ _ valid value sourceValid⟩
  · have sourceReal : source = .real := of_decide_eq_true sourceReal
    subst source
    obtain ⟨rationalTarget, rationalMember, rationalValid⟩ := List.any_eq_true.mp rationals
    obtain ⟨floatTarget, floatMember, floatValid⟩ := List.any_eq_true.mp floats
    intro value valid
    rcases real_numeric_split value valid with rational | float
    · exact ⟨rationalTarget, rationalMember, numericFamilyCheck_sound _ _ rationalValid value rational⟩
    · exact ⟨floatTarget, floatMember, numericFamilyCheck_sound _ _ floatValid value float⟩
/-- Existing Z/ descriptors recognize unsigned residues; the view never invokes
their modular normalization, arithmetic methods or byte encoders. -/
def residueRange (modulus : Nat) : IntegerRange := ⟨some 0, some (Int.ofNat modulus - 1)⟩
/-- Exact observational bounds coincide with the standard uint-below? contract. -/
theorem residueRange_exact (modulus : Nat) (value : Int) :
    (residueRange modulus).Contains value ↔ 0 ≤ value ∧ value < Int.ofNat modulus := by
  simp only [residueRange, IntegerRange.Contains]
  simp only [Option.some.injEq, forall_eq']
  omega
/-- Positive literal modulus admission has the same 4096-bit metadata ceiling
as the host parser. It is independent of the number of possible residues. -/
def residueAdmitted (modulus : Nat) : Prop := 0 < modulus ∧ Nat.log2 modulus + 1 ≤ 4096
/-- Charge metadata words, not inhabitants; host callback/GC costs are separate. -/
def residueMetadataUnits (modulus : Nat) : Nat := (Nat.log2 modulus + 64) / 64
/-- Accepted modulus metadata contributes at most 64 word visits in one parser
pass, even when enumerating its residues would be infeasible. -/
theorem residueMetadataUnits_bounded (modulus : Nat) (admitted : residueAdmitted modulus) :
    residueMetadataUnits modulus ≤ 64 := by
  simp only [residueMetadataUnits, residueAdmitted] at *
  omega

/-- For positive source moduli, readable residue inclusion is exactly endpoint
order. It neither asserts a ring homomorphism nor changes descriptor identity. -/
theorem residueRange_includes_iff (source target : Nat) (positive : 0 < source) :
    (residueRange source).includes (residueRange target) = true ↔ source ≤ target := by
  simp [residueRange, IntegerRange.includes, IntegerRange.empty]
  omega
/-- The existing interval judgment transfers every original residue unchanged.
Out-of-range integers require explicit producer conversion, not validation. -/
theorem residue_replacement (source target : Nat)
    (accepted : (residueRange source).includes (residueRange target) = true)
    (value : Int) (valid : 0 ≤ value ∧ value < Int.ofNat source) :
    0 ≤ value ∧ value < Int.ofNat target :=
  (residueRange_exact target value).mp
    (IntegerRange.replacement _ _ accepted value ((residueRange_exact source value).mpr valid))
/-- Complete unique publication and joint target coverage compose without a
second solver: the artifact retains the original input/output metadata, and
its result has a member of the original ordered target list for every value. -/
theorem inferNumericFamily_union (input expected candidates output artifact targets)
    (published : inferNumericFamily input expected candidates = .ok (.unique output, some artifact))
    (covered : numericFamilyUnionCheck expected targets = true) :
    artifact = (input, output) ∧ ∀ value, output.Accepts value →
      ∃ target ∈ targets, target.Accepts value := by
  obtain ⟨original, _, expectedValid⟩ := inferNumericFamily_sound _ _ _ _ _ published
  exact ⟨original, fun value valid => numericFamilyUnionCheck_sound _ _ covered value (expectedValid value valid)⟩

end LeanPoo.Functional.PrototypeTypes
