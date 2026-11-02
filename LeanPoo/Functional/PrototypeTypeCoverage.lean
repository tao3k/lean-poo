import LeanPoo.Functional.PrototypeTypeSyntax
import LeanPoo.Functional.VariantValidation

/-! Intrinsic finite and interval coverage for the existing prototype type algebra. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- The numeric interpretation covers only Integer, UInt and literal ranges;
other scalar families never acquire numeric conversion or fallback semantics. -/
def numericBounds : Ty → Option IntegerRange
  | .atom .integer => some IntegerRange.all
  | .atom .uint => some IntegerRange.unsigned
  | .integerRange range => some range
  | _ => none

/-- Pure integer observations of built-in flat Types; alternatives retain order.
Zero fuel refuses rather than claiming coverage of an unvisited subtree. -/
def integerAccepts : Nat → Ty → Int → Bool
  | 0, _, _ => false
  | fuel + 1, type, value => match type with
    | .integerRange range => range.lower.all (fun lower => decide (lower ≤ value)) &&
                            range.upper.all (fun upper => decide (value ≤ upper))
    | .integerEnum values => decide (value ∈ values)
    | .atom .integer => true
    | .atom .uint => decide (0 ≤ value)
    | .union branches => branches.any (fun branch => integerAccepts fuel branch value)
    | _ => false
/-- Ordered Option traversal projects all branches or refuses the entire tree.
A wrapper-bearing branch cannot be hidden behind an earlier numeric match. -/
def collectPieces (project : Ty → Option (List VariantValidation.Interval)) : List Ty → Option (List VariantValidation.Interval)
  | [] => some []
  | branch :: rest => match project branch, collectPieces project rest with
    | some first, some tail => some (first ++ tail)
    | _, _ => none
/-- Every projected piece retains a source branch; concatenation does not sort,
coalesce or rewrite the original declaration's alternative descriptors. -/
theorem collectPieces_origin (project : Ty → Option (List VariantValidation.Interval))
    (branches : List Ty) (pieces : List VariantValidation.Interval)
    (built : collectPieces project branches = some pieces) (piece : VariantValidation.Interval) (member : piece ∈ pieces) :
    ∃ branch ∈ branches, ∃ parts, project branch = some parts ∧ piece ∈ parts := by
  induction branches generalizing pieces with
  | nil => simp [collectPieces] at built; subst pieces; simp at member
  | cons branch rest ih =>
    cases head : project branch with
    | none => simp [collectPieces, head] at built
    | some first =>
      cases tail : collectPieces project rest with
      | none => simp [collectPieces, head, tail] at built
      | some last =>
        simp only [collectPieces, head, tail, Option.some.injEq] at built
        subst pieces
        rcases List.mem_append.mp member with left | right
        · exact ⟨branch, by simp, first, head, left⟩
        · obtain ⟨original, inside, parts, projected, retained⟩ := ih last tail right
          exact ⟨original, List.mem_cons_of_mem branch inside, parts, projected, retained⟩
/-- Numeric intervals retain optional endpoints; Enum members are singleton points.
Nonnumeric built-in atoms contribute no integer cover. Other carriers refuse. -/
def numericPieces : Nat → Ty → Option (List VariantValidation.Interval)
  | 0, _ => none
  | fuel + 1, type => match type with
    | .integerRange range => some [(range.lower, range.upper)]
    | .integerEnum values => some (values.map (fun value => (some value, some value)))
    | .atom .integer => some [(none, none)]
    | .atom .uint => some [(some 0, none)]
    | .atom _ | .booleanEnum _ | .scalarEnum .symbol _ | .scalarEnum .keyword _ => some []
    | .union branches => collectPieces (numericPieces fuel) branches
    | _ => none
/-- Projection never invents an integer belonging to no original flat branch. -/
theorem numericPieces_sound (fuel type pieces)
    (built : numericPieces fuel type = some pieces) (piece : VariantValidation.Interval)
    (member : piece ∈ pieces) (value : Int) (valid : VariantValidation.intervalHas piece value) :
    integerAccepts fuel type value = true := by
  induction fuel generalizing type pieces with
  | zero => simp [numericPieces] at built
  | succ fuel ih =>
    cases type <;> try { simp [numericPieces] at built }
    case integerRange range =>
      rcases range with ⟨low, high⟩
      simp only [numericPieces, Option.some.injEq] at built
      subst pieces
      simp only [List.mem_singleton] at member
      subst piece
      cases low <;> cases high <;>
        simp_all [integerAccepts, VariantValidation.intervalHas] <;> omega
    case scalarEnum family values =>
      cases family <;> simp [numericPieces] at built
      all_goals subst pieces
      all_goals simp at member
    case booleanEnum values =>
      simp only [numericPieces, Option.some.injEq] at built
      subst pieces
      simp at member
    case integerEnum values =>
      simp only [numericPieces, Option.some.injEq] at built
      subst pieces
      obtain ⟨original, inside, equal⟩ := List.mem_map.mp member
      subst piece
      have equal : value = original := by simp [VariantValidation.intervalHas] at valid; omega
      simp [integerAccepts, equal, inside]
    case atom name =>
      cases name <;> simp only [numericPieces, Option.some.injEq] at built
      all_goals subst pieces
      all_goals try { simp at member }
      all_goals simp only [List.mem_singleton] at member
      all_goals subst piece
      all_goals simp_all [integerAccepts, VariantValidation.intervalHas] <;> omega
    case union branches =>
      obtain ⟨branch, inside, parts, projected, retained⟩ :=
        collectPieces_origin _ branches pieces built piece member
      simp only [integerAccepts, List.any_eq_true]
      exact ⟨branch, inside, ih _ _ projected retained⟩
/-- An optionally unbounded range may span several ordered flat alternatives. Coverage uses
residual subtraction and visits no integer merely because an interval is wide. -/
def rangeUnionCheck (fuel : Nat) (source : IntegerRange) (branches : List Ty) : Bool :=
  match numericPieces fuel (.union branches) with
  | none => false
  | some pieces => VariantValidation.coversInterval (source.lower, source.upper) pieces
/-- A finite literal source is checked member by member against the same ordered
flat tree; all branches must first be admitted, even for an empty source. -/
def enumUnionCheck (fuel : Nat) (values : List Int) (branches : List Ty) : Bool :=
  match numericPieces fuel (.union branches) with
  | none => false
  | some _ => values.all (fun value => integerAccepts fuel (.union branches) value)
/-- Successful range coverage retains both complete flat admission and universal
integer membership. Hashing, mutable host predicates and serialization are absent. -/
theorem rangeUnionCheck_sound (fuel source branches)
    (accepted : rangeUnionCheck fuel source branches = true) :
    ∃ pieces, numericPieces fuel (.union branches) = some pieces ∧
      ∀ value, source.Contains value → integerAccepts fuel (.union branches) value = true := by
  cases built : numericPieces fuel (.union branches) with
  | none => simp [rangeUnionCheck, built] at accepted
  | some pieces =>
    refine ⟨pieces, rfl, ?_⟩
    intro value inside
    have covered : VariantValidation.coversInterval (source.lower, source.upper) pieces = true := by
      simpa [rangeUnionCheck, built] using accepted
    obtain ⟨piece, member, valid⟩ := VariantValidation.coversInterval_sound _ _ covered value inside
    exact numericPieces_sound _ _ _ built piece member value valid
/-- Finite literal coverage likewise retains the all-branch admission certificate. -/
theorem enumUnionCheck_sound (fuel values branches)
    (accepted : enumUnionCheck fuel values branches = true) :
    ∃ pieces, numericPieces fuel (.union branches) = some pieces ∧
      ∀ value ∈ values, integerAccepts fuel (.union branches) value = true := by
  cases built : numericPieces fuel (.union branches) with
  | none => simp [enumUnionCheck, built] at accepted
  | some pieces =>
    refine ⟨pieces, rfl, ?_⟩
    have all : values.all (fun value => integerAccepts fuel (.union branches) value) = true := by
      simpa [enumUnionCheck, built] using accepted
    exact List.all_eq_true.mp all

/-- The existing numeric view preserves integer observations of both atomic
families and literal ranges; no identification of descriptor syntax is needed. -/
theorem numericBounds_contains (source : Ty) (range : IntegerRange) (fuel : Nat) (value : Int)
    (bounds : numericBounds source = some range)
    (member : integerAccepts (fuel + 1) source value = true) : range.Contains value := by
  cases source <;> simp only [numericBounds] at bounds
  all_goals try contradiction
  case integerRange actual =>
    have equal : actual = range := Option.some.inj bounds
    subst range
    rcases actual with ⟨lower, upper⟩
    cases lower <;> cases upper <;> simp_all [integerAccepts, IntegerRange.Contains]
  case atom name =>
    cases name
    all_goals try contradiction
    all_goals cases bounds
    all_goals simp_all [integerAccepts, IntegerRange.Contains, IntegerRange.all, IntegerRange.unsigned]
/-- Joint coverage applies uniformly to Integer, UInt and IntegerRange. Every
accepted integer reaches an original alternative, independently of bit width. -/
theorem numericUnion_sound (source range fuel branches)
    (bounds : numericBounds source = some range)
    (covered : rangeUnionCheck fuel range branches = true) (value : Int)
    (member : integerAccepts (fuel + 1) source value = true) :
    integerAccepts fuel (.union branches) value = true := by
  obtain ⟨_, _, inclusion⟩ := rangeUnionCheck_sound _ _ _ covered
  exact inclusion value (numericBounds_contains source range fuel value bounds member)

/-- Bool's intrinsic finite view includes false as a value, never as absence.
Boolean Exactly descriptors are represented by singleton booleanEnum lists. -/
def booleanValues : Ty → Option (List Bool)
  | .atom .bool => some [false, true]
  | .booleanEnum values => some values
  | _ => none
/-- Pure Boolean observations of the same intrinsic flat descriptor tree. -/
def booleanAccepts : Nat → Ty → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, type, value => match type with
    | .atom .bool => true
    | .booleanEnum values => decide (value ∈ values)
    | .union branches => branches.any (fun branch => booleanAccepts fuel branch value)
    | _ => false
/-- Reuse all-branch flat admission and finite literal traversal. Wrappers cannot
hide behind an earlier successful branch, including for an empty literal set. -/
def booleanCheck (fuel : Nat) (values : List Bool) (target : Ty) : Bool :=
  match numericPieces fuel target with
  | none => false
  | some _ => values.all (fun value => booleanAccepts fuel target value)
/-- Successful finite coverage retains admission and every original literal. -/
theorem booleanCheck_sound (fuel values target)
    (accepted : booleanCheck fuel values target = true) :
    ∃ pieces, numericPieces fuel target = some pieces ∧
      ∀ value ∈ values, booleanAccepts fuel target value = true := by
  cases built : numericPieces fuel target with
  | none => simp [booleanCheck, built] at accepted
  | some pieces =>
    refine ⟨pieces, rfl, ?_⟩
    exact List.all_eq_true.mp (by simpa [booleanCheck, built] using accepted)
/-- Bool coverage is exhaustive over the whole domain, not sampled observations. -/
theorem booleanCheck_total (fuel target)
    (accepted : booleanCheck fuel [false, true] target = true) :
    ∀ value : Bool, booleanAccepts fuel target value = true := by
  obtain ⟨_, _, members⟩ := booleanCheck_sound _ _ _ accepted
  intro value
  cases value <;> exact members _ (by simp)

/-- Exhaustive Boolean coverage and identity-preserving flat validators keep
both values through the first matching branch. A selected error still cannot
fall through; identity/shape agreement is an explicit runtime interpretation. -/
theorem booleanUnion_validate (fuel : Nat) (branches : List Ty)
    (validate : Ty → Bool → Except Error Bool) (missing invalid : Error)
    (covered : booleanCheck (fuel + 1) [false, true] (.union branches) = true)
    (identity : ∀ branch ∈ branches, ∀ value,
      booleanAccepts fuel branch value = true → validate branch value = .ok value) :
    ∀ value, VariantValidation.union (booleanAccepts fuel) (booleanAccepts fuel)
      validate missing invalid branches value = .ok value := by
  intro value
  apply VariantValidation.union_identity
  · exact booleanCheck_total (fuel + 1) (.union branches) covered value
  · intro branch inside selected
    exact identity branch inside value selected


/-- Only the three intrinsic, disjoint, infinite scalar families enter this rule. -/
def infiniteScalar : Atom → Bool
  | .string | .symbol | .keyword => true
  | _ => false
/-- Complete family coverage searches the existing ordered tree without sorting. -/
def scalarWhole : Nat → Atom → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, family, type => match type with
    | .atom name => decide (family = name)
    | .union branches => branches.any (scalarWhole fuel family)
    | _ => false
/-- Literal IDs model homogeneous Symbol/Keyword Enum leaves; escape tokens are
not members of these families. Host name encoding is an interpretation premise. -/
def scalarAccepts : Nat → Atom → Ty → Nat → Bool
  | 0, _, _, _ => false
  | fuel + 1, family, type, value => match type with
    | .atom name => decide (family = name)
    | .scalarEnum name values => decide (family = name) && decide (value ∈ values)
    | .union branches => branches.any (fun branch => scalarAccepts fuel family branch value)
    | _ => false
/-- A finite descriptor bounds all literal IDs; it does not enumerate a family. -/
def scalarCutoff : Nat → Ty → Nat
  | 0, _ => 0
  | fuel + 1, type => match type with
    | .scalarEnum _ values => values.foldr max 0
    | .union branches => (branches.map (scalarCutoff fuel)).foldr max 0
    | _ => 0
/-- Every literal in a finite list is bounded by its folded maximum. -/
theorem scalarLiteral_bound (values : List Nat) (value : Nat) (inside : value ∈ values) :
    value ≤ values.foldr max 0 := by
  induction values with
  | nil => simp at inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with equal | rest
    · subst value; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih rest) (Nat.le_max_right _ _)
/-- A same-family primitive branch covers every member, independently of IDs. -/
theorem scalarWhole_sound (fuel family type value)
    (covered : scalarWhole fuel family type = true) : scalarAccepts fuel family type value = true := by
  induction fuel generalizing type with
  | zero => simp [scalarWhole] at covered
  | succ fuel ih =>
    cases type <;> simp only [scalarWhole] at covered
    all_goals try contradiction
    case atom name => exact covered
    case union branches =>
      obtain ⟨branch, inside, present⟩ := List.any_eq_true.mp covered
      exact List.any_eq_true.mpr ⟨branch, inside, ih _ present⟩
/-- Beyond the finite literal cutoff only complete-family branches can match.
This supplies a real missing witness when finite alternatives leave a gap. -/
theorem scalarFresh (fuel family type value) (fresh : scalarCutoff fuel type < value) :
    scalarAccepts fuel family type value = scalarWhole fuel family type := by
  induction fuel generalizing type with
  | zero => rfl
  | succ fuel ih =>
    cases type <;> try rfl
    case scalarEnum name values =>
      have absent : value ∉ values := by
        intro inside
        have bound := scalarLiteral_bound values value inside
        simp only [scalarCutoff] at fresh
        omega
      simp [scalarAccepts, scalarWhole, absent]
    case union branches =>
      have each : ∀ branch ∈ branches,
          scalarAccepts fuel family branch value = scalarWhole fuel family branch := by
        intro branch inside
        apply ih
        have bound := scalarLiteral_bound (branches.map (scalarCutoff fuel)) (scalarCutoff fuel branch)
          (List.mem_map.mpr ⟨branch, inside, rfl⟩)
        simp only [scalarCutoff] at fresh
        omega
      clear fresh
      simp only [scalarAccepts, scalarWhole]
      induction branches with
      | nil => rfl
      | cons head tail rest =>
        simp only [List.any_cons]
        rw [each head (by simp), rest (fun branch inside => each branch (List.mem_cons_of_mem head inside))]
/-- Universal coverage is decidable in this positive finite grammar: a whole
family branch is necessary and sufficient; finite unions of literals cannot do it. -/
theorem scalarWhole_iff (fuel family type) :
    scalarWhole fuel family type = true ↔ ∀ value, scalarAccepts fuel family type value = true := by
  constructor
  · intro covered value; exact scalarWhole_sound _ _ _ _ covered
  · intro covered
    have witness := covered (scalarCutoff fuel type + 1)
    rwa [scalarFresh _ _ _ _ (by omega)] at witness
/-- Reuse complete flat admission before applying the whole-family criterion. -/
def scalarCheck (fuel : Nat) (family : Atom) (target : Ty) : Bool :=
  infiniteScalar family && match numericPieces fuel target with
    | none => false
    | some _ => scalarWhole fuel family target
/-- Every accepted family is classified, fully admitted and universally covered. -/
theorem scalarCheck_sound (fuel family target) (accepted : scalarCheck fuel family target = true) :
    infiniteScalar family = true ∧ ∃ pieces, numericPieces fuel target = some pieces ∧
      ∀ value, scalarAccepts fuel family target value = true := by
  simp only [scalarCheck, Bool.and_eq_true] at accepted
  refine ⟨accepted.1, ?_⟩
  cases built : numericPieces fuel target with
  | none => simp [built] at accepted
  | some pieces =>
    exact ⟨pieces, rfl, (scalarWhole_iff _ _ _).mp (by simpa [built] using accepted.2)⟩
/-- Completeness holds only with the same intrinsic flat admission and fuel. -/
theorem scalarCheck_complete (fuel family target pieces)
    (familyKind : infiniteScalar family = true) (built : numericPieces fuel target = some pieces)
    (covered : ∀ value, scalarAccepts fuel family target value = true) :
    scalarCheck fuel family target = true := by
  simp [scalarCheck, familyKind, built, (scalarWhole_iff _ _ _).mpr covered]
/-- The original first-selected validation law preserves every scalar member;
identity/shape agreement is required and selected errors never authorize fallback. -/
theorem scalarUnion_validate (fuel family branches) (validate : Ty → Nat → Except Error Nat)
    (missing invalid : Error) (covered : scalarCheck (fuel + 1) family (.union branches) = true)
    (identity : ∀ branch ∈ branches, ∀ value,
      scalarAccepts fuel family branch value = true → validate branch value = .ok value) :
    ∀ value, VariantValidation.union (scalarAccepts fuel family) (scalarAccepts fuel family)
      validate missing invalid branches value = .ok value := by
  obtain ⟨_, _, _, members⟩ := scalarCheck_sound _ _ _ covered
  intro value
  apply VariantValidation.union_identity
  · exact members value
  · intro branch inside selected
    exact identity branch inside value selected

/-- Witnessed finite emptiness. Optional carriers and empty collections are not
empty Types; no arbitrary predicate or fixed-point semantic law is inferred. -/
inductive EmptyType : Ty → Prop where
  | range : range.empty = true → EmptyType (.integerRange range)
  | integers : EmptyType (.integerEnum [])
  | booleans : EmptyType (.booleanEnum [])
  | scalars : EmptyType (.scalarEnum family [])
  | tuple : child ∈ children → EmptyType child → EmptyType (.tuple children)
  | pairLeft : EmptyType a → EmptyType (.pair a b)
  | pairRight : EmptyType b → EmptyType (.pair a b)
  | union : (∀ child ∈ children, EmptyType child) → EmptyType (.union children)
  | sum : (∀ child ∈ children, EmptyType child) → EmptyType (.sum tags children)

/-- A bounded positive emptiness derivation, without descriptor normalization.
False means no witness within this fragment/fuel, not a claimed inhabitant. -/
def emptyCheck : Nat → Ty → Bool
  | 0, _ => false
  | fuel + 1, type => match type with
    | .integerRange range => range.empty
    | .integerEnum values => values.isEmpty
    | .booleanEnum values => values.isEmpty
    | .scalarEnum _ values => values.isEmpty
    | .tuple children => children.any (emptyCheck fuel)
    | .pair a b => emptyCheck fuel a || emptyCheck fuel b
    | .union children | .sum _ children => children.all (emptyCheck fuel)
    | _ => false

/-- Every discovered empty product/alternative has a complete finite witness. -/
theorem emptyCheck_sound (fuel : Nat) (type : Ty) (accepted : emptyCheck fuel type = true) :
    EmptyType type := by
  induction fuel generalizing type with
  | zero => simp [emptyCheck] at accepted
  | succ fuel ih =>
    cases type <;> simp only [emptyCheck] at accepted
    all_goals try contradiction
    case integerRange range => exact .range accepted
    case integerEnum values => cases values <;> simp_all; exact .integers
    case booleanEnum values => cases values <;> simp_all; exact .booleans
    case scalarEnum family values => cases values <;> simp_all; exact .scalars
    case tuple children =>
      obtain ⟨child, member, empty⟩ := List.any_eq_true.mp accepted
      exact .tuple member (ih child empty)
    case pair a b =>
      simp only [Bool.or_eq_true] at accepted
      rcases accepted with left | right
      · exact .pairLeft (ih a left)
      · exact .pairRight (ih b right)
    case union children => exact .union (fun child member => ih child ((List.all_eq_true.mp accepted) child member))
    case sum tags children => exact .sum (fun child member => ih child ((List.all_eq_true.mp accepted) child member))

/-- Public ordered Union and Sum identities retain their existing invariant even
when empty. An enclosing impossible product may still have no inhabitants. -/
def emptySource (fuel : Nat) (type : Ty) : Bool :=
  match type with
  | .union _ | .sum _ _ => false
  | _ => emptyCheck fuel type

/-- Union targets still require full intrinsic flat admission; an empty source
cannot hide a wrapper-bearing branch behind vacuous membership coverage. -/
def emptyTarget (fuel : Nat) (type : Ty) : Bool :=
  match type with
  | .union _ => (numericPieces fuel type).isSome
  | _ => true

/-- Public emptiness permission cannot manufacture an unsupported derivation. -/
theorem emptySource_sound (fuel type) (accepted : emptySource fuel type = true) : EmptyType type := by
  cases type <;> first | exact emptyCheck_sound fuel _ accepted | contradiction

/-- Host interpretation obligations are shape inversions and empty scalar laws.
No user recognizer, callback, parser or recursive fixed point is certified here. -/
structure EmptyLaws (accepts : Ty → Value → Prop) where
  range : ∀ range, range.empty = true → ∀ value, ¬ accepts (.integerRange range) value
  integers : ∀ value, ¬ accepts (.integerEnum []) value
  booleans : ∀ value, ¬ accepts (.booleanEnum []) value
  scalars : ∀ family value, ¬ accepts (.scalarEnum family []) value
  tuple : ∀ children child, child ∈ children → ∀ value, accepts (.tuple children) value →
    ∃ item, accepts child item
  pairLeft : ∀ a b value, accepts (.pair a b) value → ∃ item, accepts a item
  pairRight : ∀ a b value, accepts (.pair a b) value → ∃ item, accepts b item
  union : ∀ children value, accepts (.union children) value → ∃ child ∈ children, accepts child value
  sum : ∀ tags children value, accepts (.sum tags children) value → ∃ child ∈ children, ∃ item, accepts child item

/-- Empty witnesses reject all observations under explicit host shape laws. -/
theorem EmptyType.refuses (laws : EmptyLaws accepts) (empty : EmptyType type) :
    ∀ value, ¬ accepts type value := by
  induction empty with
  | range proof => exact laws.range _ proof
  | integers => exact laws.integers
  | booleans => exact laws.booleans
  | scalars => exact laws.scalars _
  | tuple member _ ih =>
    intro value valid
    obtain ⟨item, checked⟩ := laws.tuple _ _ member value valid
    exact ih item checked
  | pairLeft _ ih =>
    intro value valid
    obtain ⟨item, checked⟩ := laws.pairLeft _ _ value valid
    exact ih item checked
  | pairRight _ ih =>
    intro value valid
    obtain ⟨item, checked⟩ := laws.pairRight _ _ value valid
    exact ih item checked
  | union _ ih =>
    intro value valid
    obtain ⟨child, member, checked⟩ := laws.union _ value valid
    exact ih child member value checked
  | sum _ ih =>
    intro value valid
    obtain ⟨child, member, item, checked⟩ := laws.sum _ _ value valid
    exact ih child member item checked

/-- Required row fields use the same product law. Optional fields cannot supply
this premise; open/closed layout and mutable writes remain separate protocols. -/
theorem requiredField_refuses (accepts : Field → Value → Prop) (required : Field → Prop)
    (layout : Row → Value → Prop)
    (projection : ∀ row value field, layout row value → required field → ∃ item, accepts field item)
    (field : Field) (mandatory : required field) (empty : ∀ item, ¬ accepts field item) :
    ∀ row value, ¬ layout row value := by
  intro row value valid
  obtain ⟨item, checked⟩ := projection row value field valid mandatory
  exact empty item checked

end LeanPoo.Functional.PrototypeTypes
