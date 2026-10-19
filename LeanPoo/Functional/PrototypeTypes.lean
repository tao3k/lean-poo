import Std
import LeanPoo.Functional.VariantValidation

/-! Finite rank-one prototype types. This advances the type-system future work in
Appendices C/D: explicit Self <: Super constraints, structural variance and finite
candidate inference. Host recognizers, effect behavior and mutable slot writes
are not identified with this semantic replacement relation. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- The admitted scalar vocabulary has one proper numeric inclusion. -/
inductive Atom where
  | bool | integer | uint | string | symbol
  deriving Repr, DecidableEq
/-- Literal inclusive endpoints of the existing IntegerRange descriptor.
None means unbounded; reversed finite bounds denote the empty integer set. -/
structure IntegerRange where
  lower : Option Int
  upper : Option Int
  deriving Repr, DecidableEq
/-- Membership uses exact integer order, not enumeration or machine word bounds. -/
def IntegerRange.Contains (range : IntegerRange) (value : Int) : Prop :=
  (∀ lower, range.lower = some lower → lower ≤ value) ∧
  (∀ upper, range.upper = some upper → value ≤ upper)
/-- All exact integers and UInt have fixed symbolic interval views. -/
def IntegerRange.all : IntegerRange := ⟨none, none⟩
/-- UInt's interval is inclusive zero through an unbounded upper endpoint. -/
def IntegerRange.unsigned : IntegerRange := ⟨some 0, none⟩
/-- Empty numeric ranges are successful descriptor data, not exhausted work. -/
def IntegerRange.empty (range : IntegerRange) : Bool :=
  match range.lower, range.upper with
  | some lower, some upper => decide (upper < lower)
  | _, _ => false
/-- Source inclusion checks only endpoints. Descriptor identity is separate:
mutually included Integer/UInt/range spellings need not have identical metadata. -/
def IntegerRange.includes (source target : IntegerRange) : Bool :=
  source.empty ||
    (match target.lower with | none => true | some lower => source.lower.any (fun actual => decide (lower ≤ actual))) &&
    (match target.upper with | none => true | some upper => source.upper.any (fun actual => decide (actual ≤ upper)))
/-- Checked interval inclusion preserves every integer observation, including
empty and one-sided ranges. No host predicate or primitive execution is assumed. -/
theorem IntegerRange.replacement (source target : IntegerRange)
    (included : source.includes target = true) (value : Int)
    (valid : source.Contains value) : target.Contains value := by
  rcases source with ⟨lower, upper⟩
  rcases target with ⟨lower', upper'⟩
  cases lower <;> cases upper <;> cases lower' <;> cases upper' <;>
    simp_all [IntegerRange.includes, IntegerRange.empty, IntegerRange.Contains] <;> omega
/-- Reversed finite endpoints cannot certify any integer observation. -/
theorem IntegerRange.empty_refuses (range : IntegerRange) (value : Int)
    (empty : range.empty = true) : ¬ range.Contains value := by
  rcases range with ⟨lower, upper⟩
  cases lower <;> cases upper <;> simp_all [IntegerRange.empty, IntegerRange.Contains] <;> omega

/-- Membership traversal is bounded by finite target data, never interval width.
Scheme uses an equal? table for these literal lookups and its shared work quota. -/
def IntegerRange.coverFrom : Nat → Int → Int → List Int → Bool
  | fuel, lower, upper, values =>
    if upper < lower then true else match fuel with
      | 0 => false
      | fuel + 1 => decide (lower ∈ values) && coverFrom fuel (lower + 1) upper values
/-- A successful bounded traversal contains every integer in the closed interval. -/
theorem IntegerRange.coverFrom_sound (fuel lower upper values)
    (accepted : coverFrom fuel lower upper values = true) :
    ∀ value, lower ≤ value → value ≤ upper → value ∈ values := by
  induction fuel generalizing lower with
  | zero => simp [coverFrom] at accepted; omega
  | succ fuel ih =>
    simp only [coverFrom] at accepted
    split at accepted
    · omega
    · simp only [Bool.and_eq_true] at accepted
      obtain ⟨head, tail⟩ := accepted
      intro value above below
      by_cases equal : value = lower
      · simpa [equal] using of_decide_eq_true head
      · exact ih (lower + 1) tail value (by omega) below
/-- Coverage is complete when the finite probe budget spans the interval and
every integer belongs to the target; duplicate data never proves membership. -/
theorem IntegerRange.coverFrom_complete (fuel : Nat) (lower upper : Int) (values : List Int)
    (enough : upper - lower < (fuel : Int))
    (members : ∀ value, lower ≤ value → value ≤ upper → value ∈ values) :
    coverFrom fuel lower upper values = true := by
  induction fuel generalizing lower with
  | zero => simp [coverFrom]; omega
  | succ fuel ih =>
    simp only [coverFrom]
    split
    · rfl
    · simp only [Bool.and_eq_true]
      constructor
      · exact decide_eq_true (members lower (by omega) (by omega))
      · apply ih (lower + 1) (by omega)
        intro value above below
        exact members value (by omega) below
/-- Empty ranges fit every finite target. Nonempty unbounded ranges refuse;
finite traversal has at most as many membership probes as target literals. -/
def IntegerRange.coveredBy (range : IntegerRange) (values : List Int) : Bool :=
  range.empty || match range.lower, range.upper with
    | some lower, some upper => coverFrom values.length lower upper values
    | _, _ => false
/-- Finite literal coverage preserves every integer observation, including empty
and huge-endpoint intervals; duplicate literals supply no missing membership. -/
theorem IntegerRange.coveredBy_sound (range : IntegerRange) (values : List Int)
    (accepted : range.coveredBy values = true) (value : Int)
    (valid : range.Contains value) : value ∈ values := by
  unfold coveredBy at accepted
  simp only [Bool.or_eq_true] at accepted
  rcases accepted with empty | covered
  · exact False.elim (range.empty_refuses value empty valid)
  · rcases range with ⟨lower, upper⟩
    cases lower <;> cases upper <;> simp only at covered
    all_goals try contradiction
    exact coverFrom_sound _ _ _ _ covered value (valid.1 _ rfl) (valid.2 _ rfl)

/-- Finite expressions reuse existing Type/Function/container constructor shapes.
Function lists retain exact input and multiple-output counts. -/
inductive Ty where
  | top | atom (name : Atom) | list (element : Ty) | tuple (fields : List Ty)
  | integerRange (range : IntegerRange)
  | integerEnum (values : List Int)
  | maybe (element : Ty) | orFalse (element : Ty)
  | function (outputs inputs : List Ty)
  | pair (left right : Ty) | map (key value : Ty)
  | sum (tags : List Nat) (payloads : List Ty) | union (branches : List Ty)
  deriving Repr

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
    | .atom _ => some []
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

/-- A pointwise relation checks exact length; zip cannot silently drop arguments. -/
def all₂ (test : Ty → Ty → Bool) : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => test a b && all₂ test as bs
  | _, _ => false

/-- Exact finite syntax identity is stricter than mutual derivability. It keeps
Map key normalization and ordered Union selection fixed, including nested arrows. -/
def same : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b => match a, b with
    | .top, .top => true
    | .atom a, .atom b => decide (a = b)
    | .integerRange a, .integerRange b => decide (a = b)
    | .integerEnum a, .integerEnum b => decide (a = b)
    | .list a, .list b | .maybe a, .maybe b | .orFalse a, .orFalse b => same fuel a b
    | .tuple as, .tuple bs | .union as, .union bs => all₂ (same fuel) as bs
    | .pair a b, .pair c d | .map a b, .map c d => same fuel a c && same fuel b d
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (same fuel) as bs
    | .function outs ins, .function outs' ins' =>
        all₂ (same fuel) outs outs' && all₂ (same fuel) ins ins'
    | _, _ => false

/-- Exact list identity cannot lose, reorder or merge a branch. -/
theorem all₂_equal (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → a = b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [all₂]
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      simp only [all₂, Bool.and_eq_true] at accepted
      have both := accepted
      exact congr (congrArg List.cons (sound a b both.1)) (ih bs both.2)

/-- Successful identity checks imply propositional equality, not a sampled match. -/
theorem same_sound (fuel : Nat) (a b : Ty) (accepted : same fuel a b = true) : a = b := by
  induction fuel generalizing a b with
  | zero => simp [same] at accepted
  | succ fuel ih =>
    cases a <;> cases b <;> simp only [same] at accepted
    all_goals try contradiction
    all_goals try rfl
    all_goals first
      | exact congrArg Ty.atom (of_decide_eq_true accepted)
      | exact congrArg Ty.integerRange (of_decide_eq_true accepted)
      | exact congrArg Ty.integerEnum (of_decide_eq_true accepted)
      | exact congrArg Ty.list (ih _ _ accepted)
      | exact congrArg Ty.maybe (ih _ _ accepted)
      | exact congrArg Ty.orFalse (ih _ _ accepted)
      | exact congrArg Ty.tuple (all₂_equal _ ih _ _ accepted)
      | exact congrArg Ty.union (all₂_equal _ ih _ _ accepted)
      | simp only [Bool.and_eq_true] at accepted
        have both := accepted
        first
        | exact congr (congrArg Ty.pair (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.map (ih _ _ both.1)) (ih _ _ both.2)
        | exact congr (congrArg Ty.function (all₂_equal _ ih _ _ both.1)) (all₂_equal _ ih _ _ both.2)
        | exact congr (congrArg Ty.sum (of_decide_eq_true both.1)) (all₂_equal _ ih _ _ both.2)

/-- Exact positional lifting of a relation, including empty argument lists. -/
inductive RelList (relation : Ty → Ty → Prop) : List Ty → List Ty → Prop where
  | nil : RelList relation [] []
  | cons : relation a b → RelList relation as bs → RelList relation (a :: as) (b :: bs)

/-- Declarative replacement, independent of prototype ancestry or samples. -/
inductive Subtype : Ty → Ty → Prop where
  | refl (a) : Subtype a a
  | top (a) : Subtype a .top
  | uint : Subtype (.atom .uint) (.atom .integer)
  | numeric : numericBounds a = some source → numericBounds b = some target →
      source.includes target = true → Subtype a b
  | rangeEnum : range.coveredBy values = true → Subtype (.integerRange range) (.integerEnum values)
  | rangeUnion : rangeUnionCheck fuel source branches = true →
      Subtype (.integerRange source) (.union branches)
  | enumUnion : enumUnionCheck fuel values branches = true → Subtype (.integerEnum values) (.union branches)
  | list : Subtype a b → Subtype (.list a) (.list b)
  | maybe : Subtype a b → Subtype (.maybe a) (.maybe b)
  | orFalse : Subtype a b → Subtype (.orFalse a) (.orFalse b)
  | tuple : RelList Subtype as bs → Subtype (.tuple as) (.tuple bs)
  | pair : Subtype a c → Subtype b d → Subtype (.pair a b) (.pair c d)
  | map : Subtype a b → Subtype (.map key a) (.map key b)
  | sum : RelList Subtype as bs → Subtype (.sum tags as) (.sum tags bs)
  | function : RelList Subtype outs outs' → RelList Subtype ins' ins →
      Subtype (.function outs ins) (.function outs' ins')

/-- Finite derivability checker; exhaustion is separate from a negative result in
Scheme. Fuel here bounds derivation unfolding, not host GC or callback costs. -/
def check : Nat → Ty → Ty → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    match a, b with
    | _, .top => true
    | .atom a, .atom b => decide (a = b) || decide (a = .uint ∧ b = .integer)
    | .integerRange source, .integerRange target => source.includes target
    | .integerRange source, .integerEnum values => source.coveredBy values
    | .integerEnum values, .integerEnum target => decide (values = target)
    | .integerRange source, .union branches => rangeUnionCheck fuel source branches
    | .integerEnum values, .union branches => enumUnionCheck fuel values branches
    | .integerRange source, .atom .integer => source.includes IntegerRange.all
    | .integerRange source, .atom .uint => source.includes IntegerRange.unsigned
    | .atom .integer, .integerRange target => IntegerRange.all.includes target
    | .atom .uint, .integerRange target => IntegerRange.unsigned.includes target
    | .list a, .list b | .maybe a, .maybe b | .orFalse a, .orFalse b => check fuel a b
    | .tuple as, .tuple bs => all₂ (check fuel) as bs
    | .pair a b, .pair c d => check fuel a c && check fuel b d
    | .map k a, .map k' b => same fuel k k' && check fuel a b
    | .sum tags as, .sum tags' bs => decide (tags = tags') && all₂ (check fuel) as bs
    | .union as, .union bs => all₂ (same fuel) as bs
    | .function outs ins, .function outs' ins' =>
        all₂ (check fuel) outs outs' && all₂ (check fuel) ins' ins
    | _, _ => false

/-- Lift a Boolean comparison's soundness through exact positional matching. -/
theorem all₂_sound (test : Ty → Ty → Bool) (sound : ∀ a b, test a b = true → Subtype a b)
    (as bs : List Ty) (accepted : all₂ test as bs = true) : RelList Subtype as bs := by
  induction as generalizing bs with
  | nil => cases bs with
    | nil => exact .nil
    | cons b bs => simp [all₂] at accepted
  | cons a as ih =>
    cases bs with
    | nil => simp [all₂] at accepted
    | cons b bs =>
      have both : test a b = true ∧ all₂ test as bs = true := by simpa only [all₂, Bool.and_eq_true] using accepted
      obtain ⟨head, tail⟩ := both
      exact .cons (sound a b head) (ih bs tail)

/-- Every checked inclusion has a declarative derivation, including higher-order
contravariance and multiple-value arity. No relation is inferred from inheritance. -/
theorem check_sound (fuel : Nat) (a b : Ty) (accepted : check fuel a b = true) : Subtype a b := by
  induction fuel generalizing a b with
  | zero => simp [check] at accepted
  | succ fuel ih =>
    cases a <;> cases b <;> simp only [check] at accepted
    all_goals try { contradiction }
    all_goals try { exact .top _ }
    all_goals try { exact .list (ih _ _ accepted) }
    all_goals try { exact .maybe (ih _ _ accepted) }
    all_goals try { exact .orFalse (ih _ _ accepted) }
    all_goals try { exact .tuple (all₂_sound _ ih _ _ accepted) }
    case integerRange.integerRange source target => exact .numeric rfl rfl accepted
    case integerRange.integerEnum source values => exact .rangeEnum accepted
    case integerEnum.integerEnum values target =>
      have equal := of_decide_eq_true accepted
      subst target
      exact .refl _
    case integerRange.union source branches => exact .rangeUnion accepted
    case integerEnum.union values branches => exact .enumUnion accepted
    case integerRange.atom source target =>
      cases target
      all_goals first | contradiction | exact .numeric rfl rfl accepted
    case atom.integerRange source target =>
      cases source
      all_goals first | contradiction | exact .numeric rfl rfl accepted
    case pair.pair a b c d =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      exact .pair (ih _ _ both.1) (ih _ _ both.2)
    case map.map key a key' b =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      have equal := same_sound _ _ _ both.1
      subst key'
      exact .map (ih _ _ both.2)
    case sum.sum tags as tags' bs =>
      simp only [Bool.and_eq_true] at accepted
      have both := accepted
      have equal : tags = tags' := of_decide_eq_true both.1
      subst tags'
      exact .sum (all₂_sound _ ih _ _ both.2)
    case union.union as bs =>
      have equal := all₂_equal _ (same_sound fuel) _ _ accepted
      subst bs
      exact .refl _
    case function.function outs ins outs' ins' =>
      have both : all₂ (check fuel) outs outs' = true ∧ all₂ (check fuel) ins' ins = true := by
        simpa only [Bool.and_eq_true] using accepted
      exact .function (all₂_sound _ ih _ _ both.1) (all₂_sound _ ih _ _ both.2)
    case atom.atom a b =>
      cases a <;> cases b <;> simp_all
      all_goals first | exact .refl _ | exact .uint

/-- Closed scalar derivations admit only identical families or UInt <: Integer.
String/Symbol conversion APIs cannot silently become a replacement permission. -/
theorem atom_inclusion (fuel : Nat) (source target : Atom)
    (accepted : check fuel (.atom source) (.atom target) = true) :
    source = target ∨ (source = .uint ∧ target = .integer) := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    simp only [check, Bool.or_eq_true] at accepted
    rcases accepted with same | numeric
    · exact .inl (of_decide_eq_true same)
    · exact .inr (of_decide_eq_true numeric)

/-- Runtime text/symbol conversion does not identify the source and target Types. -/
theorem text_distinct (fuel : Nat) :
    check fuel (.atom .string) (.atom .symbol) = false ∧
      check fuel (.atom .symbol) (.atom .string) = false := by
  cases fuel <;> simp [check]

/-- Admitted Map replacement cannot alter normalized key syntax. This is an
observational rule; permission to mutate the map requires a separate write law. -/
theorem map_key_invariant (fuel : Nat) (key key' value value' : Ty)
    (accepted : check fuel (.map key value) (.map key' value') = true) : key = key' := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have both : same fuel key key' = true ∧ check fuel value value' = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    exact same_sound _ _ _ both.1

/-- Ordered Union replacement fixes every branch, including duplicates and
higher-order payloads. A later permissive branch cannot erase a selected failure. -/
theorem union_branches_invariant (fuel : Nat) (as bs : List Ty)
    (accepted : check fuel (.union as) (.union bs) = true) : as = bs := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel => exact all₂_equal _ (same_sound fuel) _ _ accepted

/-- A Sum's finite tag skeleton is retained exactly; parser admission additionally
requires distinct tags and one payload for each tag before this algebra is built. -/
theorem sum_tags_invariant (fuel : Nat) (tags tags' : List Nat) (as bs : List Ty)
    (accepted : check fuel (.sum tags as) (.sum tags' bs) = true) : tags = tags' := by
  cases fuel with
  | zero => simp [check] at accepted
  | succ fuel =>
    have both : decide (tags = tags') = true ∧ all₂ (check fuel) as bs = true := by
      simpa only [check, Bool.and_eq_true] using accepted
    exact of_decide_eq_true both.1

/-- Semantic replacement is an explicit model premise. A bare Scheme procedure?
recognizer does not satisfy the arrow law; its behavioral interpretation must. -/
structure Interpretation (Value : Type) where
  accepts : Ty → Value → Prop
  top : ∀ a v, accepts a v → accepts .top v
  uint : ∀ v, accepts (.atom .uint) v → accepts (.atom .integer) v
  numeric : ∀ a b source target, numericBounds a = some source → numericBounds b = some target →
    (∀ value, source.Contains value → target.Contains value) → ∀ v, accepts a v → accepts b v
  rangeEnum : ∀ range values, (∀ value, range.Contains value → value ∈ values) →
    ∀ v, accepts (.integerRange range) v → accepts (.integerEnum values) v
  rangeUnion : ∀ source branches fuel pieces,
    numericPieces fuel (.union branches) = some pieces →
    (∀ value, source.Contains value → integerAccepts fuel (.union branches) value = true) →
    ∀ v, accepts (.integerRange source) v → accepts (.union branches) v
  enumUnion : ∀ values branches fuel pieces,
    numericPieces fuel (.union branches) = some pieces →
    (∀ value ∈ values, integerAccepts fuel (.union branches) value = true) →
    ∀ v, accepts (.integerEnum values) v → accepts (.union branches) v
  list : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.list a) v → accepts (.list b) v
  maybe : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.maybe a) v → accepts (.maybe b) v
  orFalse : ∀ a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.orFalse a) v → accepts (.orFalse b) v
  tuple : ∀ as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.tuple as) v → accepts (.tuple bs) v
  pair : ∀ a b c d, (∀ v, accepts a v → accepts c v) →
    (∀ v, accepts b v → accepts d v) → ∀ v, accepts (.pair a b) v → accepts (.pair c d) v
  map : ∀ key a b, (∀ v, accepts a v → accepts b v) →
    ∀ v, accepts (.map key a) v → accepts (.map key b) v
  sum : ∀ tags as bs, RelList (fun a b => ∀ v, accepts a v → accepts b v) as bs →
    ∀ v, accepts (.sum tags as) v → accepts (.sum tags bs) v
  function : ∀ outs outs' ins ins',
    RelList (fun a b => ∀ v, accepts a v → accepts b v) outs outs' →
    RelList (fun a b => ∀ v, accepts a v → accepts b v) ins' ins →
    ∀ v, accepts (.function outs ins) v → accepts (.function outs' ins') v

/-- Conditional denotational inclusion states exactly what safe replacement means.
The library wrapper still rechecks calls, outputs and exact evidence identities. -/
theorem replacement (model : Interpretation Value) (derivation : Subtype a b) :
    ∀ v, model.accepts a v → model.accepts b v := by
  exact Subtype.rec
    (motive_1 := fun a b _ => ∀ v, model.accepts a v → model.accepts b v)
    (motive_2 := fun as bs _ => RelList (fun a b => ∀ v, model.accepts a v → model.accepts b v) as bs)
    (fun _ _ h => h) model.top model.uint
    (fun left right included => model.numeric _ _ _ _ left right (IntegerRange.replacement _ _ included))
    (fun covered => model.rangeEnum _ _ (IntegerRange.coveredBy_sound _ _ covered))
    (fun accepted => by
      obtain ⟨pieces, projected, covered⟩ := rangeUnionCheck_sound _ _ _ accepted
      exact model.rangeUnion _ _ _ pieces projected covered)
    (fun accepted => by
      obtain ⟨pieces, projected, covered⟩ := enumUnionCheck_sound _ _ _ accepted
      exact model.enumUnion _ _ _ pieces projected covered)
    (fun _ ih => model.list _ _ ih)
    (fun _ ih => model.maybe _ _ ih)
    (fun _ ih => model.orFalse _ _ ih)
    (fun _ ih => model.tuple _ _ ih)
    (fun _ _ ha hb => model.pair _ _ _ _ ha hb)
    (fun _ ih => model.map _ _ _ ih)
    (fun _ ih => model.sum _ _ _ ih)
    (fun _ _ ho hi => model.function _ _ _ _ ho hi)
    RelList.nil (fun _ _ head tail => RelList.cons head tail) derivation

/-- Rank-one templates bind named finite variables; arbitrary recursive equations
and higher-rank impredicative quantifiers are outside this expression language. -/
inductive Expr where
  | ground (type : Ty) | var (name : Nat)
  | list (element : Expr) | tuple (fields : List Expr)
  | maybe (element : Expr) | orFalse (element : Expr)
  | function (outputs inputs : List Expr)
  | pair (left right : Expr) | map (key value : Expr)
  | sum (tags : List Nat) (payloads : List Expr) | union (branches : List Expr)
  deriving Repr

/-- Structural substitution is total in a supplied explicit environment. Admission
separately checks declared names, bounds and available candidate assignments. -/
def substitute (env : Nat → Ty) : Expr → Ty
  | .ground t => t
  | .var name => env name
  | .list e => .list (substitute env e)
  | .maybe e => .maybe (substitute env e)
  | .orFalse e => .orFalse (substitute env e)
  | .tuple es => .tuple (es.map (substitute env))
  | .pair a b => .pair (substitute env a) (substitute env b)
  | .map key value => .map (substitute env key) (substitute env value)
  | .sum tags es => .sum tags (es.map (substitute env))
  | .union es => .union (es.map (substitute env))
  | .function outs ins => .function (outs.map (substitute env)) (ins.map (substitute env))

/-- Bounds and call-site inequalities are checked together for each assignment. -/
def satisfies (fuel : Nat) (constraints : List (Expr × Expr)) (env : Nat → Ty) : Bool :=
  constraints.all fun (a, b) => check fuel (substitute env a) (substitute env b)

/-- A successful assignment proves every substituted constraint, without an
assumption that a field recognizer implies another arbitrary field recognizer. -/
theorem satisfies_sound (fuel constraints env) (accepted : satisfies fuel constraints env = true)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact check_sound _ _ _ ((List.all_eq_true.mp accepted) _ bound)

/-- Classification retains ambiguity. A singleton is accepted only after the
whole supplied finite assignment list was checked; a prefix is never a solution. -/
inductive Inference (Assignment : Type) where
  | none | unique (assignment : Assignment) | ambiguous (assignments : List Assignment)
  deriving Repr, DecidableEq
/-- Infer over an explicit finite universe; Scheme constructs the Cartesian list
lazily under its shared work counter, preserving this order and exact filtering. -/
def infer (valid : Assignment → Bool) (candidates : List Assignment) : Inference Assignment :=
  match candidates.filter valid with
  | [] => .none
  | [one] => .unique one
  | many => .ambiguous many

/-- Unique inference contains an actual admitted candidate, not the first match
of an incomplete or ambiguous search. -/
theorem infer_unique (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : infer valid candidates = .unique assignment) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold infer at accepted
  split at accepted <;> simp_all
  next one matched =>
    have equal : one = assignment := by simpa using accepted
    subst one
    have member : assignment ∈ candidates.filter valid := by simp [matched]
    exact List.mem_filter.mp member

/-- Completed failure is exact within the supplied finite universe. It does not
claim that no instance exists outside that universe or at arbitrary rank. -/
theorem infer_none (valid : Assignment → Bool) (candidates : List Assignment)
    (refused : infer valid candidates = .none) :
    ∀ assignment ∈ candidates, valid assignment = false := by
  have empty : candidates.filter valid = [] := by
    unfold infer at refused
    split at refused <;> simp_all
  intro assignment member
  cases good : valid assignment with
  | false => rfl
  | true =>
    have inFiltered : assignment ∈ candidates.filter valid := List.mem_filter.mpr ⟨member, good⟩
    simp [empty] at inFiltered

/-- Unique bounded inference entails every substituted declaration/query law. -/
theorem inferred_constraints (fuel : Nat) (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : infer (satisfies fuel constraints) candidates = .unique env)
    (bound : (a, b) ∈ constraints) : Subtype (substitute env a) (substitute env b) := by
  exact satisfies_sound _ _ _ (infer_unique _ _ accepted).2 bound

/-- Resource failure carries no partial assignment or initialized prototype. -/
inductive Failure where
  | unsupported | malformed | exhausted | bounds
  deriving Repr, DecidableEq
/-- Atomic bounded search refuses before classification when the assignment scan
is incomplete. Individual expression/comparison work is additionally metered by
Scheme; this abstract scan bound is not an exact allocation/performance claim. -/
def inferBounded (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment) :
    Except Failure (Inference Assignment) :=
  if candidates.length ≤ budget then .ok (infer valid candidates) else .error .exhausted

/-- Exhaustion cannot expose a unique candidate from an already accepted prefix. -/
theorem incomplete_refuses (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (incomplete : budget < candidates.length) :
    inferBounded budget valid candidates = .error .exhausted := by
  simp [inferBounded, Nat.not_le.mpr incomplete]

/-- A successful bounded unique result retains semantic candidate validity. -/
theorem bounded_unique (budget : Nat) (valid : Assignment → Bool) (candidates : List Assignment)
    (accepted : inferBounded budget valid candidates = .ok (.unique assignment)) :
    assignment ∈ candidates ∧ valid assignment = true := by
  unfold inferBounded at accepted
  split at accepted
  · exact infer_unique valid candidates (Except.ok.inj accepted)
  · contradiction

/-- Candidate-dependent projection retains the layout/signature evidence beside
its original assignment. Bounds/kind mismatch rejects only that candidate; other
failures abort the whole search. Fuel is shared across the complete scan and no
accepted prefix is returned on exhaustion. Expression-level work is separately
metered by Scheme, so this scan bound is not a runtime cost certificate. -/
def collectCandidates (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) : Nat → List Assignment →
    Except Failure (List (Assignment × Evidence))
  | _, [] => .ok []
  | 0, _ :: _ => .error .exhausted
  | fuel + 1, candidate :: rest =>
    match derive candidate with
    | .error .bounds => collectCandidates derive valid fuel rest
    | .error cause => .error cause
    | .ok evidence =>
      match collectCandidates derive valid fuel rest with
      | .error cause => .error cause
      | .ok accepted => .ok (if valid candidate evidence then (candidate, evidence) :: accepted else accepted)

/-- Every retained layout belongs to its own candidate, and that same candidate
satisfies all bounds and call inequalities derived from the layout. Sibling
queries from different alternatives cannot be merged into a synthetic solution. -/
theorem collectCandidates_sound (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidates accepted)
    (completed : collectCandidates derive valid fuel candidates = .ok accepted)
    (entry : Assignment × Evidence) (member : entry ∈ accepted) :
    entry.1 ∈ candidates ∧ derive entry.1 = .ok entry.2 ∧ valid entry.1 entry.2 = true := by
  induction candidates generalizing fuel accepted with
  | nil => simp [collectCandidates] at completed; subst accepted; simp at member
  | cons candidate rest ih =>
    cases fuel with
    | zero => simp [collectCandidates] at completed
    | succ fuel =>
      cases projected : derive candidate with
      | error cause =>
        cases cause <;> simp only [collectCandidates, projected] at completed
        all_goals try contradiction
        obtain ⟨source, own, checked⟩ := ih fuel accepted completed member
        exact ⟨List.mem_cons_of_mem _ source, own, checked⟩
      | ok evidence =>
        cases tail : collectCandidates derive valid fuel rest with
        | error cause => simp [collectCandidates, projected, tail] at completed
        | ok remaining =>
          by_cases checked : valid candidate evidence = true
          · simp [collectCandidates, projected, tail, checked] at completed
            subst accepted
            rcases List.mem_cons.mp member with equal | later
            · subst entry; exact ⟨by simp, projected, checked⟩
            · obtain ⟨source, own, good⟩ := ih fuel remaining tail later
              exact ⟨List.mem_cons_of_mem _ source, own, good⟩
          · simp [collectCandidates, projected, tail, checked] at completed
            subst accepted
            obtain ⟨source, own, good⟩ := ih fuel remaining tail member
            exact ⟨List.mem_cons_of_mem _ source, own, good⟩

/-- Complete successful scanning retains every admitted candidate. Thus a unique
answer cannot hide another valid layout, and no-solution is relative to the whole
explicit universe rather than to a visited prefix. -/
theorem collectCandidates_complete (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidates accepted)
    (completed : collectCandidates derive valid fuel candidates = .ok accepted)
    (candidate : Assignment) (evidence : Evidence) (source : candidate ∈ candidates)
    (projected : derive candidate = .ok evidence) (checked : valid candidate evidence = true) :
    (candidate, evidence) ∈ accepted := by
  induction candidates generalizing fuel accepted with
  | nil => simp at source
  | cons head rest ih =>
    cases fuel with
    | zero => simp [collectCandidates] at completed
    | succ fuel =>
      cases first : derive head with
      | error cause =>
        cases cause <;> simp only [collectCandidates, first] at completed
        all_goals try contradiction
        rcases List.mem_cons.mp source with equal | later
        · subst head; rw [projected] at first; contradiction
        · exact ih fuel accepted completed later
      | ok value =>
        cases tail : collectCandidates derive valid fuel rest with
        | error cause => simp [collectCandidates, first, tail] at completed
        | ok remaining =>
          rcases List.mem_cons.mp source with equal | later
          · subst head
            have same : value = evidence := by simpa [projected] using first.symm
            subst value
            simp [collectCandidates, first, tail, checked] at completed
            subst accepted
            exact List.mem_cons_self
          · have retained := ih fuel remaining tail later
            by_cases headValid : valid head value = true
            · simp [collectCandidates, first, tail, headValid] at completed
              subst accepted
              exact List.mem_cons_of_mem _ retained
            · simp [collectCandidates, first, tail, headValid] at completed
              subst accepted
              exact retained

/-- Not even a valid first assignment can survive an incomplete scan. -/
theorem collectCandidates_exhausted (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (candidate : Assignment) (rest : List Assignment) :
    collectCandidates derive valid 0 (candidate :: rest) = .error .exhausted := rfl

/-- A well-formed candidate with the wrong kind is an ordinary negative choice,
not a whole-request syntax error and not an excuse to suppress later errors. -/
theorem collectCandidates_bounds (derive : Assignment → Except Failure Evidence)
    (valid : Assignment → Evidence → Bool) (fuel candidate rest)
    (rejected : derive candidate = .error .bounds) :
    collectCandidates derive valid (fuel + 1) (candidate :: rest) =
      collectCandidates derive valid fuel rest := by
  simp [collectCandidates, rejected]

/-- Prefix binding fixes the first parameters and renumbers only the residual
variables. This is the semantic environment of capture-free residual syntax. -/
def prefixEnvironment (fixed : List Ty) (tail : Nat → Ty) (name : Nat) : Ty :=
  if present : name < fixed.length then fixed[name] else tail (name - fixed.length)

/-- A later inference assignment cannot overwrite an already bound ground prefix. -/
theorem prefixEnvironment_fixed (fixed : List Ty) (tail : Nat → Ty) (name : Nat)
    (present : name < fixed.length) : prefixEnvironment fixed tail name = fixed[name] := by
  simp [prefixEnvironment, present]

/-- The first unbound variable is exactly the first residual parameter. -/
theorem prefixEnvironment_tail (fixed : List Ty) (tail : Nat → Ty) (name : Nat) :
    prefixEnvironment fixed tail (fixed.length + name) = tail name := by
  have absent : ¬ fixed.length + name < fixed.length := by omega
  simp [prefixEnvironment, absent]

/-- Unique complete residual inference establishes every ORIGINAL substituted
bound/query under the combined environment, not just the unbound suffix alone. -/
theorem inferred_prefix_constraints (fuel budget : Nat) (fixed : List Ty)
    (constraints : List (Expr × Expr)) (candidates : List (Nat → Ty))
    (accepted : inferBounded budget (fun tail => satisfies fuel constraints (prefixEnvironment fixed tail))
      candidates = .ok (.unique tail)) (bound : (a,b) ∈ constraints) :
    Subtype (substitute (prefixEnvironment fixed tail) a) (substitute (prefixEnvironment fixed tail) b) := by
  exact satisfies_sound _ _ _ (bounded_unique _ _ _ accepted).2 bound

/-- Direct mathematical arrow replacement: accepting a broader input and
returning a narrower output suffices, assuming the original behavior is valid. -/
theorem function_replacement (sourceIn targetIn sourceOut targetOut : Value → Prop)
    (input : ∀ v, targetIn v → sourceIn v) (output : ∀ v, sourceOut v → targetOut v)
    (f : Value → Value) (behavior : ∀ v, sourceIn v → sourceOut (f v)) :
    ∀ v, targetIn v → targetOut (f v) := fun _v h => output _ (behavior _ (input _ h))
end LeanPoo.Functional.PrototypeTypes
