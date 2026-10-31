import Std

/-! Finite rank-one prototype types. This advances the type-system future work in
Appendices C/D: explicit Self <: Super constraints, structural variance and finite
candidate inference. Host recognizers, effect behavior and mutable slot writes
are not identified with this semantic replacement relation. -/
namespace LeanPoo.Functional.PrototypeTypes

/-- The admitted scalar vocabulary has one proper numeric inclusion. -/
inductive Atom where
  | bool | integer | uint | string | symbol | keyword
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
  | booleanEnum (values : List Bool)
  | scalarEnum (family : Atom) (values : List Nat)
  | maybe (element : Ty) | orFalse (element : Ty)
  | function (outputs inputs : List Ty)
  | pair (left right : Ty) | map (key value : Ty)
  | sum (tags : List Nat) (payloads : List Ty) | union (branches : List Ty)
  deriving Repr


end LeanPoo.Functional.PrototypeTypes
