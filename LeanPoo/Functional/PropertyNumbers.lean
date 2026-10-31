import LeanPoo.Functional.PropertyProducts
import Init.Data.Rat.Lemmas

/-! Bounded exact-ratio profiles reuse Lean's normalized Rat carrier. These laws
assume faithful Scheme exact arithmetic, primitive interval draws and pair codecs;
they do not verify floating representation, PRNG distribution or host arithmetic. -/
namespace LeanPoo.Functional.PropertyTesting

/-- Canonical numerator/denominator complexity, with zero as the least value. -/
def rationalWeight (value : Rat) : Nat := value.num.natAbs + value.den - 1

/-- Normalized parts give the existing pair codec's compact equality key. -/
def rationalKey (value : Rat) : Int × Nat := (value.num, value.den)

/-- Comparing canonical keys is exactly rational equality, not a weaker surrogate. -/
theorem rationalKey_eq (left right : Rat) : rationalKey left = rationalKey right ↔ left = right := by
  constructor
  · intro same
    exact Rat.ext (congrArg Prod.fst same) (congrArg Prod.snd same)
  · intro same
    cases same
    rfl

/-- Existing integer-pair transport rejects zero instead of inventing a default. -/
def rationalFromParts (parts : Int × Nat) : Option Rat :=
  if parts.2 = 0 then none else some (mkRat parts.1 parts.2)

/-- The signed magnitude comes from two existing finite integer/choice draws. -/
def rationalNumerator (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(magnitude : Int) else magnitude

/-- The denominator draw is offset from one, so normalization is always defined. -/
def rationalSample (negative : Bool) (magnitude offset : Nat) : Rat :=
  mkRat (rationalNumerator negative magnitude) (offset + 1)

/-- A malformed pair never decodes as zero or another fallback. -/
theorem rationalFromParts_zero (numerator : Int) : rationalFromParts (numerator, 0) = none := by
  simp [rationalFromParts]

/-- Canonical pair restoration preserves the exact original mathematical value. -/
theorem rationalFromParts_roundtrip (value : Rat) :
    rationalFromParts (value.num, value.den) = some value := by
  simp [rationalFromParts, value.den_nz, Rat.mkRat_self]

/-- Exact normalization cannot increase numerator magnitude. -/
theorem rational_normalize_num_bound (numerator : Int) (denominator : Nat)
    (positive : denominator ≠ 0) :
    (Rat.normalize numerator denominator positive).num.natAbs ≤ numerator.natAbs := by
  rw [Rat.num_normalize positive,
    Int.natAbs_ediv_of_dvd (Int.ofNat_dvd_left.2 (Nat.gcd_dvd_left ..)), Int.natAbs_natCast]
  exact Nat.div_le_self _ _

/-- Exact normalization cannot increase the positive denominator. -/
theorem rational_normalize_den_bound (numerator : Int) (denominator : Nat)
    (positive : denominator ≠ 0) :
    (Rat.normalize numerator denominator positive).den ≤ denominator := by
  rw [Rat.den_normalize positive]
  exact Nat.div_le_self _ _

/-- Primitive draw bounds transfer through actual normalization to the profile. -/
theorem rationalSample_bounds (negative : Bool) (magnitude offset size limit : Nat)
    (numeratorBound : magnitude ≤ size) (denominatorBound : offset < min limit (size + 1)) :
    (rationalSample negative magnitude offset).num.natAbs ≤ size ∧
      0 < (rationalSample negative magnitude offset).den ∧
      (rationalSample negative magnitude offset).den ≤ min limit (size + 1) := by
  have numerator := rational_normalize_num_bound (rationalNumerator negative magnitude)
    (offset + 1) (by omega)
  have denominator := rational_normalize_den_bound (rationalNumerator negative magnitude)
    (offset + 1) (by omega)
  have magnitudeEq : (rationalNumerator negative magnitude).natAbs = magnitude := by
    cases negative <;> simp [rationalNumerator]
  have normalized : rationalSample negative magnitude offset =
      Rat.normalize (rationalNumerator negative magnitude) (offset + 1) (by omega) := by
    simp [rationalSample, mkRat]
  refine ⟨?_, Nat.pos_of_ne_zero (rationalSample negative magnitude offset).den_nz, ?_⟩
  · rw [normalized]
    omega
  · rw [normalized]
    omega

/-- Zero-size magnitude produces exactly zero regardless of sign/denominator. -/
theorem rationalSample_zero (negative : Bool) (offset : Nat) : rationalSample negative 0 offset = 0 := by
  cases negative <;> simp [rationalSample, rationalNumerator, mkRat, Rat.normalize_zero]

/-- A denominator-one profile contains only integral canonical values. -/
theorem rationalSample_integral (negative : Bool) (magnitude : Nat) :
    (rationalSample negative magnitude 0).den = 1 := by
  have bound : (rationalSample negative magnitude 0).den ≤ 1 := by
    simp [rationalSample, mkRat]
  have positive := Nat.pos_of_ne_zero (rationalSample negative magnitude 0).den_nz
  omega

/-- Numerator proposals and positive denominator offsets share one canonical
normalization/filter policy. Raw finite integer proposal lists are parameters. -/
def rationalCandidates (best : Rat) (numerators : List Int) (denominatorOffsets : List Nat) : List Rat :=
  (List.eraseDupsBy (fun left right => rationalKey left == rationalKey right)
    ((numerators.map (fun numerator => mkRat numerator best.den)) ++
      denominatorOffsets.map (fun offset => mkRat best.num (offset + 1)))).filter
      (fun candidate => decide (rationalWeight candidate < rationalWeight best))

/-- Every retained candidate decreases canonical value complexity, not preimage rank. -/
theorem rationalCandidates_descent (best candidate : Rat) (numerators : List Int)
    (denominatorOffsets : List Nat) (member : candidate ∈ rationalCandidates best numerators denominatorOffsets) :
    rationalWeight candidate < rationalWeight best := by
  have accepted := (List.mem_filter.mp member).2
  simpa using accepted

/-- Different numerator/denominator spellings of the same value cannot fake descent. -/
theorem rationalCandidates_same_refused (best : Rat) (numerators : List Int) (denominatorOffsets : List Nat) :
    best ∉ rationalCandidates best numerators denominatorOffsets := by
  intro member
  have strict := rationalCandidates_descent best best numerators denominatorOffsets member
  omega

/-- Exact optional integer bounds; none denotes an omitted endpoint. -/
def integerInRange (lower upper : Option Int) (value : Int) : Prop :=
  (match lower with | none => True | some bound => bound ≤ value) ∧
  (match upper with | none => True | some bound => value ≤ bound)

/-- The nearest-to-zero endpoint, under nonempty interval admission. -/
def integerRangeAnchor (lower upper : Option Int) : Int :=
  if 0 < lower.getD 0 then lower.getD 0
  else if upper.getD 0 < 0 then upper.getD 0 else 0

/-- A nonempty declared interval admits its anchor, including half-unbounded ones. -/
theorem integerRangeAnchor_valid (lower upper : Option Int) (witness : Int)
    (nonempty : integerInRange lower upper witness) :
    integerInRange lower upper (integerRangeAnchor lower upper) := by
  cases lower <;> cases upper <;> simp_all [integerInRange, integerRangeAnchor] <;> omega

/-- Size clips a finite draw window around the admitted anchor. -/
def integerRangeWindow (lower upper : Option Int) (size : Nat) : Int × Int :=
  let anchor := integerRangeAnchor lower upper
  (match lower with | none => anchor - size | some bound => max bound (anchor - size),
   match upper with | none => anchor + size | some bound => min bound (anchor + size))

/-- No admitted interval can yield an empty draw window. -/
theorem integerRangeWindow_anchor (lower upper : Option Int) (size : Nat) (witness : Int)
    (nonempty : integerInRange lower upper witness) :
    (integerRangeWindow lower upper size).1 ≤ integerRangeAnchor lower upper ∧
      integerRangeAnchor lower upper ≤ (integerRangeWindow lower upper size).2 := by
  have admitted := integerRangeAnchor_valid lower upper witness nonempty
  cases lower <;> cases upper <;> simp_all [integerRangeWindow, integerInRange] <;> omega

/-- Primitive inclusive-window draws stay in the declared domain and size segment. -/
theorem integerRangeWindow_sound (lower upper : Option Int) (size : Nat) (value : Int)
    (lo : (integerRangeWindow lower upper size).1 ≤ value)
    (hi : value ≤ (integerRangeWindow lower upper size).2) :
    integerInRange lower upper value ∧
      integerRangeAnchor lower upper - size ≤ value ∧ value ≤ integerRangeAnchor lower upper + size := by
  cases lower <;> cases upper <;> simp_all [integerRangeWindow, integerInRange] <;> omega

/-- A size-zero admitted draw is exactly the anchor, not an out-of-domain zero. -/
theorem integerRangeWindow_zero (lower upper : Option Int) (value : Int)
    (lo : (integerRangeWindow lower upper 0).1 ≤ value)
    (hi : value ≤ (integerRangeWindow lower upper 0).2) :
    value = integerRangeAnchor lower upper := by
  have bounded := integerRangeWindow_sound lower upper 0 value lo hi
  omega

/-- Window width is at most twice size, independently of endpoint bit widths. -/
theorem integerRangeWindow_width (lower upper : Option Int) (size : Nat) :
    (integerRangeWindow lower upper size).2 - (integerRangeWindow lower upper size).1 ≤ 2 * (size : Int) := by
  cases lower <;> cases upper <;> simp_all [integerRangeWindow] <;> omega

/-- Positive-distance integer-shrinks is the existing zero/half/predecessor policy. -/
def rangeMagnitudeShrinks (distance : Nat) : List Nat :=
  if distance = 0 then [] else [0, distance / 2, distance - 1].eraseDups

/-- Every existing magnitude proposal strictly reduces its positive rank. -/
theorem rangeMagnitudeShrinks_descent (distance smaller : Nat)
    (member : smaller ∈ rangeMagnitudeShrinks distance) : smaller < distance := by
  by_cases zero : distance = 0
  · simp [rangeMagnitudeShrinks, zero] at member
  · have choices : smaller = 0 ∨ smaller = distance / 2 ∨ smaller = distance - 1 := by
      simpa [rangeMagnitudeShrinks, zero] using member
    rcases choices with rfl | rfl | rfl
    · omega
    · exact Nat.div_lt_self (by omega) (by decide)
    · omega

/-- Reconstruct a value from anchor, polarity and natural distance. -/
def integerAt (anchor : Int) (negative : Bool) (distance : Nat) : Int :=
  if negative then anchor - distance else anchor + distance

/-- Reconstruction has exactly the intended natural-valued measure. -/
theorem integerAt_distance (anchor : Int) (negative : Bool) (distance : Nat) :
    (integerAt anchor negative distance - anchor).natAbs = distance := by
  have offset : integerAt anchor negative distance - anchor =
      if negative then -(distance : Int) else (distance : Int) := by
    cases negative <;> simp only [integerAt, Bool.false_eq_true, ite_false, ite_true] <;> omega
  rw [offset]
  cases negative <;> simp

/-- Exact sign/magnitude decomposition preserves the original exact integer. -/
theorem integerAt_split (anchor value : Int) :
    integerAt anchor (decide (value < anchor)) (value - anchor).natAbs = value := by
  by_cases negative : value < anchor
  · have cast := Int.ofNat_natAbs_of_nonpos (a := value - anchor) (by omega)
    simp only [integerAt, negative, decide_true, ite_true]
    omega
  · have cast := Int.ofNat_natAbs_of_nonneg (a := value - anchor) (by omega)
    simp only [integerAt, negative, decide_false, Bool.false_eq_true, ite_false]
    omega

/-- Moving toward an admitted anchor cannot leave the closed integer interval. -/
theorem integerAt_segment (lower upper : Option Int) (anchor : Int) (negative : Bool)
    (distance smaller : Nat) (anchorValid : integerInRange lower upper anchor)
    (originalValid : integerInRange lower upper (integerAt anchor negative distance))
    (closer : smaller ≤ distance) : integerInRange lower upper (integerAt anchor negative smaller) := by
  cases negative <;> cases lower <;> cases upper <;> simp_all [integerInRange, integerAt] <;> omega

/-- Shift the existing magnitude neighborhood without filtering or resampling. -/
def integerRangeCandidates (anchor value : Int) : List Int :=
  (rangeMagnitudeShrinks (value - anchor).natAbs).map
    (integerAt anchor (decide (value < anchor)))

/-- Every actual translated proposal stays in the interval and strictly decreases. -/
theorem integerRangeCandidates_sound (lower upper : Option Int) (value candidate : Int)
    (valid : integerInRange lower upper value)
    (member : candidate ∈ integerRangeCandidates (integerRangeAnchor lower upper) value) :
    integerInRange lower upper candidate ∧
      (candidate - integerRangeAnchor lower upper).natAbs < (value - integerRangeAnchor lower upper).natAbs := by
  obtain ⟨smaller, child, rfl⟩ := List.mem_map.mp member
  have descent := rangeMagnitudeShrinks_descent _ smaller child
  refine ⟨integerAt_segment lower upper _ _ _ smaller
    (integerRangeAnchor_valid lower upper value valid) ?_ (Nat.le_of_lt descent), ?_⟩
  · simpa only [integerAt_split] using valid
  · simpa only [integerAt_distance] using descent

/-- An anchor is a terminal value; zero size never invents a shrink toward zero. -/
theorem integerRangeCandidates_anchor (anchor : Int) : integerRangeCandidates anchor anchor = [] := by
  simp [integerRangeCandidates, rangeMagnitudeShrinks]

end LeanPoo.Functional.PropertyTesting
