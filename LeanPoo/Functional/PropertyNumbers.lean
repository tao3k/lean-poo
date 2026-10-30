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

end LeanPoo.Functional.PropertyTesting
