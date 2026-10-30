import LeanPoo.Functional.PropertyNumbers

open LeanPoo.Functional.PropertyTesting

-- Symbolic controls reuse proved normalization laws without kernel evaluation
-- of a concrete rational arithmetic decision procedure.
example : rationalSample true 0 7 = 0 := rationalSample_zero true 7
example : rationalFromParts (1, 0) = none := rationalFromParts_zero 1
example (value : Rat) : rationalFromParts (value.num, value.den) = some value :=
  rationalFromParts_roundtrip value

-- Common-factor aliases are equal by the standard normalization law, without
-- running its proof-producing arithmetic decision procedure on literal ratios.
example (numerator : Int) (denominator factor : Nat)
    (positive : denominator ≠ 0) (nonzero : factor ≠ 0) :
    Rat.normalize (numerator * factor) (denominator * factor) (Nat.mul_ne_zero positive nonzero) =
      Rat.normalize numerator denominator positive := Rat.normalize_mul_right positive nonzero

-- Canonical key comparison preserves actual rational equality.
example (left right : Rat) (same : rationalKey left = rationalKey right) : left = right :=
  (rationalKey_eq left right).mp same

-- Raw aliases of the best value cannot enter the decreasing neighborhood.
example (best : Rat) : best ∉ rationalCandidates best [0, 1] [0, 1, 3] :=
  rationalCandidates_same_refused best [0, 1] [0, 1, 3]

-- Every actual candidate decreases the same canonical rank used by replay.
example (best candidate : Rat) (member : candidate ∈ rationalCandidates best [0, 1] [0, 1, 3]) :
    rationalWeight candidate < rationalWeight best :=
  rationalCandidates_descent best candidate [0, 1] [0, 1, 3] member
