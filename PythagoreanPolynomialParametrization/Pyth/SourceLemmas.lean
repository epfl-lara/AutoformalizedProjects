import Pyth.Basic

/-! # Source-level handoff lemmas

These declarations mirror the intermediate claims used in the paper's proofs. They are
kept separate from the explicit polynomial witnesses so each proof obligation has a
small, source-located target.
-/

/-- The rational map
T(a,b,c) = (c(a²-b²)/2, cab, c(a²+b²)/2)
used in the proof of the main parametrization theorem. -/
def TMap (a b c : ℤ) : ℚ × ℚ × ℚ :=
  ((c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2,
    (c : ℚ) * (a : ℚ) * (b : ℚ),
    (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2)

/-- A value of `TMap` is integral when all three rational coordinates are integers. -/
def IsIntegralTValue (a b c : ℤ) : Prop :=
  ∃ x y z : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ))

/-- The paper's parity condition for `T(a,b,c)` to have integer coordinates:
`c` is even or `a` and `b` have the same parity. -/
def PaperParityCondition (a b c : ℤ) : Prop :=
  Even c ∨ Even (a - b)

/-- Positive parameters for the paper's positive-triple variant of `T(a,b,c)`. -/
def PositiveTParameters (a b c : ℤ) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ b < a ∧ PaperParityCondition a b c

/-- The introductory source claim: every Pythagorean triple is covered by one of two
integer-coefficient polynomial families, and every value of those families is a
Pythagorean triple. -/
theorem pythagoreanTriple_two_integer_polynomial_families (x y z : ℤ) :
    IsPythagoreanTriple x y z ↔
      ∃ a b c : ℤ,
        (x = c * (a ^ 2 - b ^ 2) ∧
          y = (2 : ℤ) * c * a * b ∧
          z = c * (a ^ 2 + b ^ 2)) ∨
        (x = (2 : ℤ) * c * a * b ∧
          y = c * (a ^ 2 - b ^ 2) ∧
          z = c * (a ^ 2 + b ^ 2)) := by
  sorry

/-- Source proof handoff lemma: the set of Pythagorean triples is exactly the set of
integer triples in the range of `TMap`. -/
theorem pythagorean_iff_mem_TMap_range (x y z : ℤ) :
    IsPythagoreanTriple x y z ↔
      ∃ a b c : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
  sorry

/-- Source proof handoff lemma: `T(a,b,c)` has integer coordinates iff the paper's
parity condition holds. -/
theorem TMap_integral_iff_parity (a b c : ℤ) :
    IsIntegralTValue a b c ↔ PaperParityCondition a b c := by
  sorry

/-- Source proof handoff lemma: the parity condition is parametrized by
`(y + zw, z - yw, 2x - xw)`. -/
theorem parity_condition_parametrized (a b c : ℤ) :
    PaperParityCondition a b c ↔
      ∃ x y z w : ℤ,
        a = y + z * w ∧
        b = z - y * w ∧
        c = (2 : ℤ) * x - x * w := by
  sorry

/-- Source proof handoff lemma for the positive remark: the restricted positive
parameters are parametrized by `(y + (1+w)z, y, x + (1-w)^2 x)`. -/
theorem positive_T_parameters_parametrized (a b c : ℤ) :
    PositiveTParameters a b c ↔
      ∃ x y z w : ℤ,
        0 < x ∧ 0 < y ∧ 0 < z ∧ 0 ≤ w ∧
        a = y + ((1 : ℤ) + w) * z ∧
        b = y ∧
        c = x + ((1 : ℤ) - w) ^ 2 * x := by
  sorry

/-- Lagrange four-square handoff: every nonnegative integer is a sum of four squares. -/
theorem int_nonneg_iff_four_squares (n : ℤ) :
    0 ≤ n ↔ ∃ a b c d : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  sorry

/-- Four-square corollary used by the 16-parameter substitution: every positive integer
is one plus a sum of four squares. -/
theorem int_positive_iff_four_squares_add_one (n : ℤ) :
    0 < n ↔ ∃ a b c d : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 1 := by
  sorry
