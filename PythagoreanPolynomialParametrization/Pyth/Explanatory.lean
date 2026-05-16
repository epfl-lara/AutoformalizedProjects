import Pyth.Basic

open MvPolynomial

/-! # Explanatory and cited source statements

This file records source-level material from Frisch--Vaserstein that is not used by
the main parametrization proof.
-/

/-- Source-cited result, `pyth.tex` lines 138--141: every set of integer tuples
parametrized by a single integer-valued polynomial tuple is parametrized by a finite
number of integer-coefficient polynomial tuples.

The paper cites this from Frisch's work and does not use it in the proof of the main
Pythagorean-triple parametrization theorem. -/
theorem single_intValued_parametrization_yields_finite_intPoly_parametrization
    {n k : ℕ} {F : Fin k → RatPoly n} {S : Set (Fin k → ℤ)}
    (hF : IntValuedTupleParametrizes F S) :
    ∃ (m : ℕ) (G : Fin m → Fin k → IntPoly n),
      FiniteIntPolyTupleParametrizes G S := by
  sorry

/-! ## The displayed integer-valued factorization example -/

/-- The falling factorial polynomial `x(x-1)...(x-k+1)` in `ℚ[x]`. -/
noncomputable def fallingFactorialRatPoly (k : ℕ) : RatPoly 1 :=
  Finset.prod (Finset.range k) fun i => X (0 : Fin 1) - C (i : ℚ)

/-- The binomial-coefficient polynomial `(x choose k)` over `ℚ[x]`, represented as
`(x(x-1)...(x-k+1))/k!`. -/
noncomputable def binomialRatPoly (k : ℕ) : RatPoly 1 :=
  C ((Nat.factorial k : ℚ)⁻¹) * fallingFactorialRatPoly k

/-- Source claim behind `pyth.tex` lines 185--186: the binomial-coefficient polynomial
is integer-valued. -/
theorem binomialRatPoly_intValued (k : ℕ) : IsIntValued (binomialRatPoly k) := by
  sorry

/-- The displayed identity `x(x-1)...(x-k+1) = k! * (x choose k)` from
`pyth.tex` lines 185--186. -/
theorem fallingFactorial_eq_factorial_mul_binomialRatPoly (k : ℕ) :
    fallingFactorialRatPoly k =
      C (Nat.factorial k : ℚ) * binomialRatPoly k := by
  sorry

/-- Source-level placeholder for `pyth.tex` lines 179--189: `Int(ℤ)` does not have
unique factorization into irreducibles. The displayed falling-factorial identity above
is the motivating example described in the paper. -/
theorem integerValued_polynomial_ring_not_uniqueFactorization :
    ¬ UniqueFactorizationMonoid (IntegerValuedPoly 1) := by
  sorry
