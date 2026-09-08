import Pythagore2.Classical
import Pythagore2.QRationals

open Polynomial

/-! # q-Pythagorean triples

This file contains the source construction of the q-Pythagorean polynomial triple and
the main theorem skeletons proving that the construction satisfies the required
conditions.
-/

/-! ## Matrix construction and trace -/

/-- The degenerate source matrix `X₀`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:562-570`. -/
noncomputable def X0q : QMatrix :=
  !![0, 0; 0, 1]

/-- The q-analogue of the Pythagorean matrix `X_{m/n}(q) = A_q X₀ A_q^T`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:855-869`. -/
noncomputable def qPythagoreanMatrix (m n : ℕ) : QMatrix :=
  qRationalMatrix m n * X0q * qRationalTransposeMatrix m n

/-- Trace of a 2-by-2 q-polynomial matrix. -/
noncomputable def qMatrixTrace (M : QMatrix) : PolyZ :=
  M 0 0 + M 1 1

/-- The trace of `X_{m/n}(q)` is `q N_{m/n}(q)^2 + D_{m/n}(q)^2`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:893-904`. -/
theorem qPythagoreanMatrix_trace (m n : ℕ) :
    qMatrixTrace (qPythagoreanMatrix m n) =
      (X : PolyZ) * (qRationalNum m n) ^ 2 + (qRationalDen m n) ^ 2 := by
  sorry

/-! ## Explicit formulas -/

/-- The polynomial `C_{m/n}(q) = q N_{m/n}(q)^2 + D_{m/n}(q)^2`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:948-952`. -/
noncomputable def qPythagoreanC (m n : ℕ) : PolyZ :=
  (X : PolyZ) * (qRationalNum m n) ^ 2 + (qRationalDen m n) ^ 2

/-- The polynomial
`A_{m/n}(q) = q N_{m/n}(q) N_{n/m}(q) + D_{m/n}(q) D_{n/m}(q)`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:966-973`. -/
noncomputable def qPythagoreanA (m n : ℕ) : PolyZ :=
  (X : PolyZ) * qRationalNum m n * qRationalNum n m +
    qRationalDen m n * qRationalDen n m

/-- The polynomial
`B_{m/n}(q) = N_{m/n}(q) D_{n/m}(q) - D_{m/n}(q) N_{n/m}(q)`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:974-977`. -/
noncomputable def qPythagoreanB (m n : ℕ) : PolyZ :=
  qRationalNum m n * qRationalDen n m - qRationalDen m n * qRationalNum n m

/-- The `n/1` family displayed after the main existence theorem.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:383-392`. -/
theorem qPythagorean_n_over_one_formulas (n : ℕ) (hn : 1 < n) :
    qPythagoreanA n 1 = qInteger (2 * n) ∧
    qPythagoreanB n 1 = qInteger (n + 1) * qInteger (n - 1) ∧
    qPythagoreanC n 1 = 1 + (X : PolyZ) * (qInteger n) ^ 2 := by
  sorry

/-- The reciprocal of `C_{m/n}` equals `q N_{n/m}² + D_{n/m}²`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:986-1001`. -/
theorem qPythagoreanC_reciprocal (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    reciprocalPolynomial (qPythagoreanC m n) =
      (X : PolyZ) * (qRationalNum n m) ^ 2 + (qRationalDen n m) ^ 2 := by
  sorry

/-- The explicit formulas `A`, `B`, and `C` satisfy the q-deformed Pythagoras equation.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:966-1022`. -/
theorem qPythagoreanTriple_satisfies_equation (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    IsQDeformedPythagoreanTriple (qPythagoreanA m n) (qPythagoreanB m n)
      (qPythagoreanC m n) := by
  sorry

/-- The q-Pythagorean triple corresponds to the classical triple
`(2mn, m²-n², m²+n²)` at `q = 1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:353-360`. -/
theorem qPythagoreanTriple_corresponds (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    CorrespondsToPythagoreanTriple
      (qPythagoreanA m n) (qPythagoreanB m n) (qPythagoreanC m n)
      (2 * m * n) (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) := by
  sorry

/-! ## Conditions Con1--Con3 -/

/-- The polynomials `A_{m/n}` and `B_{m/n}` are self-reciprocal when `m/n > 1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:1039-1080`. -/
theorem qPythagoreanTriple_selfReciprocal (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    IsSelfReciprocal (qPythagoreanA m n) ∧ IsSelfReciprocal (qPythagoreanB m n) := by
  sorry

/-- The polynomials `A_{m/n}`, `B_{m/n}`, and `C_{m/n}` are monic and have positive
coefficients when `m/n > 1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:1039-1095`. -/
theorem qPythagoreanTriple_monic_positive (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    IsFullyMonic (qPythagoreanA m n) ∧ IsFullyMonic (qPythagoreanB m n) ∧
    IsFullyMonic (qPythagoreanC m n) ∧
    HasPositiveCoefficients (qPythagoreanA m n) ∧
    HasPositiveCoefficients (qPythagoreanB m n) ∧
    HasPositiveCoefficients (qPythagoreanC m n) := by
  sorry

/-- The reciprocal of `C_{m/n}` is fully monic, completing Con3.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:347-350`. -/
theorem qPythagoreanC_reciprocal_monic (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    IsFullyMonic (reciprocalPolynomial (qPythagoreanC m n)) := by
  sorry

/-- The explicitly constructed triple satisfies all source conditions. -/
theorem qPythagoreanTriple_conditions (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    QDeformedSolutionConditions (qPythagoreanA m n) (qPythagoreanB m n)
      (qPythagoreanC m n) := by
  sorry

/-! ## Main existence theorem -/

/-- Main existence theorem: every standard Pythagorean triple has a q-deformation
satisfying the q-Pythagoras equation and conditions Con1--Con3, and corresponding to
the original triple at `q = 1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:373-379`. -/
theorem exists_qPythagoreanTriple (a b c : ℕ) (h : StandardPythagoreanTriple a b c) :
    ∃ A B C : PolyZ,
      IsQDeformedPythagoreanTriple A B C ∧
      QDeformedSolutionConditions A B C ∧
      CorrespondsToPythagoreanTriple A B C a b c := by
  sorry
