import Pythagore2.Basic

open Polynomial

/-! # q-rationals

The previous draft modeled q-rationals by axioms. This file instead records the source
construction: choose an odd-length finite continued fraction expansion, replace the
classical generators by `R_q` and `L_q`, and extract the numerator and denominator from
the second column of the resulting matrix. The difficult facts about this construction
are stated as theorem skeletons, not axioms.
-/

/-! ## Continued fractions -/

/-- Value of a finite continued fraction `[a₁, ..., aₖ]`. -/
def finiteContinuedFractionValue : List ℕ → ℚ
  | [] => 0
  | a :: [] => (a : ℚ)
  | a :: rest => (a : ℚ) + (finiteContinuedFractionValue rest)⁻¹

/-- Odd-length continued fraction data for `m/n`.

The first coefficient is allowed to be zero, which covers rationals in `[0,1)`;
subsequent coefficients are positive. The paper fixes odd length for uniqueness.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:645-659`. -/
structure OddContinuedFractionExpansion (m n : ℕ) where
  coeffs : List ℕ
  oddLength : coeffs.length % 2 = 1
  tailPositive : ∀ a ∈ coeffs.tail, 0 < a
  represents : finiteContinuedFractionValue coeffs = (m : ℚ) / (n : ℚ)

/-- Every nonnegative rational has an odd-length finite continued fraction expansion.

This is a source-backed construction theorem, used only to choose concrete expansion data
for `qRationalNum` and `qRationalDen`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:645-659`. -/
theorem exists_oddContinuedFractionExpansion (m n : ℕ) :
    Nonempty (OddContinuedFractionExpansion m n) := by
  sorry

/-- A chosen odd-length continued fraction expansion for `m/n`. -/
noncomputable def chosenOddContinuedFractionExpansion (m n : ℕ) :
    OddContinuedFractionExpansion m n :=
  Classical.choice (exists_oddContinuedFractionExpansion m n)

/-! ## q-deformed matrix action -/

abbrev QMatrix := Matrix (Fin 2) (Fin 2) PolyZ

/-- The q-deformed right generator `R_q`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:722-735`. -/
noncomputable def Rq : QMatrix :=
  !![(X : PolyZ), 1; 0, 1]

/-- The q-deformed left generator `L_q`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:722-735`. -/
noncomputable def Lq : QMatrix :=
  !![(X : PolyZ), 0; (X : PolyZ), 1]

/-- Matrix word `R_q^a₁ L_q^a₂ R_q^a₃ ...` for a continued fraction. -/
noncomputable def qMatrixWordAux : ℕ → List ℕ → QMatrix
  | _, [] => 1
  | i, a :: rest =>
      ((if i % 2 = 0 then Rq else Lq) ^ a) * qMatrixWordAux (i + 1) rest

/-- Matrix word `A_q = R_q^a₁ L_q^a₂ R_q^a₃ ...`. -/
noncomputable def qMatrixWord (coeffs : List ℕ) : QMatrix :=
  qMatrixWordAux 0 coeffs

/-- The source's q-transposed word
`A_q^T = L_q^aₖ R_q^aₖ₋₁ ... L_q^a₁` for odd-length words.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:855-869`. -/
noncomputable def qTransposeMatrixWordAux : ℕ → List ℕ → QMatrix
  | _, [] => 1
  | i, a :: rest =>
      ((if i % 2 = 0 then Lq else Rq) ^ a) * qTransposeMatrixWordAux (i + 1) rest

/-- Source q-transposed matrix word associated with a continued fraction. -/
noncomputable def qTransposeMatrixWord (coeffs : List ℕ) : QMatrix :=
  qTransposeMatrixWordAux 0 coeffs.reverse

/-- Matrix `A_q` associated to the chosen continued fraction for `m/n`. -/
noncomputable def qRationalMatrix (m n : ℕ) : QMatrix :=
  qMatrixWord (chosenOddContinuedFractionExpansion m n).coeffs

/-- Matrix `A_q^T` associated to the chosen continued fraction for `m/n`. -/
noncomputable def qRationalTransposeMatrix (m n : ℕ) : QMatrix :=
  qTransposeMatrixWord (chosenOddContinuedFractionExpansion m n).coeffs

/-- The numerator of `[m/n]_q`, extracted from the second column of `A_q`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:691-712, 747-755`. -/
noncomputable def qRationalNum (m n : ℕ) : PolyZ :=
  qRationalMatrix m n 0 1

/-- The denominator of `[m/n]_q`, extracted from the second column of `A_q`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:691-712, 747-755`. -/
noncomputable def qRationalDen (m n : ℕ) : PolyZ :=
  qRationalMatrix m n 1 1

/-- The degree bound `d = max(deg N, deg D)` used in inverse q-rational formulas. -/
noncomputable def qRationalDegreeBound (m n : ℕ) : ℕ :=
  max (qRationalNum m n).natDegree (qRationalDen m n).natDegree

/-- The zero q-rational starts from `[0]_q = 0`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:698-702`. -/
theorem qRational_zero :
    qRationalNum 0 1 = 0 ∧ qRationalDen 0 1 = 1 := by
  sorry

/-- q-rationals evaluate to the classical numerator and denominator at `q = 1`. -/
theorem qRationalEvalOne (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    (qRationalNum m n).eval 1 = m ∧ (qRationalDen m n).eval 1 = n := by
  sorry

/-- Numerators and denominators of q-rationals are monic with nonnegative coefficients.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:713-716`. -/
theorem qRationalMonicNonnegative (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    (qRationalNum m n).Monic ∧ (qRationalDen m n).Monic ∧
    HasNonNegativeCoefficients (qRationalNum m n) ∧
    HasNonNegativeCoefficients (qRationalDen m n) := by
  sorry

/-- The inverse q-rational relation for numerators and denominators.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:800-820`. -/
theorem qRationalNumDenReciprocal (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    qRationalNum n m =
      reciprocalPolynomialWithDegree (qRationalDen m n) (qRationalDegreeBound m n) ∧
    qRationalDen n m =
      reciprocalPolynomialWithDegree (qRationalNum m n) (qRationalDegreeBound m n) := by
  sorry

/-- The source degree bound is the maximum of the numerator and denominator degrees. -/
theorem qRationalDegreeBoundMax (m n : ℕ) :
    qRationalDegreeBound m n = max (qRationalNum m n).natDegree (qRationalDen m n).natDegree := by
  rfl

/-- When `m/n > 1`, the numerator degree exceeds the denominator degree.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:1067`. -/
theorem qRationalDegreeInequality (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    (qRationalNum m n).natDegree > (qRationalDen m n).natDegree := by
  sorry

/-- The lower coefficient of `N_{n/m}` vanishes when `m/n > 1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:1086-1088`. -/
theorem qRationalNumLowerCoeffVanishes (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    (qRationalNum n m).coeff 0 = 0 := by
  sorry

/-- The constant term of every positive q-rational denominator is `1`. -/
theorem qRationalDenConstCoeffOne (m n : ℕ) (hm : m > 0) (hn : n > 0) :
    (qRationalDen m n).coeff 0 = 1 := by
  sorry

/-- The constant term of `N_{m/n}` is `1` when `m/n > 1`. -/
theorem qRationalNumConstCoeffOne (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    (qRationalNum m n).coeff 0 = 1 := by
  sorry

/-- Total positivity of q-rationals.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:780-794`. -/
theorem qRationalTotalPositivity (m n m' n' : ℕ)
    (hm : m > 0) (hn : n > 0) (hm' : m' > 0) (hn' : n' > 0)
    (h : (m : ℚ) / n > (m' : ℚ) / n') :
    HasPositiveCoefficients
      (qRationalNum m n * qRationalDen m' n' - qRationalDen m n * qRationalNum m' n') := by
  sorry
