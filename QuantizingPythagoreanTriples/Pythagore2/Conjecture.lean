import Pythagore2.QPythagorean

/-! # Unimodality conjecture

The source states unimodality as an open conjecture. This is the only remaining axiom in
the Pythagore2 formalization setup.
-/

/-- A sequence of real numbers is unimodal if it increases to a maximum and then
decreases.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:409-412`. -/
def IsUnimodal (s : ℕ → ℝ) : Prop :=
  ∃ k : ℕ, (∀ i j, i ≤ j → j ≤ k → s i ≤ s j) ∧ (∀ i j, k ≤ i → i ≤ j → s j ≤ s i)

/-- The sequence of coefficients of a polynomial is unimodal. -/
def IsUnimodalPolynomial (P : PolyZ) : Prop :=
  IsUnimodal (fun i => (P.coeff i : ℝ))

/-- Unimodality conjecture for the constructed q-Pythagorean triples.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:426-429`. -/
axiom unimodality_conjecture (m n : ℕ) (hm : m > 0) (hn : n > 0) (hmn : m > n) :
    IsUnimodalPolynomial (qPythagoreanA m n) ∧
    IsUnimodalPolynomial (qPythagoreanB m n) ∧
    IsUnimodalPolynomial (qPythagoreanC m n)
