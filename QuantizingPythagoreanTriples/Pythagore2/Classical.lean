import Pythagore2.Basic

/-! # Classical Pythagorean triples

This file records the classical inputs used by the q-deformation construction.
-/

/-- Euclid's formula for standard Pythagorean triples.

For every standard Pythagorean triple, there exist coprime positive integers `m,n`
with `m > n` such that
`a = 2mn`, `b = m² - n²`, and `c = m² + n²`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:233-238`. -/
theorem euclid_formula_standard (a b c : ℕ) (h : StandardPythagoreanTriple a b c) :
    ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ m > n ∧ Nat.Coprime m n ∧
      a = 2 * m * n ∧ b = m ^ 2 - n ^ 2 ∧ c = m ^ 2 + n ^ 2 := by
  sorry

/-- The Euclid formula really gives a Pythagorean triple in the source range `m >= n`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:219-230`. -/
theorem euclid_formula_is_pythagorean (m n : ℕ) (hmn : n ≤ m) :
    (2 * m * n) ^ 2 + (m ^ 2 - n ^ 2) ^ 2 = (m ^ 2 + n ^ 2) ^ 2 := by
  sorry
