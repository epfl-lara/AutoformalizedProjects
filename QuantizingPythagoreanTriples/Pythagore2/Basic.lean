import Mathlib

open Polynomial

/-! # Basic definitions for quantized Pythagorean triples

This file contains the shared definitions from Mathevet--Morier-Genoud--Ovsienko,
"Quantizing Pythagorean triples".
-/

abbrev PolyZ := Polynomial ℤ

/-! ## Standard Pythagorean triples -/

/-- A Pythagorean triple `(a,b,c)` is *standard* if:
- `a`, `b`, and `c` are positive integers satisfying `a² + b² = c²`;
- `gcd(a,b,c)` is `1` or `2`;
- if the gcd is `1`, then `a` is even;
- if the gcd is `2`, then `a/2` is odd.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:189-217`. -/
def StandardPythagoreanTriple (a b c : ℕ) : Prop :=
  a > 0 ∧ b > 0 ∧ c > 0 ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
  (Nat.gcd (Nat.gcd a b) c = 1 ∨ Nat.gcd (Nat.gcd a b) c = 2) ∧
  (Nat.gcd (Nat.gcd a b) c = 1 → Even a) ∧
  (Nat.gcd (Nat.gcd a b) c = 2 → Odd (a / 2))

/-! ## q-integers and reciprocal polynomials -/

/-- The q-analogue of a positive integer:
`[n]_q = 1 + q + q² + ... + q^(n-1)`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:298-301`. -/
noncomputable def qInteger (n : ℕ) : PolyZ :=
  ∑ i ∈ Finset.range n, (X : PolyZ) ^ i

/-- The reciprocal of a polynomial `C`:
`C*(q) = q^(deg C) C(q⁻¹)`.

For `C = ∑ c_i q^i`, this is encoded as `∑ c_i q^(deg C - i)`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:270-274`. -/
noncomputable def reciprocalPolynomial {R : Type*} [CommRing R] (C : Polynomial R) :
    Polynomial R :=
  ∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i • (X : Polynomial R) ^ (C.natDegree - i)

/-- Reciprocal with an explicitly supplied degree `d`:
`q^d C(q⁻¹) = ∑ c_i q^(d-i)`.

This is the form used for the numerator/denominator inverse relation.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:811-820`. -/
noncomputable def reciprocalPolynomialWithDegree {R : Type*} [CommRing R]
    (C : Polynomial R) (d : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range (C.natDegree + 1), C.coeff i • (X : Polynomial R) ^ (d - i)

/-- A polynomial is self-reciprocal, or palindromic. -/
def IsSelfReciprocal {R : Type*} [CommRing R] (P : Polynomial R) : Prop :=
  reciprocalPolynomial P = P

/-- A polynomial has no negative integer coefficients. -/
def HasNonNegativeCoefficients (P : PolyZ) : Prop :=
  ∀ i, P.coeff i ≥ 0

/-- A polynomial has positive integer coefficients in the paper's combinatorial sense:
it is nonzero and has no negative coefficients. Zeros outside its support are ignored. -/
def HasPositiveCoefficients (P : PolyZ) : Prop :=
  P ≠ 0 ∧ HasNonNegativeCoefficients P

/-! ## q-deformed Pythagoras equation -/

/-- Three polynomials satisfy the q-deformed Pythagoras equation
`A(q)² + q B(q)² = C(q) C*(q)`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:265-274`. -/
def IsQDeformedPythagoreanTriple (A B C : PolyZ) : Prop :=
  A ^ 2 + (X : PolyZ) * B ^ 2 = C * reciprocalPolynomial C

/-- A polynomial triple corresponds to a classical Pythagorean triple when evaluation at
`q = 1` gives the classical coordinates.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:353-360`. -/
def CorrespondsToPythagoreanTriple (A B C : PolyZ) (a b c : ℕ) : Prop :=
  A.eval 1 = a ∧ B.eval 1 = b ∧ C.eval 1 = c

/-- The paper's monicity condition: leading and lower-degree coefficients are both `1`.

Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:347-350`. -/
def IsFullyMonic (P : PolyZ) : Prop :=
  P.Monic ∧ P.coeff 0 = 1

/-- Conditions Con1, Con2, and Con3 from the paper. -/
structure QDeformedSolutionConditions (A B C : PolyZ) : Prop where
  positiveCoeffs :
    HasPositiveCoefficients A ∧ HasPositiveCoefficients B ∧ HasPositiveCoefficients C
  selfReciprocalAB : IsSelfReciprocal A ∧ IsSelfReciprocal B
  monicABC :
    IsFullyMonic A ∧ IsFullyMonic B ∧ IsFullyMonic C ∧ IsFullyMonic (reciprocalPolynomial C)
