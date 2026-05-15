import Mathlib

open MvPolynomial

/-! # Basic definitions for Pythagorean polynomial parametrizations

This file contains the shared definitions used by the Frisch--Vaserstein
formalization setup.
-/

/-- A triple of integers (x,y,z) is a Pythagorean triple if x² + y² = z². -/
def IsPythagoreanTriple (x y z : ℤ) : Prop := x^2 + y^2 = z^2

/-- The set of all Pythagorean triples. -/
def pythagoreanTriples : Set (ℤ × ℤ × ℤ) := {(x, y, z) | IsPythagoreanTriple x y z}

/-- The set of all positive Pythagorean triples (x,y,z > 0). -/
def positivePythagoreanTriples : Set (ℤ × ℤ × ℤ) :=
  {(x, y, z) | 0 < x ∧ 0 < y ∧ 0 < z ∧ IsPythagoreanTriple x y z}

/-- Multivariate polynomials with integer coefficients in n variables. -/
abbrev IntPoly (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- Multivariate polynomials with rational coefficients in n variables. -/
abbrev RatPoly (n : ℕ) := MvPolynomial (Fin n) ℚ

/-- A rational-coefficient polynomial is integer-valued if it evaluates to an integer
at every integer tuple. -/
def IsIntValued {n : ℕ} (p : RatPoly n) : Prop :=
  ∀ a : Fin n → ℤ, ∃ k : ℤ, eval (fun i => (a i : ℚ)) p = (k : ℚ)

/-- Evaluate an integer-coefficient polynomial at an integer tuple. -/
noncomputable def intPolyEval {n : ℕ} (p : IntPoly n) (a : Fin n → ℤ) : ℤ :=
  eval a p

/-- Evaluate a rational-coefficient polynomial at an integer tuple. -/
noncomputable def ratPolyEval {n : ℕ} (p : RatPoly n) (a : Fin n → ℤ) : ℚ :=
  eval (fun i => (a i : ℚ)) p

/-- A triple of integer-coefficient polynomials parametrizes a set S ⊆ ℤ³
if S equals the image of the polynomial map ℤⁿ → ℤ³. -/
def IntPolyParametrizes {n : ℕ} (f g h : IntPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    intPolyEval f a = x ∧ intPolyEval g a = y ∧ intPolyEval h a = z}

/-- A triple of rational-coefficient polynomials parametrizes a set S ⊆ ℤ³
if each is integer-valued and S equals the image of the polynomial map. -/
def IntValuedParametrizes {n : ℕ} (f g h : RatPoly n) (S : Set (ℤ × ℤ × ℤ)) : Prop :=
  IsIntValued f ∧ IsIntValued g ∧ IsIntValued h ∧
  S = {(x, y, z) | ∃ a : Fin n → ℤ,
    ratPolyEval f a = (x : ℚ) ∧ ratPolyEval g a = (y : ℚ) ∧ ratPolyEval h a = (z : ℚ)}
