import Pyth.IntegerValued

open MvPolynomial

/-! # Positive Pythagorean triples and 16-parameter variant

This file contains the positive-triple remark and the unrestricted 16-parameter
substitution obtained from the four-square theorem.
-/

/-- a_pos = y + (1+w)·z -/
noncomputable def a_pos_param : RatPoly 4 := y_var + (C (1 : ℚ) + w_var) * z_var

/-- b_pos = y -/
noncomputable def b_pos_param : RatPoly 4 := y_var

/-- c_pos = x + (1-w)²·x -/
noncomputable def c_pos_param : RatPoly 4 := x_var + (C (1 : ℚ) - w_var) ^ 2 * x_var

/-- f_pos = c_pos·(a_pos² - b_pos²)/2

In the paper: ((x+(1-w)²x)((y+(1+w)z)²-y²))/2 -/
noncomputable def f_pos_param : RatPoly 4 :=
  C (1 / 2 : ℚ) * c_pos_param * (a_pos_param ^ 2 - b_pos_param ^ 2)

/-- g_pos = c_pos·a_pos·b_pos

In the paper: (x+(1-w)²x)(y+(1+w)z)y -/
noncomputable def g_pos_param : RatPoly 4 := c_pos_param * a_pos_param * b_pos_param

/-- h_pos = c_pos·(a_pos² + b_pos²)/2

In the paper: ((x+(1-w)²x)((y+(1+w)z)²+y²))/2 -/
noncomputable def h_pos_param : RatPoly 4 :=
  C (1 / 2 : ℚ) * c_pos_param * (a_pos_param ^ 2 + b_pos_param ^ 2)

/-- f_pos_param is integer-valued.

**Prover notes:** Similar to f_param_intValued. For any integer tuple (x,y,z,w),
f_pos_param evaluates to ((x+(1-w)²x)((y+(1+w)z)²-y²))/2. Show this is always an integer. -/
theorem f_pos_param_intValued : IsIntValued f_pos_param := by
  sorry

/-- g_pos_param is integer-valued.

**Prover notes:** For any integer tuple (x,y,z,w), g_pos_param evaluates to
(x+(1-w)²x)(y+(1+w)z)y, which is clearly an integer product of integers. -/
theorem g_pos_param_intValued : IsIntValued g_pos_param := by
  sorry

/-- h_pos_param is integer-valued.

**Prover notes:** Similar to h_param_intValued. For any integer tuple (x,y,z,w),
h_pos_param evaluates to ((x+(1-w)²x)((y+(1+w)z)²+y²))/2. Show this is always an integer. -/
theorem h_pos_param_intValued : IsIntValued h_pos_param := by
  sorry

/-- Construct a 4-tuple input for polynomial evaluation from individual components. -/
def mkRatPolyInput4 (x' y' z' w' : ℤ) : Fin 4 → ℤ := fun i =>
  if i = 0 then x' else if i = 1 then y' else if i = 2 then z' else w'

/-- Parametrization of positive Pythagorean triples.

**Source statement:** The set of positive PTs is parametrized by
((x+(1-w)²x)((y+(1+w)z)²-y²)/2, (x+(1-w)²x)(y+(1+w)z)y, (x+(1-w)²x)((y+(1+w)z)²+y²)/2)
where x,y,z range through the positive integers and w through the non-negative integers.

**Source proof sketch:** As in the main theorem, positive PTs are precisely the triples
with positive integer coordinates in the range of T. Now T(a,b,c) is a positive triple
iff a,b,c are positive integers with a > b and either c ≡ 0 (mod 2) or a ≡ b (mod 2).
Such triples are parametrized by (y+(1+w)z, y, x+(1-w)²x) with x,y,z > 0 and w ≥ 0.
Substituting gives the parametrization. The 4-square theorem allows converting this to
a parametrization with 16 integer parameters. -/
theorem positive_triples_parametrization :
    IsIntValued f_pos_param ∧ IsIntValued g_pos_param ∧ IsIntValued h_pos_param ∧
    positivePythagoreanTriples =
      {(x, y, z) | ∃ (x' y' z' w' : ℤ),
        0 < x' ∧ 0 < y' ∧ 0 < z' ∧ 0 ≤ w' ∧
        ratPolyEval f_pos_param (mkRatPolyInput4 x' y' z' w') = (x : ℚ) ∧
        ratPolyEval g_pos_param (mkRatPolyInput4 x' y' z' w') = (y : ℚ) ∧
        ratPolyEval h_pos_param (mkRatPolyInput4 x' y' z' w') = (z : ℚ)} := by
  sorry

/-! ## 16-parameter parametrization via four-square theorem -/

/-- x_sub = x₁² + x₂² + x₃² + x₄² + 1 -/
noncomputable def x_sub : RatPoly 16 :=
  (X 0)^2 + (X 1)^2 + (X 2)^2 + (X 3)^2 + C (1 : ℚ)

/-- y_sub = y₁² + y₂² + y₃² + y₄² + 1 -/
noncomputable def y_sub : RatPoly 16 :=
  (X 4)^2 + (X 5)^2 + (X 6)^2 + (X 7)^2 + C (1 : ℚ)

/-- z_sub = z₁² + z₂² + z₃² + z₄² + 1 -/
noncomputable def z_sub : RatPoly 16 :=
  (X 8)^2 + (X 9)^2 + (X 10)^2 + (X 11)^2 + C (1 : ℚ)

/-- w_sub = w₁² + w₂² + w₃² + w₄² -/
noncomputable def w_sub : RatPoly 16 :=
  (X 12)^2 + (X 13)^2 + (X 14)^2 + (X 15)^2

/-- a_16 = y_sub + (1 + w_sub) * z_sub -/
noncomputable def a_16_param : RatPoly 16 := y_sub + (C (1 : ℚ) + w_sub) * z_sub

/-- b_16 = y_sub -/
noncomputable def b_16_param : RatPoly 16 := y_sub

/-- c_16 = x_sub + (1 - w_sub)² * x_sub -/
noncomputable def c_16_param : RatPoly 16 := x_sub + (C (1 : ℚ) - w_sub) ^ 2 * x_sub

/-- f_16 = c_16·(a_16² - b_16²)/2

In the paper: ((x_sub+(1-w_sub)²x_sub)((y_sub+(1+w_sub)z_sub)²-y_sub²))/2 -/
noncomputable def f_16_param : RatPoly 16 :=
  C (1 / 2 : ℚ) * c_16_param * (a_16_param ^ 2 - b_16_param ^ 2)

/-- g_16 = c_16·a_16·b_16

In the paper: (x_sub+(1-w_sub)²x_sub)(y_sub+(1+w_sub)z_sub)y_sub -/
noncomputable def g_16_param : RatPoly 16 := c_16_param * a_16_param * b_16_param

/-- h_16 = c_16·(a_16² + b_16²)/2

In the paper: ((x_sub+(1-w_sub)²x_sub)((y_sub+(1+w_sub)z_sub)²+y_sub²))/2 -/
noncomputable def h_16_param : RatPoly 16 :=
  C (1 / 2 : ℚ) * c_16_param * (a_16_param ^ 2 + b_16_param ^ 2)

/-- There exists a parametrization of positive Pythagorean triples by a single triple of
integer-valued polynomials in 16 variables (using Lagrange's four-square theorem).

**Source statement:** From the 4-variable parametrization of positive PTs, a parametrization
with integer parameters can be obtained by replacing w by w₁²+w₂²+w₃²+w₄² and x, y, z by
x₁²+x₂²+x₃²+x₄²+1, y₁²+y₂²+y₃²+y₄²+1, and z₁²+z₂²+z₃²+z₄²+1, respectively.

**Source proof sketch:** By Lagrange's four-square theorem, every non-negative integer is a
sum of four squares, and every positive integer is of the form (sum of four squares)+1.
Therefore the restricted parameters (x,y,z > 0 and w ≥ 0) in the 4-variable parametrization
can be replaced by unrestricted integer parameters via these substitutions, yielding a
parametrization with 16 integer parameters. -/
theorem exists_16_param_parametrization :
    IsIntValued f_16_param ∧ IsIntValued g_16_param ∧ IsIntValued h_16_param ∧
    positivePythagoreanTriples =
      {(x, y, z) | ∃ (a : Fin 16 → ℤ),
        ratPolyEval f_16_param a = (x : ℚ) ∧
        ratPolyEval g_16_param a = (y : ℚ) ∧
        ratPolyEval h_16_param a = (z : ℚ)} := by
  sorry
