import Pyth.SourceLemmas

open MvPolynomial

/-! # Integer-valued parametrization of all Pythagorean triples

This file contains the explicit four-variable integer-valued polynomial triple from
Frisch and Vaserstein's main theorem.
-/

/-- Variable x (index 0) in the 4-variable rational polynomial ring. -/
noncomputable def x_var : RatPoly 4 := X 0

/-- Variable y (index 1) in the 4-variable rational polynomial ring. -/
noncomputable def y_var : RatPoly 4 := X 1

/-- Variable z (index 2) in the 4-variable rational polynomial ring. -/
noncomputable def z_var : RatPoly 4 := X 2

/-- Variable w (index 3) in the 4-variable rational polynomial ring. -/
noncomputable def w_var : RatPoly 4 := X 3

/-- a = y + z·w -/
noncomputable def a_param : RatPoly 4 := y_var + z_var * w_var

/-- b = z - y·w -/
noncomputable def b_param : RatPoly 4 := z_var - y_var * w_var

/-- c = 2x - x·w -/
noncomputable def c_param : RatPoly 4 := C (2 : ℚ) * x_var - x_var * w_var

/-- f = c·(a² - b²)/2

In the paper: ((2x-xw)((y+zw)²-(z-yw)²))/2 -/
noncomputable def f_param : RatPoly 4 := C (1 / 2 : ℚ) * c_param * (a_param ^ 2 - b_param ^ 2)

/-- g = c·a·b

In the paper: (2x-xw)(y+zw)(z-yw) -/
noncomputable def g_param : RatPoly 4 := c_param * a_param * b_param

/-- h = c·(a² + b²)/2

In the paper: ((2x-xw)((y+zw)²+(z-yw)²))/2 -/
noncomputable def h_param : RatPoly 4 := C (1 / 2 : ℚ) * c_param * (a_param ^ 2 + b_param ^ 2)

/-- f_param is integer-valued.

**Prover notes:** Expand the definition of f_param and IsIntValued. For any integer tuple
(x,y,z,w), f_param evaluates to ((2x-xw)((y+zw)²-(z-yw)²))/2. Show this is always an integer
by case analysis on the parity of w: if w is even, then 2x-xw is even; if w is odd, then
(y+zw) and (z-yw) have the same parity, so their squares differ by a multiple of 4, making
the product divisible by 2. -/
theorem f_param_intValued : IsIntValued f_param := by
  sorry

/-- g_param is integer-valued.

**Prover notes:** Expand the definition of g_param and IsIntValued. For any integer tuple
(x,y,z,w), g_param evaluates to (2x-xw)(y+zw)(z-yw), which is clearly an integer product
of integers. -/
theorem g_param_intValued : IsIntValued g_param := by
  sorry

/-- h_param is integer-valued.

**Prover notes:** Expand the definition of h_param and IsIntValued. For any integer tuple
(x,y,z,w), h_param evaluates to ((2x-xw)((y+zw)²+(z-yw)²))/2. Show this is always an integer
by case analysis on the parity of w: if w is even, then 2x-xw is even; if w is odd, then
(y+zw) and (z-yw) have the same parity, so the sum of their squares is even. -/
theorem h_param_intValued : IsIntValued h_param := by
  sorry

/-- There exist f,g,h ∈ Int(ℤ⁴) such that (f,g,h) parametrizes the set of Pythagorean triples.

**Source proof sketch:** Every primitive PT (x,y,z) with gcd(x,y,z)=1 and z>0 is either of
the form T₁(a,b) = (a²-b², 2ab, a²+b²) or T₂(a,b) = (2ab, a²-b², a²+b²) with a,b ∈ ℤ.
Since 2·T₂(a,b) = T₁(a+b, a-b), every primitive PT is of the form c·T₁(a,b)/2 with
c ∈ {1,2} and a,b ∈ ℤ. Let T(a,b,c) = (c(a²-b²)/2, cab, c(a²+b²)/2).
Then every PT is T(a,b,c) for some a,b,c ∈ ℤ. Also, every T(a,b,c) is a rational solution
of x²+y²=z². The set of PTs is precisely the integer triples in the range of T.
Now T(a,b,c) ∈ ℤ³ iff c ≡ 0 (mod 2) or a ≡ b (mod 2). Triples satisfying this condition
are parametrized by (y+zw, z-yw, 2x-xw). If w is even then c ≡ 0 (mod 2);
if w is odd then a ≡ b (mod 2); and all such triples occur for some (x,y,z,w) ∈ ℤ⁴
(as seen by setting w=0 or w=1). Substituting yields the parametrization. -/
theorem exists_int_valued_parametrization :
    IntValuedParametrizes f_param g_param h_param pythagoreanTriples := by
  sorry
