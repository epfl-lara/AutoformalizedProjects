import Pyth.Basic

/-! # Integer-coefficient obstruction

This file contains the paper's impossibility result for a single triple of
integer-coefficient polynomials.
-/

/-- There do not exist f,g,h ∈ ℤ[x₁,…,xₙ] for any n such that (f,g,h) parametrizes
the set of Pythagorean triples.

**Source proof sketch:** Suppose (f,g,h) parametrizes the PTs. As ℤ[x] is a UFD,
there exists d = gcd(g,h) (unique up to sign), which also divides f since f²+g²=h².
Let φ = f/d, ψ = g/d, θ = h/d. Then φ² = θ² - ψ² = (θ+ψ)(θ-ψ).
The gcd of (θ+ψ) and (θ-ψ) is either 1 or 2, but it cannot be 2 because there exist
PTs with odd first coordinate (e.g. (3,4,5)). Since they are coprime and their product
is a square, both are squares (up to sign, which we eliminate by adjusting the sign of d).
So θ+ψ = s² and θ-ψ = t², giving θ = (s²+t²)/2 and ψ = (s²-t²)/2.
Since s²-t² = (s+t)(s-t) is divisible by 2, it is actually divisible by 4,
so ψ is divisible by 2, contradicting the existence of PTs with odd second coordinate
(e.g. (4,3,5)). -/
theorem no_int_poly_parametrization :
    ¬∃ (n : ℕ) (f g h : IntPoly n), IntPolyParametrizes f g h pythagoreanTriples := by
  sorry
