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
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  have hpar : PaperParityCondition A B Cc := by
    exact (parity_condition_parametrized A B Cc).mpr ⟨x, y, z, w, rfl, rfl, rfl⟩
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨fx, ?_⟩
  have hfcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 - (B : ℚ) ^ 2) / 2 = (fx : ℚ) := by
    simpa [TMap] using congrArg Prod.fst hT
  rw [← hfcoord]
  simp [f_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, A, B, Cc]
  ring

/-- g_param is integer-valued.

**Prover notes:** Expand the definition of g_param and IsIntValued. For any integer tuple
(x,y,z,w), g_param evaluates to (2x-xw)(y+zw)(z-yw), which is clearly an integer product
of integers. -/
theorem g_param_intValued : IsIntValued g_param := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  refine ⟨Cc * A * B, ?_⟩
  simp [g_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, A, B, Cc]
  ring

/-- h_param is integer-valued.

**Prover notes:** Expand the definition of h_param and IsIntValued. For any integer tuple
(x,y,z,w), h_param evaluates to ((2x-xw)((y+zw)²+(z-yw)²))/2. Show this is always an integer
by case analysis on the parity of w: if w is even, then 2x-xw is even; if w is odd, then
(y+zw) and (z-yw) have the same parity, so the sum of their squares is even. -/
theorem h_param_intValued : IsIntValued h_param := by
  intro v
  let x : ℤ := v (0 : Fin 4)
  let y : ℤ := v (1 : Fin 4)
  let z : ℤ := v (2 : Fin 4)
  let w : ℤ := v (3 : Fin 4)
  let A : ℤ := y + z * w
  let B : ℤ := z - y * w
  let Cc : ℤ := (2 : ℤ) * x - x * w
  have hpar : PaperParityCondition A B Cc := by
    exact (parity_condition_parametrized A B Cc).mpr ⟨x, y, z, w, rfl, rfl, rfl⟩
  rcases (TMap_integral_iff_parity A B Cc).mpr hpar with ⟨fx, gy, hz, hT⟩
  refine ⟨hz, ?_⟩
  have hhcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 + (B : ℚ) ^ 2) / 2 = (hz : ℚ) := by
    simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
  rw [← hhcoord]
  simp [h_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, A, B, Cc]
  ring

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
  refine ⟨f_param_intValued, g_param_intValued, h_param_intValued, ?_⟩
  ext p
  rcases p with ⟨x, y, z⟩
  constructor
  · intro hp
    have hpy : IsPythagoreanTriple x y z := by
      simpa [pythagoreanTriples] using hp
    rcases (pythagorean_iff_mem_TMap_range x y z).mp hpy with ⟨a, b, c, hT⟩
    have hIntegral : IsIntegralTValue a b c := ⟨x, y, z, hT⟩
    have hpar : PaperParityCondition a b c := (TMap_integral_iff_parity a b c).mp hIntegral
    rcases (parity_condition_parametrized a b c).mp hpar with
      ⟨x0, y0, z0, w0, ha, hb, hc⟩
    let v : Fin 4 → ℤ := fun i =>
      if i = (0 : Fin 4) then x0 else
      if i = (1 : Fin 4) then y0 else
      if i = (2 : Fin 4) then z0 else w0
    refine ⟨v, ?_, ?_, ?_⟩
    · have hfcoord : (c : ℚ) * ((a : ℚ) ^ 2 - (b : ℚ) ^ 2) / 2 = (x : ℚ) := by
        simpa [TMap] using congrArg Prod.fst hT
      rw [← hfcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, f_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, v]
      ring
    · have hgcoord : (c : ℚ) * (a : ℚ) * (b : ℚ) = (y : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.1) hT
      rw [← hgcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, g_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, v]
    · have hhcoord : (c : ℚ) * ((a : ℚ) ^ 2 + (b : ℚ) ^ 2) / 2 = (z : ℚ) := by
        simpa [TMap] using congrArg (fun p : ℚ × ℚ × ℚ => p.2.2) hT
      rw [← hhcoord]
      rw [ha, hb, hc]
      simp [ratPolyEval, h_param, c_param, a_param, b_param, x_var, y_var, z_var, w_var, v]
      ring
  · rintro ⟨v, hf, hg, hh⟩
    let x0 : ℤ := v (0 : Fin 4)
    let y0 : ℤ := v (1 : Fin 4)
    let z0 : ℤ := v (2 : Fin 4)
    let w0 : ℤ := v (3 : Fin 4)
    let A : ℤ := y0 + z0 * w0
    let B : ℤ := z0 - y0 * w0
    let Cc : ℤ := (2 : ℤ) * x0 - x0 * w0
    have hfcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 - (B : ℚ) ^ 2) / 2 = (x : ℚ) := by
      rw [← hf]
      simp [ratPolyEval, f_param, c_param, a_param, b_param,
        x_var, y_var, z_var, w_var, A, B, Cc, x0, y0, z0, w0]
      ring
    have hgcoord : (Cc : ℚ) * (A : ℚ) * (B : ℚ) = (y : ℚ) := by
      rw [← hg]
      simp [ratPolyEval, g_param, c_param, a_param, b_param,
        x_var, y_var, z_var, w_var, A, B, Cc, x0, y0, z0, w0]
    have hhcoord : (Cc : ℚ) * ((A : ℚ) ^ 2 + (B : ℚ) ^ 2) / 2 = (z : ℚ) := by
      rw [← hh]
      simp [ratPolyEval, h_param, c_param, a_param, b_param,
        x_var, y_var, z_var, w_var, A, B, Cc, x0, y0, z0, w0]
      ring
    have hT : ∃ a b c : ℤ, TMap a b c = ((x : ℚ), (y : ℚ), (z : ℚ)) := by
      refine ⟨A, B, Cc, ?_⟩
      ext
      · simpa [TMap] using hfcoord
      · simpa [TMap] using hgcoord
      · simpa [TMap] using hhcoord
    have hpy : IsPythagoreanTriple x y z := (pythagorean_iff_mem_TMap_range x y z).mpr hT
    simpa [pythagoreanTriples] using hpy
