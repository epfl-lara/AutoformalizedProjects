import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

open MvPolynomial UniqueFactorizationMonoid

def IntegerValued4 (F : ℤ → ℤ → ℤ → ℤ → ℚ) : Prop :=
  ∀ x y z w : ℤ, ∃ n : ℤ, (n : ℚ) = F x y z w

def IntegerValued4OnPositiveNonnegative (F : ℤ → ℤ → ℤ → ℤ → ℚ) : Prop :=
  ∀ x y z w : ℤ, x > 0 → y > 0 → z > 0 → w ≥ 0 → ∃ n : ℤ, (n : ℚ) = F x y z w

def IntegerValued16 (F : (Fin 16 → ℤ) → ℚ) : Prop :=
  ∀ a : Fin 16 → ℤ, ∃ n : ℤ, (n : ℚ) = F a

/-! ## Rational parametrization T(a,b,c)

The source defines `T(a,b,c) = (c(a²-b²)/2, cab, c(a²+b²)/2)`.
These are rational-valued functions that yield Pythagorean triples.
-/

def T_x (a b c : ℤ) : ℚ := (c * (a^2 - b^2)) / 2
def T_y (a b c : ℤ) : ℚ := c * a * b
def T_z (a b c : ℤ) : ℚ := (c * (a^2 + b^2)) / 2

/-- `T(a,b,c)` always satisfies the Pythagorean equation.

Source proof: direct verification by expanding
`T_x² + T_y² = T_z²`.
-/
theorem T_is_pythagorean (a b c : ℤ) :
    (T_x a b c)^2 + (T_y a b c)^2 = (T_z a b c)^2 := by
  simp [T_x, T_y, T_z]
  ring

/-- `T(a,b,c)` yields integers iff `c` is even or `a ≡ b (mod 2)`.

Source proof: `T_y` is always integral. `T_x` and `T_z` involve division by 2,
so they are integral exactly when `c(a²-b²)` and `c(a²+b²)` are even.
Since `a²-b²` and `a²+b²` have the same parity, this happens iff `c` is even
or `a²-b²` is even, i.e. `a ≡ b (mod 2)`.
-/
theorem T_integer_iff (a b c : ℤ) :
    (∃ x y z : ℤ, (x : ℚ) = T_x a b c ∧ (y : ℚ) = T_y a b c ∧ (z : ℚ) = T_z a b c) ↔
      c % 2 = 0 ∨ a % 2 = b % 2 := by
  constructor
  · -- Forward: if T(a,b,c) gives integers, then c even or a ≡ b (mod 2)
    rintro ⟨x, y, z, hx, hy, hz⟩
    have h1 : 2 * x = c * (a^2 - b^2) := by
      have h : (2 * x : ℚ) = c * (a^2 - b^2) := by
        rw [hx]
        simp [T_x]
        ring
      exact_mod_cast h
    by_cases hc : c % 2 = 0
    · left; exact hc
    · right
      have hc' : c % 2 = 1 := by omega
      have h3 : (a^2 - b^2) % 2 = 0 := by
        have h4 : 2 ∣ c * (a^2 - b^2) := by
          use x
          rw [h1]
        have h5 : c % 2 = 1 := hc'
        have h6 : (c * (a^2 - b^2)) % 2 = 0 := by
          rw [Int.dvd_iff_emod_eq_zero] at h4
          exact h4
        simp [Int.mul_emod, h5] at h6
        omega
      have ha0 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb0 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha0 with (ha | ha)
      · rcases hb0 with (hb | hb)
        · have : a % 2 = b % 2 := by rw [ha, hb]
          exact this
        · have h6 : a^2 % 2 = 0 := by
            rw [pow_two, Int.mul_emod, ha]
            norm_num
          have h7 : b^2 % 2 = 1 := by
            rw [pow_two, Int.mul_emod, hb]
            norm_num
          have h8 : (a^2 - b^2) % 2 = 1 := by
            rw [Int.sub_emod, h6, h7]
            norm_num
          rw [h8] at h3
          exfalso
          linarith
      · rcases hb0 with (hb | hb)
        · have h6 : a^2 % 2 = 1 := by
            rw [pow_two, Int.mul_emod, ha]
            norm_num
          have h7 : b^2 % 2 = 0 := by
            rw [pow_two, Int.mul_emod, hb]
            norm_num
          have h8 : (a^2 - b^2) % 2 = 1 := by
            rw [Int.sub_emod, h6, h7]
            norm_num
          rw [h8] at h3
          exfalso
          linarith
        · have : a % 2 = b % 2 := by rw [ha, hb]
          exact this
  · -- Backward: if c even or a ≡ b (mod 2), then T(a,b,c) gives integers
    rintro (hc | hab)
    · -- c % 2 = 0
      have ⟨k, hk⟩ : ∃ k : ℤ, c = 2 * k := ⟨c / 2, by omega⟩
      use k * (a^2 - b^2), c * a * b, k * (a^2 + b^2)
      constructor
      · simp [T_x, hk]
        ring
      constructor
      · simp [T_y]
      · simp [T_z, hk]
        ring
    · -- a % 2 = b % 2
      have h1 : (a^2 - b^2) % 2 = 0 := by
        have h2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have h3 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases h2 with (ha | ha)
        · rcases h3 with (hb | hb)
          · have h4 : a^2 % 2 = 0 := by
              rw [pow_two, Int.mul_emod, ha]
              norm_num
            have h5 : b^2 % 2 = 0 := by
              rw [pow_two, Int.mul_emod, hb]
              norm_num
            rw [Int.sub_emod, h4, h5]
            norm_num
          · exfalso
            have h4 : (0 : ℤ) = 1 := by
              rw [← ha, hab, hb]
            norm_num at h4
            all_goals tauto
        · rcases h3 with (hb | hb)
          · exfalso
            have h4 : (1 : ℤ) = 0 := by
              rw [← ha, hab, hb]
            norm_num at h4
            all_goals tauto
          · have h4 : a^2 % 2 = 1 := by
              rw [pow_two, Int.mul_emod, ha]
              norm_num
            have h5 : b^2 % 2 = 1 := by
              rw [pow_two, Int.mul_emod, hb]
              norm_num
            rw [Int.sub_emod, h4, h5]
            norm_num
      have h2 : (a^2 + b^2) % 2 = 0 := by
        have h3 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have h4 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases h3 with (ha | ha)
        · rcases h4 with (hb | hb)
          · have h5 : a^2 % 2 = 0 := by
              rw [pow_two, Int.mul_emod, ha]
              norm_num
            have h6 : b^2 % 2 = 0 := by
              rw [pow_two, Int.mul_emod, hb]
              norm_num
            rw [Int.add_emod, h5, h6]
            norm_num
          · exfalso
            have h5 : (0 : ℤ) = 1 := by
              rw [← ha, hab, hb]
            norm_num at h5
            all_goals tauto
        · rcases h4 with (hb | hb)
          · exfalso
            have h5 : (1 : ℤ) = 0 := by
              rw [← ha, hab, hb]
            norm_num at h5
            all_goals tauto
          · have h5 : a^2 % 2 = 1 := by
              rw [pow_two, Int.mul_emod, ha]
              norm_num
            have h6 : b^2 % 2 = 1 := by
              rw [pow_two, Int.mul_emod, hb]
              norm_num
            rw [Int.add_emod, h5, h6]
            norm_num
      have ⟨k1, hk1⟩ : ∃ k1 : ℤ, c * (a^2 - b^2) = 2 * k1 := by
        have h3 : 2 ∣ (a^2 - b^2) := by
          rw [Int.dvd_iff_emod_eq_zero]
          exact h1
        have h4 : 2 ∣ c * (a^2 - b^2) := by
          apply dvd_mul_of_dvd_right
          exact h3
        rcases h4 with ⟨k1, hk1⟩
        exact ⟨k1, hk1⟩
      have ⟨k2, hk2⟩ : ∃ k2 : ℤ, c * (a^2 + b^2) = 2 * k2 := by
        have h3 : 2 ∣ (a^2 + b^2) := by
          rw [Int.dvd_iff_emod_eq_zero]
          exact h2
        have h4 : 2 ∣ c * (a^2 + b^2) := by
          apply dvd_mul_of_dvd_right
          exact h3
        rcases h4 with ⟨k2, hk2⟩
        exact ⟨k2, hk2⟩
      use k1, c * a * b, k2
      constructor
      · simp [T_x]
        have h : (c * (a^2 - b^2) : ℚ) = 2 * (k1 : ℚ) := by exact_mod_cast hk1
        linarith
      constructor
      · simp [T_y]
      · simp [T_z]
        have h : (c * (a^2 + b^2) : ℚ) = 2 * (k2 : ℚ) := by exact_mod_cast hk2
        linarith

/-- Every Pythagorean triple is of the form `T(a,b,c)` for some integers `a,b,c`.

Source proof: Every primitive PT with `z>0` is `T₁(a,b)` or `T₂(a,b)`.
Since `2·T₂(a,b) = T₁(a+b,a-b)`, every primitive PT is `c·T₁(a,b)/2` with
`c ∈ {1,2}`. Scaling gives the general case.
-/
theorem pythagoreanTriple_eq_T (x y z : ℤ) (h : PythagoreanTriple x y z) :
    ∃ a b c : ℤ, (x : ℚ) = T_x a b c ∧ (y : ℚ) = T_y a b c ∧ (z : ℚ) = T_z a b c := by
  have h_eq : x * x + y * y = z * z := PythagoreanTriple.eq h
  have h_class := PythagoreanTriple.classified h
  let k := h_class.choose
  let h1 := h_class.choose_spec
  let m := h1.choose
  let h2 := h1.choose_spec
  let n := h2.choose
  let h3 := h2.choose_spec
  have hmn : m.gcd n = 1 := h3.right
  have h_eq2 : x = k * (m^2 - n^2) ∧ y = k * (2 * m * n) ∨ x = k * (2 * m * n) ∧ y = k * (m^2 - n^2) := h3.left
  cases h_eq2 with
  | inl h_eq2 =>
    have hx : x = k * (m^2 - n^2) := h_eq2.left
    have hy : y = k * (2 * m * n) := h_eq2.right
    have h1 : z^2 = (k * (m^2 + n^2))^2 := by
      have h2 : (k * (m^2 - n^2))^2 + (k * (2 * m * n))^2 = z^2 := by
        have h4 : x * x + y * y = z * z := h_eq
        rw [hx, hy] at h4
        ring_nf at h4 ⊢
        linarith
      have h3 : (k * (m^2 - n^2))^2 + (k * (2 * m * n))^2 = (k * (m^2 + n^2))^2 := by
        ring
      linarith
    have hz : z = k * (m^2 + n^2) ∨ z = -k * (m^2 + n^2) := by
      have h2 : z^2 - (k * (m^2 + n^2))^2 = 0 := by linarith
      have h3 : (z - k * (m^2 + n^2)) * (z + k * (m^2 + n^2)) = 0 := by
        rw [← h2]
        ring
      rcases (mul_eq_zero.mp h3) with (h4 | h5)
      · left; linarith
      · right; linarith
    cases hz with
    | inl hz =>
      use m, n, 2 * k
      simp [T_x, T_y, T_z]
      constructor
      · rw [hx]
        norm_num
        ring
      constructor
      · rw [hy]
        norm_num
        ring
      · rw [hz]
        norm_num
        ring
    | inr hz =>
      use n, -m, -2 * k
      simp [T_x, T_y, T_z]
      constructor
      · rw [hx]
        norm_num
        ring
      constructor
      · rw [hy]
        norm_num
        ring
      · rw [hz]
        norm_num
        ring
  | inr h_eq2 =>
    have hx : x = k * (2 * m * n) := h_eq2.left
    have hy : y = k * (m^2 - n^2) := h_eq2.right
    have h1 : z^2 = (k * (m^2 + n^2))^2 := by
      have h2 : (k * (2 * m * n))^2 + (k * (m^2 - n^2))^2 = z^2 := by
        have h4 : x * x + y * y = z * z := h_eq
        rw [hx, hy] at h4
        ring_nf at h4 ⊢
        linarith
      have h3 : (k * (2 * m * n))^2 + (k * (m^2 - n^2))^2 = (k * (m^2 + n^2))^2 := by
        ring
      linarith
    have hz : z = k * (m^2 + n^2) ∨ z = -k * (m^2 + n^2) := by
      have h2 : z^2 - (k * (m^2 + n^2))^2 = 0 := by linarith
      have h3 : (z - k * (m^2 + n^2)) * (z + k * (m^2 + n^2)) = 0 := by
        rw [← h2]
        ring
      rcases (mul_eq_zero.mp h3) with (h4 | h5)
      · left; linarith
      · right; linarith
    cases hz with
    | inl hz =>
      use m + n, m - n, k
      simp [T_x, T_y, T_z]
      constructor
      · rw [hx]
        norm_num
        ring
      constructor
      · rw [hy]
        norm_num
        ring
      · rw [hz]
        norm_num
        ring
    | inr hz =>
      use m - n, -(m + n), -k
      simp [T_x, T_y, T_z]
      constructor
      · rw [hx]
        norm_num
        ring
      constructor
      · rw [hy]
        norm_num
        ring
      · rw [hz]
        norm_num
        ring

/-! ## Integer-valued polynomial parametrization (Theorem, line-194)

The explicit triple from the source:
```
f = (2x-xw)((y+zw)²-(z-yw)²)/2
g = (2x-xw)(y+zw)(z-yw)
h = (2x-xw)((y+zw)²+(z-yw)²)/2
```
-/

def f_param (x y z w : ℤ) : ℚ := ((2 * x - x * w) * ((y + z * w)^2 - (z - y * w)^2)) / 2
def g_param (x y z w : ℤ) : ℚ := (2 * x - x * w) * (y + z * w) * (z - y * w)
def h_param (x y z w : ℤ) : ℚ := ((2 * x - x * w) * ((y + z * w)^2 + (z - y * w)^2)) / 2

/-- The source's displayed rational formulas are integer-valued on all integer inputs.

Source proof: Substitute `a = y+zw`, `b = z-yw`, `c = 2x-xw` into the
integrality condition for `T(a,b,c)`.
-/
theorem param_integer_valued :
    IntegerValued4 f_param ∧ IntegerValued4 g_param ∧ IntegerValued4 h_param := by
  have h_subst : ∀ x y z w : ℤ,
      f_param x y z w = T_x (y + z * w) (z - y * w) (2 * x - x * w) ∧
      g_param x y z w = T_y (y + z * w) (z - y * w) (2 * x - x * w) ∧
      h_param x y z w = T_z (y + z * w) (z - y * w) (2 * x - x * w) := by
    intro x y z w
    constructor
    · simp [f_param, T_x]
    constructor
    · simp [g_param, T_y]
    · simp [h_param, T_z]
  have h_parity : ∀ x y z w : ℤ,
      (2 * x - x * w) % 2 = 0 ∨ (y + z * w) % 2 = (z - y * w) % 2 := by
    intro x y z w
    by_cases hw : w % 2 = 0
    · left
      simp [Int.sub_emod, Int.mul_emod, hw]
    · have hw1 : w % 2 = 1 := by omega
      right
      simp [Int.add_emod, Int.sub_emod, Int.mul_emod, hw1]
      omega
  constructor
  · -- f_param is integer-valued
    intro x y z w
    have ⟨hfx, _, _⟩ := h_subst x y z w
    rw [hfx]
    have h2 := h_parity x y z w
    have h3 := (T_integer_iff (y + z * w) (z - y * w) (2 * x - x * w)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use a
  constructor
  · -- g_param is integer-valued
    intro x y z w
    have ⟨_, hgy, _⟩ := h_subst x y z w
    rw [hgy]
    have h2 := h_parity x y z w
    have h3 := (T_integer_iff (y + z * w) (z - y * w) (2 * x - x * w)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use b
  · -- h_param is integer-valued
    intro x y z w
    have ⟨_, _, hhz⟩ := h_subst x y z w
    rw [hhz]
    have h2 := h_parity x y z w
    have h3 := (T_integer_iff (y + z * w) (z - y * w) (2 * x - x * w)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use c

/-- The integer-valued parametrization `(f_param, g_param, h_param)` covers all Pythagorean triples.

Source proof: Substitute `a = y+zw`, `b = z-yw`, `c = 2x-xw` into `T(a,b,c)`.
If `w` is even then `c` is even; if `w` is odd then `a ≡ b (mod 2)`.
Conversely, any `(a,b,c)` with `c` even or `a ≡ b (mod 2)` arises
by setting `w=0` or `w=1` appropriately.
-/
theorem integer_valued_parametrization :
    IntegerValued4 f_param ∧ IntegerValued4 g_param ∧ IntegerValued4 h_param ∧
    {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} =
    {(x, y, z) : ℤ × ℤ × ℤ | ∃ a b c d : ℤ,
      (x : ℚ) = f_param a b c d ∧ (y : ℚ) = g_param a b c d ∧ (z : ℚ) = h_param a b c d} := by
  have h_subst : ∀ x y z w : ℤ,
      f_param x y z w = T_x (y + z * w) (z - y * w) (2 * x - x * w) ∧
      g_param x y z w = T_y (y + z * w) (z - y * w) (2 * x - x * w) ∧
      h_param x y z w = T_z (y + z * w) (z - y * w) (2 * x - x * w) := by
    intro x y z w
    constructor
    · simp [f_param, T_x]
    constructor
    · simp [g_param, T_y]
    · simp [h_param, T_z]
  constructor
  · exact param_integer_valued.left
  constructor
  · exact param_integer_valued.right.left
  constructor
  · exact param_integer_valued.right.right
  · ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Forward: Pythagorean triple implies in the parametrization range
      intro h_pt
      have h_eq := pythagoreanTriple_eq_T x y z h_pt
      rcases h_eq with ⟨a, b, c, hx, hy, hz⟩
      have h_int : c % 2 = 0 ∨ a % 2 = b % 2 := by
        have h1 : ∃ x' y' z' : ℤ, (x' : ℚ) = T_x a b c ∧ (y' : ℚ) = T_y a b c ∧ (z' : ℚ) = T_z a b c := by
          use x, y, z
        exact (T_integer_iff a b c).mp h1
      rcases h_int with (hc | hab)
      · -- c % 2 = 0
        have ⟨k, hk⟩ : ∃ k : ℤ, c = 2 * k := ⟨c / 2, by omega⟩
        use k, a, b, 0
        constructor
        · rw [hx]
          have h1 := (h_subst k a b 0).left
          rw [h1]
          simp [hk]
        constructor
        · rw [hy]
          have h1 := (h_subst k a b 0).right.left
          rw [h1]
          simp [hk]
        · rw [hz]
          have h1 := (h_subst k a b 0).right.right
          rw [h1]
          simp [hk]
      · -- a % 2 = b % 2
        have h1 : (a + b) % 2 = 0 := by omega
        have h2 : (a - b) % 2 = 0 := by omega
        have h3 : (a - b) / 2 + (a + b) / 2 = a := by omega
        have h4 : (a + b) / 2 - (a - b) / 2 = b := by omega
        use c, (a - b) / 2, (a + b) / 2, 1
        constructor
        · rw [hx]
          have h1 := (h_subst c ((a - b) / 2) ((a + b) / 2) 1).left
          rw [h1]
          have h_arg1 : (a - b) / 2 + (a + b) / 2 * 1 = a := by
            have : (a + b) / 2 * 1 = (a + b) / 2 := by simp
            rw [this]
            exact h3
          have h_arg2 : (a + b) / 2 - (a - b) / 2 * 1 = b := by
            have : (a - b) / 2 * 1 = (a - b) / 2 := by simp
            rw [this]
            exact h4
          have h_arg3 : 2 * c - c * 1 = c := by simp; ring
          rw [h_arg1, h_arg2, h_arg3]
        constructor
        · rw [hy]
          have h1 := (h_subst c ((a - b) / 2) ((a + b) / 2) 1).right.left
          rw [h1]
          have h_arg1 : (a - b) / 2 + (a + b) / 2 * 1 = a := by
            have : (a + b) / 2 * 1 = (a + b) / 2 := by simp
            rw [this]
            exact h3
          have h_arg2 : (a + b) / 2 - (a - b) / 2 * 1 = b := by
            have : (a - b) / 2 * 1 = (a - b) / 2 := by simp
            rw [this]
            exact h4
          have h_arg3 : 2 * c - c * 1 = c := by simp; ring
          rw [h_arg1, h_arg2, h_arg3]
        · rw [hz]
          have h1 := (h_subst c ((a - b) / 2) ((a + b) / 2) 1).right.right
          rw [h1]
          have h_arg1 : (a - b) / 2 + (a + b) / 2 * 1 = a := by
            have : (a + b) / 2 * 1 = (a + b) / 2 := by simp
            rw [this]
            exact h3
          have h_arg2 : (a + b) / 2 - (a - b) / 2 * 1 = b := by
            have : (a - b) / 2 * 1 = (a - b) / 2 := by simp
            rw [this]
            exact h4
          have h_arg3 : 2 * c - c * 1 = c := by simp; ring
          rw [h_arg1, h_arg2, h_arg3]
    · -- Backward: in the parametrization range implies Pythagorean triple
      rintro ⟨a, b, c, d, hx, hy, hz⟩
      have h_eq : (x : ℚ)^2 + (y : ℚ)^2 = (z : ℚ)^2 := by
        rw [hx, hy, hz]
        have h_subst' := h_subst a b c d
        rcases h_subst' with ⟨hfx, hgy, hhz⟩
        rw [hfx, hgy, hhz]
        exact T_is_pythagorean (b + c * d) (c - b * d) (2 * a - a * d)
      have h_eq2 : x * x + y * y = z * z := by
        have h3 : (x * x + y * y : ℚ) = (z * z : ℚ) := by
          have h4 : (x * x + y * y : ℚ) = (x : ℚ)^2 + (y : ℚ)^2 := by ring
          have h5 : (z * z : ℚ) = (z : ℚ)^2 := by ring
          rw [h4, h5, h_eq]
        exact_mod_cast h3
      exact h_eq2

/-! ## Positive Pythagorean triples (Remark, line-240)

The explicit triple from the source:
```
f = (x+(1-w)²x)((y+(1+w)z)²-y²)/2
g = (x+(1-w)²x)(y+(1+w)z)y
h = (x+(1-w)²x)((y+(1+w)z)²+y²)/2
```
where `x,y,z > 0` and `w ≥ 0`.
-/

def f_pos (x y z w : ℤ) : ℚ := ((x + (1 - w)^2 * x) * ((y + (1 + w) * z)^2 - y^2)) / 2
def g_pos (x y z w : ℤ) : ℚ := (x + (1 - w)^2 * x) * (y + (1 + w) * z) * y
def h_pos (x y z w : ℤ) : ℚ := ((x + (1 - w)^2 * x) * ((y + (1 + w) * z)^2 + y^2)) / 2

def fourSquares (a b c d : ℤ) : ℤ := a^2 + b^2 + c^2 + d^2
def fourSquaresPos (a b c d : ℤ) : ℤ := fourSquares a b c d + 1

def f_pos16 (a : Fin 16 → ℤ) : ℚ :=
  f_pos
    (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
    (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
    (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
    (fourSquares (a 12) (a 13) (a 14) (a 15))

def g_pos16 (a : Fin 16 → ℤ) : ℚ :=
  g_pos
    (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
    (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
    (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
    (fourSquares (a 12) (a 13) (a 14) (a 15))

def h_pos16 (a : Fin 16 → ℤ) : ℚ :=
  h_pos
    (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
    (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
    (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
    (fourSquares (a 12) (a 13) (a 14) (a 15))

/-- The positive-parametrization formulas are integer-valued on their stated domain.

Source proof: Substitute `a = y+(1+w)z`, `b = y`,
`c = x+(1-w)²x` into the integrality condition for `T(a,b,c)`.
-/
theorem positive_param_integer_valued :
    IntegerValued4OnPositiveNonnegative f_pos ∧
    IntegerValued4OnPositiveNonnegative g_pos ∧
    IntegerValued4OnPositiveNonnegative h_pos := by
  have h_subst : ∀ x y z w : ℤ,
      f_pos x y z w = T_x (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
      g_pos x y z w = T_y (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
      h_pos x y z w = T_z (y + (1 + w) * z) y (x + (1 - w)^2 * x) := by
    intro x y z w
    constructor
    · simp [f_pos, T_x]
      <;> ring
    constructor
    · simp [g_pos, T_y]
      <;> ring
    · simp [h_pos, T_z]
      <;> ring
  have h_parity : ∀ x y z w : ℤ, w ≥ 0 →
      (x + (1 - w)^2 * x) % 2 = 0 ∨ (y + (1 + w) * z) % 2 = y % 2 := by
    intro x y z w hw
    by_cases hw_even : w % 2 = 0
    · left
      have h1 : (1 - w) % 2 = 1 := by
        simp [Int.sub_emod, hw_even]
      have h2 : ((1 - w) ^ 2) % 2 = 1 := by
        simp [pow_two, Int.mul_emod, h1]
      have h3 : (1 + (1 - w) ^ 2) % 2 = 0 := by
        simp [Int.add_emod, h2]
      have h4 : (x + (1 - w)^2 * x) % 2 = 0 := by
        have h5 : x + (1 - w)^2 * x = x * (1 + (1 - w)^2) := by ring
        rw [h5]
        simp [Int.mul_emod, h3]
      exact h4
    · have hw_odd : w % 2 = 1 := by omega
      right
      have h1 : (1 + w) % 2 = 0 := by
        simp [Int.add_emod, hw_odd]
      have h2 : ((1 + w) * z) % 2 = 0 := by
        simp [Int.mul_emod, h1]
      have h3 : (y + (1 + w) * z) % 2 = y % 2 := by
        simp [Int.add_emod, h2]
      exact h3
  constructor
  · -- f_pos is integer-valued on positive domain
    intro x y z w hx hy hz hw
    have ⟨hfx, _, _⟩ := h_subst x y z w
    rw [hfx]
    have h2 := h_parity x y z w hw
    have h3 := (T_integer_iff (y + (1 + w) * z) y (x + (1 - w)^2 * x)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use a
  constructor
  · -- g_pos is integer-valued on positive domain
    intro x y z w hx hy hz hw
    have ⟨_, hgy, _⟩ := h_subst x y z w
    rw [hgy]
    have h2 := h_parity x y z w hw
    have h3 := (T_integer_iff (y + (1 + w) * z) y (x + (1 - w)^2 * x)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use b
  · -- h_pos is integer-valued on positive domain
    intro x y z w hx hy hz hw
    have ⟨_, _, hhz⟩ := h_subst x y z w
    rw [hhz]
    have h2 := h_parity x y z w hw
    have h3 := (T_integer_iff (y + (1 + w) * z) y (x + (1 - w)^2 * x)).mpr h2
    rcases h3 with ⟨a, b, c, ha, hb, hc⟩
    use c

/-- The parametrization `(f_pos, g_pos, h_pos)` covers all positive Pythagorean triples.

Source proof: Positive PTs are `T(a,b,c)` with `a,b,c > 0`, `a > b`, and
`c` even or `a ≡ b (mod 2)`. Such triples are parametrized by
`(a,b,c) = (y+(1+w)z, y, x+(1-w)²x)` with `x,y,z > 0` and `w ≥ 0`.
Substituting into `T` gives `f_pos, g_pos, h_pos`.
-/
theorem positive_pythagorean_parametrization :
    IntegerValued4OnPositiveNonnegative f_pos ∧
    IntegerValued4OnPositiveNonnegative g_pos ∧
    IntegerValued4OnPositiveNonnegative h_pos ∧
    {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ PythagoreanTriple x y z} =
    {(x, y, z) : ℤ × ℤ × ℤ | ∃ a b c d : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d ≥ 0 ∧
      (x : ℚ) = f_pos a b c d ∧ (y : ℚ) = g_pos a b c d ∧ (z : ℚ) = h_pos a b c d} := by
  constructor
  · exact positive_param_integer_valued.left
  constructor
  · exact positive_param_integer_valued.right.left
  constructor
  · exact positive_param_integer_valued.right.right
  · ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Forward: positive PT implies in the parametrization range
      rintro ⟨hx, hy, hz, h_pt⟩
      have h_eq := pythagoreanTriple_eq_T x y z h_pt
      rcases h_eq with ⟨a, b, c, hx_T, hy_T, hz_T⟩
      have h_subst : ∀ x y z w : ℤ,
          f_pos x y z w = T_x (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
          g_pos x y z w = T_y (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
          h_pos x y z w = T_z (y + (1 + w) * z) y (x + (1 - w)^2 * x) := by
        intro x y z w
        constructor
        · simp [f_pos, T_x]
          <;> ring
        constructor
        · simp [g_pos, T_y]
          <;> ring
        · simp [h_pos, T_z]
          <;> ring
      have hc_pos : c > 0 := by
        have h1 : (z : ℚ) = (c * (a^2 + b^2)) / 2 := by
          rw [hz_T]
          simp [T_z]
          <;> ring
        have h2 : (z : ℚ) > 0 := by exact_mod_cast hz
        have h3 : (c * (a^2 + b^2) : ℚ) > 0 := by linarith [h1, h2]
        have h4 : c * (a^2 + b^2) > 0 := by exact_mod_cast h3
        have h5 : a^2 + b^2 > 0 := by
          by_contra h
          push_neg at h
          have h6 : a^2 ≥ 0 := sq_nonneg a
          have h7 : b^2 ≥ 0 := sq_nonneg b
          have h8 : a^2 = 0 := by nlinarith
          have h9 : b^2 = 0 := by nlinarith
          have h10 : a = 0 := by simpa using h8
          have h11 : b = 0 := by simpa using h9
          rw [h10, h11] at h1
          norm_num at h1
          have h12 : (z : ℚ) = 0 := by linarith
          have h13 : z = 0 := by exact_mod_cast h12
          linarith
        nlinarith
      have hab_pos : a * b > 0 := by
        have h1 : (y : ℚ) = (c * (a * b) : ℚ) := by
          rw [hy_T]
          simp [T_y]
          <;> ring
        have h2 : (y : ℚ) > 0 := by exact_mod_cast hy
        have h3 : (c * (a * b) : ℚ) > 0 := by linarith [h1, h2]
        have h4 : c * (a * b) > 0 := by exact_mod_cast h3
        nlinarith [hc_pos]
      have ha2_gt_b2 : a^2 > b^2 := by
        have h1 : (x : ℚ) = (c * (a^2 - b^2)) / 2 := by
          rw [hx_T]
          simp [T_x]
          <;> ring
        have h2 : (x : ℚ) > 0 := by exact_mod_cast hx
        have h3 : (c * (a^2 - b^2) : ℚ) > 0 := by linarith [h1, h2]
        have h4 : c * (a^2 - b^2) > 0 := by exact_mod_cast h3
        nlinarith [hc_pos]
      have h_a_pos_or_neg : a > 0 ∨ a < 0 := by
        by_contra h
        push_neg at h
        have : a = 0 := by omega
        rw [this] at hab_pos
        nlinarith
      cases h_a_pos_or_neg with
      | inl ha_pos =>
        have hb_pos : b > 0 := by nlinarith [hab_pos]
        have ha_gt_b : a > b := by nlinarith [ha2_gt_b2, ha_pos, hb_pos]
        have h_parity : c % 2 = 0 ∨ a % 2 = b % 2 := by
          have h1 : ∃ x' y' z' : ℤ, (x' : ℚ) = T_x a b c ∧ (y' : ℚ) = T_y a b c ∧ (z' : ℚ) = T_z a b c := by
            use x, y, z
          exact (T_integer_iff a b c).mp h1
        rcases h_parity with (hc_even | hab_parity)
        · -- c even
          have ⟨k, hk⟩ : ∃ k : ℤ, c = 2 * k := ⟨c / 2, by omega⟩
          have hk_pos : k > 0 := by nlinarith [hc_pos, hk]
          use k, b, a - b, 0
          constructor
          · exact hk_pos
          constructor
          · exact hb_pos
          constructor
          · exact sub_pos.mpr ha_gt_b
          constructor
          · exact Int.le_refl 0
          constructor
          · -- x = f_pos k b (a - b) 0
            have h_eq : (f_pos k b (a - b) 0 : ℚ) = (T_x a b c : ℚ) := by
              have h1 := (h_subst k b (a - b) 0).left
              rw [h1]
              have h2 : b + (1 + 0) * (a - b) = a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hx_T
          constructor
          · -- y = g_pos k b (a - b) 0
            have h_eq : (g_pos k b (a - b) 0 : ℚ) = (T_y a b c : ℚ) := by
              have h1 := (h_subst k b (a - b) 0).right.left
              rw [h1]
              have h2 : b + (1 + 0) * (a - b) = a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hy_T
          · -- z = h_pos k b (a - b) 0
            have h_eq : (h_pos k b (a - b) 0 : ℚ) = (T_z a b c : ℚ) := by
              have h1 := (h_subst k b (a - b) 0).right.right
              rw [h1]
              have h2 : b + (1 + 0) * (a - b) = a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hz_T
        · -- a ≡ b (mod 2)
          have h1 : (a + b) % 2 = 0 := by omega
          have h2 : (a - b) % 2 = 0 := by omega
          use c, b, (a - b) / 2, 1
          constructor
          · exact hc_pos
          constructor
          · exact hb_pos
          constructor
          · have h3 : (a - b) / 2 > 0 := by
              have h4 : a - b > 0 := by omega
              have h5 : (a - b) % 2 = 0 := by omega
              have h6 : a - b ≥ 2 := by
                by_contra h
                push_neg at h
                have h7 : a - b = 1 := by omega
                have h8 : (a - b) % 2 = 1 := by
                  rw [h7]
                  norm_num
                omega
              omega
            exact h3
          constructor
          · exact Int.le_of_lt (show (1 : ℤ) > 0 by norm_num)
          constructor
          · -- x = f_pos c b ((a - b) / 2) 1
            have h_eq : (f_pos c b ((a - b) / 2) 1 : ℚ) = (x : ℚ) := by
              have h1 := (h_subst c b ((a - b) / 2) 1).left
              rw [h1]
              have h2 : b + (1 + 1) * ((a - b) / 2) = a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hx_T.symm
            exact_mod_cast h_eq.symm
          constructor
          · -- y = g_pos c b ((a - b) / 2) 1
            have h_eq : (g_pos c b ((a - b) / 2) 1 : ℚ) = (y : ℚ) := by
              have h1 := (h_subst c b ((a - b) / 2) 1).right.left
              rw [h1]
              have h2 : b + (1 + 1) * ((a - b) / 2) = a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hy_T.symm
            exact_mod_cast h_eq.symm
          · -- z = h_pos c b ((a - b) / 2) 1
            have h_eq : (h_pos c b ((a - b) / 2) 1 : ℚ) = (z : ℚ) := by
              have h1 := (h_subst c b ((a - b) / 2) 1).right.right
              rw [h1]
              have h2 : b + (1 + 1) * ((a - b) / 2) = a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hz_T.symm
            exact_mod_cast h_eq.symm
      | inr ha_neg =>
        have hb_neg : b < 0 := by nlinarith [hab_pos]
        have ha_gt_b : -a > -b := by nlinarith [ha2_gt_b2, ha_neg, hb_neg]
        have hx_T' : (x : ℚ) = T_x (-a) (-b) c := by
          rw [hx_T]
          simp [T_x]
          <;> ring
        have hy_T' : (y : ℚ) = T_y (-a) (-b) c := by
          rw [hy_T]
          simp [T_y]
          <;> ring
        have hz_T' : (z : ℚ) = T_z (-a) (-b) c := by
          rw [hz_T]
          simp [T_z]
          <;> ring
        have h_parity : c % 2 = 0 ∨ (-a) % 2 = (-b) % 2 := by
          have h1 : ∃ x' y' z' : ℤ, (x' : ℚ) = T_x (-a) (-b) c ∧ (y' : ℚ) = T_y (-a) (-b) c ∧ (z' : ℚ) = T_z (-a) (-b) c := by
            use x, y, z
          exact (T_integer_iff (-a) (-b) c).mp h1
        rcases h_parity with (hc_even | hab_parity)
        · -- c even
          have ⟨k, hk⟩ : ∃ k : ℤ, c = 2 * k := ⟨c / 2, by omega⟩
          have hk_pos : k > 0 := by nlinarith [hc_pos, hk]
          use k, -b, -a - (-b), 0
          constructor
          · exact hk_pos
          constructor
          · exact show -b > 0 by linarith
          constructor
          · exact sub_pos.mpr ha_gt_b
          constructor
          · exact Int.le_refl 0
          constructor
          · -- x = f_pos k (-b) (-a - (-b)) 0
            have h_eq : (f_pos k (-b) (-a - (-b)) 0 : ℚ) = (T_x (-a) (-b) c : ℚ) := by
              have h1 := (h_subst k (-b) (-a - (-b)) 0).left
              rw [h1]
              have h2 : -b + (1 + 0) * (-a - (-b)) = -a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hx_T'
          constructor
          · -- y = g_pos k (-b) (-a - (-b)) 0
            have h_eq : (g_pos k (-b) (-a - (-b)) 0 : ℚ) = (T_y (-a) (-b) c : ℚ) := by
              have h1 := (h_subst k (-b) (-a - (-b)) 0).right.left
              rw [h1]
              have h2 : -b + (1 + 0) * (-a - (-b)) = -a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hy_T'
          · -- z = h_pos k (-b) (-a - (-b)) 0
            have h_eq : (h_pos k (-b) (-a - (-b)) 0 : ℚ) = (T_z (-a) (-b) c : ℚ) := by
              have h1 := (h_subst k (-b) (-a - (-b)) 0).right.right
              rw [h1]
              have h2 : -b + (1 + 0) * (-a - (-b)) = -a := by ring
              have h3 : k + (1 - 0)^2 * k = c := by
                rw [show c = 2 * k by omega]
                ring
              rw [h2, h3]
            rw [h_eq]
            exact hz_T'
        · -- -a ≡ -b (mod 2)
          have h1 : (-a + -b) % 2 = 0 := by omega
          have h2 : (-a - -b) % 2 = 0 := by omega
          use c, -b, (-a - -b) / 2, 1
          constructor
          · exact hc_pos
          constructor
          · exact show -b > 0 by linarith
          constructor
          · have h3 : (-a - -b) / 2 > 0 := by
              have h4 : -a - -b > 0 := by nlinarith
              have h5 : (-a - -b) % 2 = 0 := by omega
              have h6 : -a - -b ≥ 2 := by
                by_contra h
                push_neg at h
                have h7 : -a - -b = 1 := by omega
                have h8 : (-a - -b) % 2 = 1 := by
                  rw [h7]
                  norm_num
                omega
              omega
            exact h3
          constructor
          · exact Int.le_of_lt (show (1 : ℤ) > 0 by norm_num)
          constructor
          · -- x = f_pos c (-b) ((-a - -b) / 2) 1
            have h_eq : (f_pos c (-b) ((-a - -b) / 2) 1 : ℚ) = (x : ℚ) := by
              have h1 := (h_subst c (-b) ((-a - -b) / 2) 1).left
              rw [h1]
              have h2 : -b + (1 + 1) * ((-a - -b) / 2) = -a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hx_T'.symm
            exact_mod_cast h_eq.symm
          constructor
          · -- y = g_pos c (-b) ((-a - -b) / 2) 1
            have h_eq : (g_pos c (-b) ((-a - -b) / 2) 1 : ℚ) = (y : ℚ) := by
              have h1 := (h_subst c (-b) ((-a - -b) / 2) 1).right.left
              rw [h1]
              have h2 : -b + (1 + 1) * ((-a - -b) / 2) = -a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hy_T'.symm
            exact_mod_cast h_eq.symm
          · -- z = h_pos c (-b) ((-a - -b) / 2) 1
            have h_eq : (h_pos c (-b) ((-a - -b) / 2) 1 : ℚ) = (z : ℚ) := by
              have h1 := (h_subst c (-b) ((-a - -b) / 2) 1).right.right
              rw [h1]
              have h2 : -b + (1 + 1) * ((-a - -b) / 2) = -a := by omega
              have h3 : c + (1 - 1)^2 * c = c := by ring
              rw [h2, h3]
              exact hz_T'.symm
            exact_mod_cast h_eq.symm
    · -- Backward: in the parametrization range implies positive PT
      rintro ⟨a, b, c, d, ha, hb, hc, hd, hx, hy, hz⟩
      have h_subst : ∀ x y z w : ℤ,
          f_pos x y z w = T_x (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
          g_pos x y z w = T_y (y + (1 + w) * z) y (x + (1 - w)^2 * x) ∧
          h_pos x y z w = T_z (y + (1 + w) * z) y (x + (1 - w)^2 * x) := by
        intro x y z w
        constructor
        · simp [f_pos, T_x]
          <;> ring
        constructor
        · simp [g_pos, T_y]
          <;> ring
        · simp [h_pos, T_z]
          <;> ring
      have h_pt : PythagoreanTriple x y z := by
        have h_eq : (x : ℚ)^2 + (y : ℚ)^2 = (z : ℚ)^2 := by
          rw [hx, hy, hz]
          have h1 := h_subst a b c d
          rcases h1 with ⟨hfx, hgy, hhz⟩
          rw [hfx, hgy, hhz]
          exact T_is_pythagorean (b + (1 + d) * c) b (a + (1 - d)^2 * a)
        have h_eq2 : x * x + y * y = z * z := by
          have h3 : (x * x + y * y : ℚ) = (z * z : ℚ) := by
            have h4 : (x * x + y * y : ℚ) = (x : ℚ)^2 + (y : ℚ)^2 := by ring
            have h5 : (z * z : ℚ) = (z : ℚ)^2 := by ring
            rw [h4, h5, h_eq]
          exact_mod_cast h3
        exact h_eq2
      have h_a_term_pos : (a + (1 - d)^2 * a : ℚ) > 0 := by
        have h1 : (a : ℚ) > 0 := by exact_mod_cast ha
        have h2 : (1 + (1 - d : ℚ)^2) > 0 := by
          have h3 : (1 - d : ℚ)^2 ≥ 0 := sq_nonneg ((1 - d : ℚ))
          nlinarith
        have h3 : (a + (1 - d)^2 * a : ℚ) = (a : ℚ) * (1 + (1 - d : ℚ)^2) := by ring
        rw [h3]
        nlinarith
      have h_b_term_pos : (b + (1 + d) * c : ℚ) > (b : ℚ) := by
        have h1 : (1 + d : ℚ) ≥ 1 := by
          have h2 : (d : ℚ) ≥ 0 := by exact_mod_cast hd
          nlinarith
        have h2 : (c : ℚ) > 0 := by exact_mod_cast hc
        have h3 : ((1 + d) * c : ℚ) > 0 := by nlinarith
        nlinarith
      have hx_pos : x > 0 := by
        have h1 : (x : ℚ) > 0 := by
          rw [hx]
          have hfx := (h_subst a b c d).left
          rw [hfx]
          simp [T_x]
          have h2 : (b + (1 + d) * c : ℚ)^2 > (b : ℚ)^2 := by
            have h3 : (b + (1 + d) * c : ℚ) > (b : ℚ) := h_b_term_pos
            have h4 : (b + (1 + d) * c : ℚ) + (b : ℚ) > 0 := by nlinarith [show (b : ℚ) > 0 by exact_mod_cast hb, show (c : ℚ) > 0 by exact_mod_cast hc, show (d : ℚ) ≥ 0 by exact_mod_cast hd]
            nlinarith [h3, h4]
          have h3 : (b + (1 + d) * c : ℚ)^2 - (b : ℚ)^2 > 0 := by linarith
          apply div_pos
          · nlinarith
          · norm_num
        exact_mod_cast h1
      have hy_pos : y > 0 := by
        have h1 : (y : ℚ) > 0 := by
          rw [hy]
          have hgy := (h_subst a b c d).right.left
          rw [hgy]
          simp [T_y]
          have h2 : (b + (1 + d) * c : ℚ) > 0 := by
            have h3 : (b : ℚ) > 0 := by exact_mod_cast hb
            have h4 : ((1 + d) * c : ℚ) > 0 := by
              have h5 : (1 + d : ℚ) ≥ 1 := by
                have h6 : (d : ℚ) ≥ 0 := by exact_mod_cast hd
                nlinarith
              have h6 : (c : ℚ) > 0 := by exact_mod_cast hc
              nlinarith
            nlinarith
          have h3 : (a + (1 - d)^2 * a : ℚ) > 0 := h_a_term_pos
          have h4 : (b : ℚ) > 0 := by exact_mod_cast hb
          positivity
        exact_mod_cast h1
      have hz_pos : z > 0 := by
        have h1 : (z : ℚ) > 0 := by
          rw [hz]
          have hhz := (h_subst a b c d).right.right
          rw [hhz]
          simp [T_z]
          have h2 : (b + (1 + d) * c : ℚ)^2 + (b : ℚ)^2 > 0 := by
            have h3 : (b + (1 + d) * c : ℚ)^2 ≥ 0 := sq_nonneg ((b + (1 + d) * c : ℚ))
            have h4 : (b : ℚ)^2 > 0 := by
              have h5 : (b : ℚ) > 0 := by exact_mod_cast hb
              nlinarith
            nlinarith
          apply div_pos
          · nlinarith
          · norm_num
        exact_mod_cast h1
      exact ⟨hx_pos, hy_pos, hz_pos, h_pt⟩

/-- The four-square substitution gives a parametrization of positive Pythagorean triples
with unrestricted integer parameters.

Source proof: use the four-square theorem to replace each positive parameter by
a sum of four squares plus one, and the nonnegative parameter by a sum of four squares.
-/
theorem positive_pythagorean_parametrization_integer_parameters :
    IntegerValued16 f_pos16 ∧ IntegerValued16 g_pos16 ∧ IntegerValued16 h_pos16 ∧
    {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ PythagoreanTriple x y z} =
    {(x, y, z) : ℤ × ℤ × ℤ | ∃ a : Fin 16 → ℤ,
      (x : ℚ) = f_pos16 a ∧ (y : ℚ) = g_pos16 a ∧ (z : ℚ) = h_pos16 a} := by
  constructor
  · -- IntegerValued16 f_pos16
    intro a
    exact (positive_param_integer_valued.left)
      (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
      (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
      (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
      (fourSquares (a 12) (a 13) (a 14) (a 15))
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 4), sq_nonneg (a 5), sq_nonneg (a 6), sq_nonneg (a 7)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 8), sq_nonneg (a 9), sq_nonneg (a 10), sq_nonneg (a 11)])
      (by simp [fourSquares]; nlinarith [sq_nonneg (a 12), sq_nonneg (a 13), sq_nonneg (a 14), sq_nonneg (a 15)])
  constructor
  · -- IntegerValued16 g_pos16
    intro a
    exact (positive_param_integer_valued.right.left)
      (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
      (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
      (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
      (fourSquares (a 12) (a 13) (a 14) (a 15))
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 4), sq_nonneg (a 5), sq_nonneg (a 6), sq_nonneg (a 7)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 8), sq_nonneg (a 9), sq_nonneg (a 10), sq_nonneg (a 11)])
      (by simp [fourSquares]; nlinarith [sq_nonneg (a 12), sq_nonneg (a 13), sq_nonneg (a 14), sq_nonneg (a 15)])
  constructor
  · -- IntegerValued16 h_pos16
    intro a
    exact (positive_param_integer_valued.right.right)
      (fourSquaresPos (a 0) (a 1) (a 2) (a 3))
      (fourSquaresPos (a 4) (a 5) (a 6) (a 7))
      (fourSquaresPos (a 8) (a 9) (a 10) (a 11))
      (fourSquares (a 12) (a 13) (a 14) (a 15))
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 4), sq_nonneg (a 5), sq_nonneg (a 6), sq_nonneg (a 7)])
      (by simp [fourSquaresPos, fourSquares]; nlinarith [sq_nonneg (a 8), sq_nonneg (a 9), sq_nonneg (a 10), sq_nonneg (a 11)])
      (by simp [fourSquares]; nlinarith [sq_nonneg (a 12), sq_nonneg (a 13), sq_nonneg (a 14), sq_nonneg (a 15)])
  · -- Set equality
    ext ⟨x, y, z⟩
    simp only [Set.mem_setOf_eq]
    constructor
    · -- Forward: positive PT implies in the 16-parameter range
      rintro ⟨hx, hy, hz, h_pt⟩
      have h_eq := positive_pythagorean_parametrization.right.right.right
      have h_mem : (x, y, z) ∈ {(x, y, z) : ℤ × ℤ × ℤ | ∃ a b c d : ℤ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d ≥ 0 ∧
        (x : ℚ) = f_pos a b c d ∧ (y : ℚ) = g_pos a b c d ∧ (z : ℚ) = h_pos a b c d} := by
        rw [← h_eq]
        exact ⟨hx, hy, hz, h_pt⟩
      rcases h_mem with ⟨a, b, c, d, ha, hb, hc, hd, hx_eq, hy_eq, hz_eq⟩
      have h_a : ∃ a1 a2 a3 a4 : ℕ, (a - 1 : ℤ) = a1^2 + a2^2 + a3^2 + a4^2 := by
        have h_nonneg : a - 1 ≥ 0 := by omega
        have h_nat : ((a - 1).toNat : ℤ) = a - 1 := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h_sum := Nat.sum_four_squares (a - 1).toNat
        rcases h_sum with ⟨a1, a2, a3, a4, h_eq_nat⟩
        use a1, a2, a3, a4
        rw [← h_nat]
        exact_mod_cast h_eq_nat.symm
      have h_b : ∃ b1 b2 b3 b4 : ℕ, (b - 1 : ℤ) = b1^2 + b2^2 + b3^2 + b4^2 := by
        have h_nonneg : b - 1 ≥ 0 := by omega
        have h_nat : ((b - 1).toNat : ℤ) = b - 1 := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h_sum := Nat.sum_four_squares (b - 1).toNat
        rcases h_sum with ⟨b1, b2, b3, b4, h_eq_nat⟩
        use b1, b2, b3, b4
        rw [← h_nat]
        exact_mod_cast h_eq_nat.symm
      have h_c : ∃ c1 c2 c3 c4 : ℕ, (c - 1 : ℤ) = c1^2 + c2^2 + c3^2 + c4^2 := by
        have h_nonneg : c - 1 ≥ 0 := by omega
        have h_nat : ((c - 1).toNat : ℤ) = c - 1 := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h_sum := Nat.sum_four_squares (c - 1).toNat
        rcases h_sum with ⟨c1, c2, c3, c4, h_eq_nat⟩
        use c1, c2, c3, c4
        rw [← h_nat]
        exact_mod_cast h_eq_nat.symm
      have h_d : ∃ d1 d2 d3 d4 : ℕ, (d : ℤ) = d1^2 + d2^2 + d3^2 + d4^2 := by
        have h_nonneg : d ≥ 0 := hd
        have h_nat : (d.toNat : ℤ) = d := by
          rw [Int.toNat_of_nonneg h_nonneg]
        have h_sum := Nat.sum_four_squares d.toNat
        rcases h_sum with ⟨d1, d2, d3, d4, h_eq_nat⟩
        use d1, d2, d3, d4
        rw [← h_nat]
        exact_mod_cast h_eq_nat.symm
      rcases h_a with ⟨a1, a2, a3, a4, ha_eq⟩
      rcases h_b with ⟨b1, b2, b3, b4, hb_eq⟩
      rcases h_c with ⟨c1, c2, c3, c4, hc_eq⟩
      rcases h_d with ⟨d1, d2, d3, d4, hd_eq⟩
      let a' : Fin 16 → ℤ := fun i =>
        if i.val = 0 then (a1 : ℤ)
        else if i.val = 1 then (a2 : ℤ)
        else if i.val = 2 then (a3 : ℤ)
        else if i.val = 3 then (a4 : ℤ)
        else if i.val = 4 then (b1 : ℤ)
        else if i.val = 5 then (b2 : ℤ)
        else if i.val = 6 then (b3 : ℤ)
        else if i.val = 7 then (b4 : ℤ)
        else if i.val = 8 then (c1 : ℤ)
        else if i.val = 9 then (c2 : ℤ)
        else if i.val = 10 then (c3 : ℤ)
        else if i.val = 11 then (c4 : ℤ)
        else if i.val = 12 then (d1 : ℤ)
        else if i.val = 13 then (d2 : ℤ)
        else if i.val = 14 then (d3 : ℤ)
        else if i.val = 15 then (d4 : ℤ)
        else (0 : ℤ)
      use a'
      have ha' : fourSquaresPos (a' 0) (a' 1) (a' 2) (a' 3) = (a : ℤ) := by
        simp [a', fourSquaresPos, fourSquares]
        linarith
      have hb' : fourSquaresPos (a' 4) (a' 5) (a' 6) (a' 7) = (b : ℤ) := by
        simp [a', fourSquaresPos, fourSquares]
        linarith
      have hc' : fourSquaresPos (a' 8) (a' 9) (a' 10) (a' 11) = (c : ℤ) := by
        simp [a', fourSquaresPos, fourSquares]
        linarith
      have hd' : fourSquares (a' 12) (a' 13) (a' 14) (a' 15) = (d : ℤ) := by
        simp [a', fourSquares]
        linarith
      constructor
      · -- x = f_pos16 a'
        rw [hx_eq]
        simp [f_pos16, ha', hb', hc', hd']
      constructor
      · -- y = g_pos16 a'
        rw [hy_eq]
        simp [g_pos16, ha', hb', hc', hd']
      · -- z = h_pos16 a'
        rw [hz_eq]
        simp [h_pos16, ha', hb', hc', hd']
    · -- Backward: in the 16-parameter range implies positive PT
      rintro ⟨a, hx_eq, hy_eq, hz_eq⟩
      have h_eq := positive_pythagorean_parametrization.right.right.right
      have h_mem : (x, y, z) ∈ {(x, y, z) : ℤ × ℤ × ℤ | x > 0 ∧ y > 0 ∧ z > 0 ∧ PythagoreanTriple x y z} := by
        rw [h_eq]
        use fourSquaresPos (a 0) (a 1) (a 2) (a 3),
            fourSquaresPos (a 4) (a 5) (a 6) (a 7),
            fourSquaresPos (a 8) (a 9) (a 10) (a 11),
            fourSquares (a 12) (a 13) (a 14) (a 15)
        constructor
        · simp [fourSquaresPos, fourSquares]
          nlinarith [sq_nonneg (a 0), sq_nonneg (a 1), sq_nonneg (a 2), sq_nonneg (a 3)]
        constructor
        · simp [fourSquaresPos, fourSquares]
          nlinarith [sq_nonneg (a 4), sq_nonneg (a 5), sq_nonneg (a 6), sq_nonneg (a 7)]
        constructor
        · simp [fourSquaresPos, fourSquares]
          nlinarith [sq_nonneg (a 8), sq_nonneg (a 9), sq_nonneg (a 10), sq_nonneg (a 11)]
        constructor
        · simp [fourSquares]
          nlinarith [sq_nonneg (a 12), sq_nonneg (a 13), sq_nonneg (a 14), sq_nonneg (a 15)]
        constructor
        · rw [hx_eq]
          simp [f_pos16]
        constructor
        · rw [hy_eq]
          simp [g_pos16]
        · rw [hz_eq]
          simp [h_pos16]
      exact h_mem

/-! ## No integer-coefficient polynomial parametrization (Remark, line-143)

The source proves that no single triple of polynomials with integer coefficients
in any number of variables can parametrize all Pythagorean triples.
-/

/-- There do not exist `f,g,h ∈ ℤ[x₁,…,xₙ]` (for any `n`) that parametrize all PTs.

Source proof: Suppose `(f,g,h)` parametrizes PTs. In the UFD `ℤ[x]`, let `d = gcd(g,h)`.
Then `d | f` and setting `φ=f/d`, `ψ=g/d`, `θ=h/d` gives `φ² = (θ+ψ)(θ-ψ)`.
The gcd of `θ+ψ` and `θ-ψ` is 1 or 2; it cannot be 2 because of `(3,4,5)`.
So `θ+ψ` and `θ-ψ` are coprime squares, yielding `θ=(s²+t²)/2`, `ψ=(s²-t²)/2`.
Then `ψ` is divisible by 2, contradicting `(4,3,5)`.
-/
theorem no_integer_polynomial_parametrization (n : ℕ) :
    ¬∃ (f g h : MvPolynomial (Fin n) ℤ),
      {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} =
      Set.range (fun (a : Fin n → ℤ) => (eval a f, eval a g, eval a h)) := by
  rintro ⟨f, g, h, heq⟩
  have h1 : ∀ a : Fin n → ℤ, PythagoreanTriple (eval a f) (eval a g) (eval a h) := by
    intro a
    have : (eval a f, eval a g, eval a h) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := by
      rw [heq]
      exact Set.mem_range_self a
    simpa using this
  by_cases hn : n = 0
  · -- n = 0: f, g, h are constants, so the range is a single triple.
    -- But there exist at least two distinct PTs, e.g. (0,0,0) and (3,4,5).
    subst hn
    have h00 : PythagoreanTriple 0 0 0 := by norm_num [PythagoreanTriple]
    have h345 : PythagoreanTriple 3 4 5 := by norm_num [PythagoreanTriple]
    have h00_in : (0, 0, 0) ∈ Set.range (fun (a : Fin 0 → ℤ) => (eval a f, eval a g, eval a h)) := by
      rw [← heq]
      simpa using h00
    have h345_in : (3, 4, 5) ∈ Set.range (fun (a : Fin 0 → ℤ) => (eval a f, eval a g, eval a h)) := by
      rw [← heq]
      simpa using h345
    obtain ⟨a, ha⟩ := h00_in
    obtain ⟨b, hb⟩ := h345_in
    have hab : a = b := by funext i; exact Fin.elim0 i
    rw [hab] at ha
    have h_eq : ((0 : ℤ), (0 : ℤ), (0 : ℤ)) = ((3 : ℤ), (4 : ℤ), (5 : ℤ)) := by
      have h1 : (eval b f, eval b g, eval b h) = ((0 : ℤ), (0 : ℤ), (0 : ℤ)) := by
        simpa using ha
      have h2 : (eval b f, eval b g, eval b h) = ((3 : ℤ), (4 : ℤ), (5 : ℤ)) := by
        simpa using hb
      exact h1.symm.trans h2
    simp at h_eq
  by_cases hn1 : n = 1
  · -- n = 1: univariate polynomials.
    subst hn1
    -- For every k, (3k, 4k, 5k) is in the range
    have h35 (k : ℤ) : ∃ a : Fin 1 → ℤ, eval a f = 3 * k ∧ eval a g = 4 * k ∧ eval a h = 5 * k := by
      have h_pt : PythagoreanTriple (3 * k) (4 * k) (5 * k) := by
        norm_num [PythagoreanTriple]
        <;> ring
      have : (3 * k, 4 * k, 5 * k) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
      rw [heq] at this
      obtain ⟨a, ha⟩ := this
      use a
      simp [Prod.ext_iff] at ha
      exact ⟨ha.1, ha.2.1, ha.2.2⟩
    -- For every k, (5k, 12k, 13k) is in the range
    have h51213 (k : ℤ) : ∃ a : Fin 1 → ℤ, eval a f = 5 * k ∧ eval a g = 12 * k ∧ eval a h = 13 * k := by
      have h_pt : PythagoreanTriple (5 * k) (12 * k) (13 * k) := by
        norm_num [PythagoreanTriple]
        <;> ring
      have : (5 * k, 12 * k, 13 * k) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
      rw [heq] at this
      obtain ⟨a, ha⟩ := this
      use a
      simp [Prod.ext_iff] at ha
      exact ⟨ha.1, ha.2.1, ha.2.2⟩
    -- Restate to get integer witnesses directly
    have h35' (k : ℤ) : ∃ r : ℤ, eval (fun _ => r) f = 3 * k ∧ eval (fun _ => r) g = 4 * k ∧ eval (fun _ => r) h = 5 * k := by
      obtain ⟨a, ha⟩ := h35 k
      use a 0
      have hf : eval (fun _ => a 0) f = eval a f := by
        congr; funext i; fin_cases i; simp
      have hg : eval (fun _ => a 0) g = eval a g := by
        congr; funext i; fin_cases i; simp
      have hh : eval (fun _ => a 0) h = eval a h := by
        congr; funext i; fin_cases i; simp
      rw [hf, hg, hh]
      exact ha
    have h51213' (k : ℤ) : ∃ r : ℤ, eval (fun _ => r) f = 5 * k ∧ eval (fun _ => r) g = 12 * k ∧ eval (fun _ => r) h = 13 * k := by
      obtain ⟨a, ha⟩ := h51213 k
      use a 0
      have hf : eval (fun _ => a 0) f = eval a f := by
        congr; funext i; fin_cases i; simp
      have hg : eval (fun _ => a 0) g = eval a g := by
        congr; funext i; fin_cases i; simp
      have hh : eval (fun _ => a 0) h = eval a h := by
        congr; funext i; fin_cases i; simp
      rw [hf, hg, hh]
      exact ha
    choose r1 hr1 using h35'
    choose r2 hr2 using h51213'
    -- r1 is injective because h(r1(k)) = 5k
    have hr1_inj : Function.Injective r1 := by
      intro k l h_eq
      have hk : eval (fun _ => r1 k) h = 5 * k := (hr1 k).2.2
      have hl : eval (fun _ => r1 l) h = 5 * l := (hr1 l).2.2
      rw [show r1 k = r1 l by exact h_eq] at hk
      linarith
    -- r2 is injective because h(r2(k)) = 13k
    have hr2_inj : Function.Injective r2 := by
      intro k l h_eq
      have hk : eval (fun _ => r2 k) h = 13 * k := (hr2 k).2.2
      have hl : eval (fun _ => r2 l) h = 13 * l := (hr2 l).2.2
      rw [show r2 k = r2 l by exact h_eq] at hk
      linarith
    -- Helper: if a MvPolynomial (Fin 1) ℤ vanishes on infinitely many inputs, it is zero
    have mvPoly_eq_zero_of_infinite_roots (p : MvPolynomial (Fin 1) ℤ)
        (r : ℤ → ℤ) (hr_inj : Function.Injective r)
        (hroots : ∀ k, eval (fun _ => r k) p = 0) : p = 0 := by
      -- Use MvPolynomial.funext_set: if p=q on a product of infinite sets, then p=q
      -- For Fin 1, we need one infinite set S ⊆ ℤ such that p vanishes on S
      -- The range of r is infinite since r is injective
      have h_inf : Set.Infinite (Set.range r) := by
        apply Set.infinite_range_of_injective
        exact hr_inj
      have h_zero : ∀ x ∈ Set.univ.pi (fun _ => Set.range r), eval x p = eval x 0 := by
        intro x hx
        have hx0 : x 0 ∈ Set.range r := hx 0 (Set.mem_univ 0)
        obtain ⟨k, hk⟩ := hx0
        have : x = fun _ => r k := by
          funext i
          fin_cases i
          simpa using hk.symm
        rw [this]
        simp [hroots k]
      exact MvPolynomial.funext_set (fun _ => Set.range r) (fun _ => h_inf) h_zero
    -- 3h - 5f = 0 as MvPolynomials (infinitely many roots from r1)
    have h_eq1 : 3 * h - 5 * f = 0 := by
      apply mvPoly_eq_zero_of_infinite_roots (3 * h - 5 * f) r1 hr1_inj
      intro k
      have hk_f : eval (fun _ => r1 k) f = 3 * k := (hr1 k).1
      have hk_h : eval (fun _ => r1 k) h = 5 * k := (hr1 k).2.2
      simp [hk_f, hk_h]
      ring
    -- 5h - 13f = 0 as MvPolynomials (infinitely many roots from r2)
    have h_eq2 : 5 * h - 13 * f = 0 := by
      apply mvPoly_eq_zero_of_infinite_roots (5 * h - 13 * f) r2 hr2_inj
      intro k
      have hk_f : eval (fun _ => r2 k) f = 5 * k := (hr2 k).1
      have hk_h : eval (fun _ => r2 k) h = 13 * k := (hr2 k).2.2
      simp [hk_f, hk_h]
      ring
    -- From 3h = 5f and 5h = 13f as MvPolynomials, derive contradiction
    have h1 : 3 * h = 5 * f := by
      have h_eq : 3 * h - 5 * f = 0 := h_eq1
      calc
        3 * h = 3 * h - 5 * f + 5 * f := by ring
        _ = 0 + 5 * f := by rw [h_eq]
        _ = 5 * f := by ring
    have h2 : 5 * h = 13 * f := by
      have h_eq : 5 * h - 13 * f = 0 := h_eq2
      calc
        5 * h = 5 * h - 13 * f + 13 * f := by ring
        _ = 0 + 13 * f := by rw [h_eq]
        _ = 13 * f := by ring
    -- Evaluate 3*h = 5*f at r2(k): 3*(13*k) = 5*(5*k), so 14*k = 0 for all k
    have h_contra : ∀ k : ℤ, 14 * k = 0 := by
      intro k
      have h_eq1_at_r2k : eval (fun _ => r2 k) (3 * h) = eval (fun _ => r2 k) (5 * f) := by
        rw [h1]
      have h3h : eval (fun _ => r2 k) (3 * h) = 39 * k := by
        have hh : eval (fun _ => r2 k) h = 13 * k := (hr2 k).2.2
        have h3 : (3 : MvPolynomial (Fin 1) ℤ) = C (3 : ℤ) := by rfl
        rw [h3, eval_mul, eval_C, hh]
        ring
      have h5f : eval (fun _ => r2 k) (5 * f) = 25 * k := by
        have hf : eval (fun _ => r2 k) f = 5 * k := (hr2 k).1
        have h5 : (5 : MvPolynomial (Fin 1) ℤ) = C (5 : ℤ) := by rfl
        rw [h5, eval_mul, eval_C, hf]
        ring
      rw [h3h, h5f] at h_eq1_at_r2k
      linarith
    -- Contradiction: 14 * 1 = 0 is false
    have h_false : 14 * (1 : ℤ) = 0 := h_contra 1
    norm_num at h_false
  · -- n ≥ 2: UFD proof following the source blueprint.
    have hn2 : n ≥ 2 := by omega
    -- Establish the polynomial identity f² + g² = h² in ℤ[x₁,…,xₙ]
    have h_poly_eq : f^2 + g^2 = h^2 := by
      have h_eq : ∀ a : Fin n → ℤ, eval a (f^2 + g^2) = eval a (h^2) := by
        intro a
        have h_pt : PythagoreanTriple (eval a f) (eval a g) (eval a h) := h1 a
        simp [PythagoreanTriple, pow_two] at h_pt ⊢
        linarith
      exact MvPolynomial.funext h_eq
    -- Use the UFD structure: ℤ[x₁,…,xₙ] is a UFD, hence has a GCD monoid structure
    letI : GCDMonoid (MvPolynomial (Fin n) ℤ) := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin n) ℤ)
    -- Let d = gcd(g, h). Then d | g and d | h.
    let d := GCDMonoid.gcd g h
    have hdg : d ∣ g := GCDMonoid.gcd_dvd_left g h
    have hdh : d ∣ h := GCDMonoid.gcd_dvd_right g h
    -- Since f² + g² = h², we have f² = h² - g² = (h+g)(h-g).
    -- Also d² | g² and d² | h², so d² | f², which implies d | f in a UFD.
    have hdf : d ∣ f := by
      have heq2 : f^2 = h^2 - g^2 := by rw [← h_poly_eq]; ring
      have hdvd : d^2 ∣ h^2 - g^2 := by
        have h1 : d ∣ h := hdh
        have h2 : d ∣ g := hdg
        have h3 : d^2 ∣ h^2 := by
          obtain ⟨q, hq⟩ := h1
          use q^2
          rw [hq]
          ring
        have h4 : d^2 ∣ g^2 := by
          obtain ⟨q, hq⟩ := h2
          use q^2
          rw [hq]
          ring
        exact dvd_sub h3 h4
      rw [← heq2] at hdvd
      -- In a UFD, if d² | f² then d | f
      have hd_ne : d ≠ 0 := by
        by_contra h0
        rw [h0] at hdg
        have hg0 : g = 0 := by simpa using hdg
        have h345 : ∃ a, eval a g = 3 := by
          have h_pt : PythagoreanTriple 4 3 5 := by norm_num [PythagoreanTriple]
          have h_in_set : (4, 3, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
          rw [heq] at h_in_set
          rcases h_in_set with ⟨a, ha⟩
          use a
          simp at ha ⊢
          linarith
        rcases h345 with ⟨a, ha⟩
        have h_zero : eval a g = 0 := by rw [hg0]; simp
        linarith
      have hf_ne : f ≠ 0 := by
        by_contra h0
        have h345 : ∃ a, eval a f = 4 := by
          have h_pt : PythagoreanTriple 4 3 5 := by norm_num [PythagoreanTriple]
          have h_in_set : (4, 3, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
          rw [heq] at h_in_set
          rcases h_in_set with ⟨a, ha⟩
          use a
          simp at ha ⊢
          linarith
        rcases h345 with ⟨a, ha⟩
        have h_zero : eval a f = 0 := by
          rw [h0]
          simp
        linarith [ha, h_zero]
      -- In a UFD, if d² | f² then d | f
      have h_dvd_f : d ∣ f := by
        have h1 : d^2 ∣ f^2 := hdvd
        have hdn : d ≠ 0 := hd_ne
        have hfn : f ≠ 0 := hf_ne
        -- Need NormalizationMonoid instance for MvPolynomial
        letI : NormalizationMonoid (MvPolynomial (Fin n) ℤ) := UniqueFactorizationMonoid.normalizationMonoid
        -- Use normalized factors: d² | f² implies normalizedFactors(d²) ≤ normalizedFactors(f²)
        -- which means 2 • normalizedFactors(d) ≤ 2 • normalizedFactors(f)
        -- which implies normalizedFactors(d) ≤ normalizedFactors(f), so d | f
        rw [dvd_iff_normalizedFactors_le_normalizedFactors hdn hfn]
        rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hdn) (pow_ne_zero 2 hfn)] at h1
        rw [normalizedFactors_pow, normalizedFactors_pow] at h1
        apply Multiset.le_iff_count.2
        intro x
        have hcount := Multiset.le_iff_count.1 h1 x
        simp [Multiset.count_nsmul] at hcount ⊢
        omega
      exact h_dvd_f
    -- Define φ = f/d, ψ = g/d, θ = h/d
    obtain ⟨φ, hφ⟩ := hdf
    obtain ⟨ψ, hψ⟩ := hdg
    obtain ⟨θ, hθ⟩ := hdh
    -- Then φ² = (θ+ψ)(θ-ψ) (after clearing denominators)
    have h_phi_sq : φ^2 = (θ + ψ) * (θ - ψ) := by
      have h1 : f = d * φ := by rw [hφ]
      have h2 : g = d * ψ := by rw [hψ]
      have h3 : h = d * θ := by rw [hθ]
      have h4 : (d * φ)^2 + (d * ψ)^2 = (d * θ)^2 := by
        rw [← h1, ← h2, ← h3]
        exact h_poly_eq
      have h5 : d^2 * (φ^2 + ψ^2) = d^2 * θ^2 := by
        have h_left : (d * φ)^2 + (d * ψ)^2 = d^2 * (φ^2 + ψ^2) := by ring
        have h_right : (d * θ)^2 = d^2 * θ^2 := by ring
        rw [h_left, h_right] at h4
        exact h4
      have h6 : φ^2 + ψ^2 = θ^2 := by
        have hd2_ne : d^2 ≠ 0 := by
          have hd_ne : d ≠ 0 := by
            by_contra h0
            have hg0 : g = 0 := by
              rw [h0] at hψ
              simp at hψ
              exact hψ
            have h345 : ∃ a, eval a g = 3 := by
              have h_pt : PythagoreanTriple 4 3 5 := by norm_num [PythagoreanTriple]
              have h_in_set : (4, 3, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
              rw [heq] at h_in_set
              rcases h_in_set with ⟨a, ha⟩
              use a
              simp at ha ⊢
              linarith
            rcases h345 with ⟨a, ha⟩
            have h_zero : eval a g = 0 := by rw [hg0]; simp
            linarith
          intro h0
          have : d = 0 := by
            have : d^2 = 0 := by simpa using h0
            simp at this
            exact this
          contradiction
        apply (mul_right_inj' hd2_ne).mp
        exact h5
      have h7 : φ^2 = θ^2 - ψ^2 := by
        rw [← h6]
        ring
      have h8 : (θ + ψ) * (θ - ψ) = θ^2 - ψ^2 := by ring
      rw [h7]
      rw [h8]
    -- Now we have φ² = (θ+ψ)(θ-ψ). We analyze gcd(θ+ψ, θ-ψ).
    -- Key insight: any common divisor of θ+ψ and θ-ψ divides both 2θ and 2ψ.
    -- Since gcd(θ,ψ) = 1 (by construction: d = gcd(g,h), ψ = g/d, θ = h/d),
    -- any common divisor must divide 2.
    --
    -- First, we show 2 ∤ (θ+ψ) as a polynomial by evaluating at a point where it's odd.
    have h2_not_dvd : ¬(2 : MvPolynomial (Fin n) ℤ) ∣ (θ + ψ) := by
      -- At the point (3,4,5), we have g=4, h=5, so d=gcd(4,5)=1, θ=5, ψ=4, θ+ψ=9
      have h_pt : PythagoreanTriple 3 4 5 := by norm_num [PythagoreanTriple]
      have h_in_set : (3, 4, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
      rw [heq] at h_in_set
      rcases h_in_set with ⟨b, hb⟩
      intro h_dvd
      have dvd_eval {p q : MvPolynomial (Fin n) ℤ} (hpq : p ∣ q) (a : Fin n → ℤ) : eval a p ∣ eval a q := by
        rcases hpq with ⟨r, hr⟩
        use eval a r
        rw [hr, eval_mul]
      have h_eval : eval b (θ + ψ) = 9 ∨ eval b (θ + ψ) = -9 := by
        simp at hb ⊢
        have h1 : eval b g = 4 := by linarith [hb]
        have h2 : eval b h = 5 := by linarith [hb]
        have hdg : d ∣ g := GCDMonoid.gcd_dvd_left g h
        have hdh : d ∣ h := GCDMonoid.gcd_dvd_right g h
        have h4 : eval b d ∣ eval b g := dvd_eval hdg b
        have h5 : eval b d ∣ eval b h := dvd_eval hdh b
        rw [h1] at h4
        rw [h2] at h5
        have h6 : eval b d = 1 ∨ eval b d = -1 := by
          have h4' : eval b d ∣ 4 := h4
          have h5' : eval b d ∣ 5 := h5
          have h7 : eval b d ∣ (1 : ℤ) := by
            have h8 : eval b d ∣ (5 : ℤ) := h5'
            have h9 : eval b d ∣ (4 : ℤ) := h4'
            have h10 : eval b d ∣ (5 - 4 : ℤ) := by exact dvd_sub h8 h9
            norm_num at h10 ⊢
            exact h10
          have h8 : eval b d ≤ 1 := by exact Int.le_of_dvd (by norm_num) h7
          have h9 : eval b d ≥ -1 := by
            have h10 : -eval b d ∣ 1 := Int.neg_dvd.2 h7
            have h11 : -eval b d ≤ 1 := by exact Int.le_of_dvd (by norm_num) h10
            linarith
          have h10 : eval b d = 0 ∨ eval b d = 1 ∨ eval b d = -1 := by omega
          rcases h10 with (h10 | h10 | h10)
          · rw [h10] at h7; norm_num at h7
          · left; exact h10
          · right; exact h10
        rcases h6 with (h6 | h6)
        · -- eval b d = 1
          have h4 : eval b θ = 5 := by
            have h5 : eval b h = eval b d * eval b θ := by
              rw [hθ]; simp [eval_mul]
            rw [h6] at h5; linarith [h2, h5]
          have h5 : eval b ψ = 4 := by
            have h6' : eval b g = eval b d * eval b ψ := by
              rw [hψ]; simp [eval_mul]
            rw [h6] at h6'; linarith [h1, h6']
          left
          linarith [h4, h5]
        · -- eval b d = -1
          have h4 : eval b θ = -5 := by
            have h5 : eval b h = eval b d * eval b θ := by
              rw [hθ]; simp [eval_mul]
            rw [h6] at h5; linarith [h2, h5]
          have h5 : eval b ψ = -4 := by
            have h6' : eval b g = eval b d * eval b ψ := by
              rw [hψ]; simp [eval_mul]
            rw [h6] at h6'; linarith [h1, h6']
          right
          linarith [h4, h5]
      have h_odd : ¬(2 ∣ eval b (θ + ψ)) := by
        rcases h_eval with (h | h)
        · rw [h]; norm_num
        · rw [h]; norm_num
      have h_even : 2 ∣ eval b (θ + ψ) := by
        have h : (eval b) (2 : MvPolynomial (Fin n) ℤ) = (2 : ℤ) := by simp
        have h' : (eval b) (2 : MvPolynomial (Fin n) ℤ) ∣ (eval b) (θ + ψ) := dvd_eval h_dvd b
        rw [h] at h'
        exact h'
      contradiction
    -- Since 2 ∤ (θ+ψ), and any common divisor of θ+ψ and θ-ψ divides 2,
    -- we conclude gcd(θ+ψ, θ-ψ) = 1 (they're coprime).
    --
    -- In a UFD, if φ² = (θ+ψ)(θ-ψ) and gcd(θ+ψ, θ-ψ) = 1, then each factor is a square up to unit.
    -- The units in ℤ[x₁,…,xₙ] are ±1.
    --
    -- But θ+ψ evaluates to 8 at the point (4,3,5), and 8 is not ± a perfect square.
    -- This is a contradiction!
    have h_pt2 : PythagoreanTriple 4 3 5 := by norm_num [PythagoreanTriple]
    have h_in_set2 : (4, 3, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt2
    rw [heq] at h_in_set2
    rcases h_in_set2 with ⟨a, ha⟩
    have h_eval_a : eval a (θ + ψ) = 8 ∨ eval a (θ + ψ) = -8 := by
      simp at ha ⊢
      have h1 : eval a g = 3 := by linarith [ha]
      have h2 : eval a h = 5 := by linarith [ha]
      have dvd_eval {p q : MvPolynomial (Fin n) ℤ} (hpq : p ∣ q) (a : Fin n → ℤ) : eval a p ∣ eval a q := by
        rcases hpq with ⟨r, hr⟩
        use eval a r
        rw [hr, eval_mul]
      have h4 : eval a d ∣ eval a g := dvd_eval (GCDMonoid.gcd_dvd_left g h) a
      have h5 : eval a d ∣ eval a h := dvd_eval (GCDMonoid.gcd_dvd_right g h) a
      rw [h1] at h4
      rw [h2] at h5
      have h6 : eval a d = 1 ∨ eval a d = -1 := by
        have h4' : eval a d ∣ 3 := h4
        have h5' : eval a d ∣ 5 := h5
        have h7 : eval a d ∣ (2 : ℤ) := by
          have h8 : eval a d ∣ (5 : ℤ) := h5'
          have h9 : eval a d ∣ (3 : ℤ) := h4'
          have h10 : eval a d ∣ (5 - 3 : ℤ) := by exact dvd_sub h8 h9
          norm_num at h10 ⊢
          exact h10
        have h8 : eval a d ≤ 2 := by exact Int.le_of_dvd (by norm_num) h7
        have h9 : eval a d ≥ -2 := by
          have h10 : -eval a d ∣ 2 := Int.neg_dvd.2 h7
          have h11 : -eval a d ≤ 2 := by exact Int.le_of_dvd (by norm_num) h10
          linarith
        have h10 : eval a d = -2 ∨ eval a d = -1 ∨ eval a d = 1 ∨ eval a d = 2 := by
          have h11 : eval a d ≤ 2 := h8
          have h12 : eval a d ≥ -2 := h9
          interval_cases eval a d <;> tauto
        rcases h10 with (h10 | h10 | h10 | h10)
        · rw [h10] at h4'; norm_num at h4'
        · right; exact h10
        · left; exact h10
        · rw [h10] at h4'; norm_num at h4'
      rcases h6 with (h6 | h6)
      · -- eval a d = 1
        have h4 : eval a θ = 5 := by
          have h5 : eval a h = eval a d * eval a θ := by
            rw [hθ]; simp [eval_mul]
          rw [h6] at h5; linarith [h2, h5]
        have h5 : eval a ψ = 3 := by
          have h6' : eval a g = eval a d * eval a ψ := by
            rw [hψ]; simp [eval_mul]
          rw [h6] at h6'; linarith [h1, h6']
        left
        linarith [h4, h5]
      · -- eval a d = -1
        have h4 : eval a θ = -5 := by
          have h5 : eval a h = eval a d * eval a θ := by
            rw [hθ]; simp [eval_mul]
          rw [h6] at h5; linarith [h2, h5]
        have h5 : eval a ψ = -3 := by
          have h6' : eval a g = eval a d * eval a ψ := by
            rw [hψ]; simp [eval_mul]
          rw [h6] at h6'; linarith [h1, h6']
        right
        linarith [h4, h5]
    -- Key contradiction: in a UFD, if φ² = (θ+ψ)(θ-ψ) and gcd(θ+ψ, θ-ψ) = 1,
    -- then θ+ψ = u * s² for some unit u. But eval a (θ+ψ) = ±8 is not ±(square).
    -- First prove gcd(θ, ψ) is a unit (since d = gcd(g,h) and ψ = g/d, θ = h/d).
    have h_gcd_ψ_θ : IsUnit (GCDMonoid.gcd ψ θ) := by
      have h1 : g = d * ψ := by rw [hψ]
      have h2 : h = d * θ := by rw [hθ]
      have hd_eq : d = GCDMonoid.gcd g h := by rfl
      have h3 : g = GCDMonoid.gcd g h * ψ := by rw [hd_eq] at h1; exact h1
      have h4 : h = GCDMonoid.gcd g h * θ := by rw [hd_eq] at h2; exact h2
      apply isUnit_gcd_of_eq_mul_gcd h3 h4
      by_contra h0
      rw [h0] at h3
      simp at h3
      have hg0 : g = 0 := by exact h3
      have h345 : ∃ a, eval a g = 3 := by
        have h_pt : PythagoreanTriple 4 3 5 := by norm_num [PythagoreanTriple]
        have h_in_set : (4, 3, 5) ∈ {(x, y, z) : ℤ × ℤ × ℤ | PythagoreanTriple x y z} := h_pt
        rw [heq] at h_in_set
        rcases h_in_set with ⟨a, ha⟩
        use a
        simp at ha ⊢
        linarith
      rcases h345 with ⟨a, ha⟩
      have h_zero : eval a g = 0 := by rw [hg0]; simp
      linarith
    -- Any common divisor of θ+ψ and θ-ψ divides 2θ and 2ψ, hence divides 2.
    -- Since 2 ∤ (θ+ψ) (proven above), gcd(θ+ψ, θ-ψ) is a unit.
    have h_coprime : IsUnit (GCDMonoid.gcd (θ + ψ) (θ - ψ)) := by
      by_contra h
      have h_gcd_ne_zero : GCDMonoid.gcd (θ + ψ) (θ - ψ) ≠ 0 := by
        by_contra h0
        have h1 : θ + ψ = 0 := by
          have h2 : GCDMonoid.gcd (θ + ψ) (θ - ψ) ∣ θ + ψ := GCDMonoid.gcd_dvd_left (θ + ψ) (θ - ψ)
          rw [h0] at h2
          simpa using h2
        have h_eval_zero : eval a (θ + ψ) = 0 := by
          rw [h1]
          simp
        rcases h_eval_a with (h_eval_a | h_eval_a)
        · rw [h_eval_a] at h_eval_zero
          norm_num at h_eval_zero
        · rw [h_eval_a] at h_eval_zero
          norm_num at h_eval_zero
      -- In a UFD, a non-unit has an irreducible (hence prime) factor
      obtain ⟨p, hp_irr, hp_dvd⟩ := WfDvdMonoid.exists_irreducible_factor h h_gcd_ne_zero
      have hp_prime : Prime p := Irreducible.prime hp_irr
      have hp1 : p ∣ θ + ψ := dvd_trans hp_dvd (GCDMonoid.gcd_dvd_left (θ + ψ) (θ - ψ))
      have hp2 : p ∣ θ - ψ := dvd_trans hp_dvd (GCDMonoid.gcd_dvd_right (θ + ψ) (θ - ψ))
      have hp2θ : p ∣ 2 * θ := by
        have h1 : p ∣ (θ + ψ) + (θ - ψ) := by
          apply dvd_add hp1 hp2
        have h2 : (θ + ψ) + (θ - ψ) = 2 * θ := by ring
        rw [h2] at h1
        exact h1
      have hp2ψ : p ∣ 2 * ψ := by
        have h1 : p ∣ (θ + ψ) - (θ - ψ) := by
          apply dvd_sub hp1 hp2
        have h2 : (θ + ψ) - (θ - ψ) = 2 * ψ := by ring
        rw [h2] at h1
        exact h1
      by_cases hp2' : p ∣ (2 : MvPolynomial (Fin n) ℤ)
      · -- p | 2, and 2 is prime, so p ~ 2, hence 2 | θ+ψ
        have h2_prime : Prime (2 : MvPolynomial (Fin n) ℤ) := by
          rw [show (2 : MvPolynomial (Fin n) ℤ) = C (2 : ℤ) by simp]
          rw [MvPolynomial.prime_C_iff]
          exact Int.prime_two
        have h_p_assoc_2 : Associated p 2 := by
          apply Prime.associated_of_dvd hp_prime h2_prime hp2'
        -- From p ~ 2 and p | θ+ψ, we get 2 | θ+ψ
        have h2_dvd_θψ : (2 : MvPolynomial (Fin n) ℤ) ∣ θ + ψ := by
          -- Associated p 2 means 2 | p (and p | 2)
          have h2_dvd_p : (2 : MvPolynomial (Fin n) ℤ) ∣ p := by
            exact h_p_assoc_2.dvd'
          -- And p | θ + ψ, so by transitivity 2 | θ + ψ
          exact dvd_trans h2_dvd_p hp1
        contradiction
      · -- p ∤ 2, so by primality p | θ and p | ψ
        have hθ : p ∣ θ := by
          cases hp_prime.dvd_or_dvd hp2θ with
          | inl h => exfalso; exact hp2' h
          | inr h => exact h
        have hψ : p ∣ ψ := by
          cases hp_prime.dvd_or_dvd hp2ψ with
          | inl h => exfalso; exact hp2' h
          | inr h => exact h
        have hp_gcd : p ∣ GCDMonoid.gcd ψ θ := dvd_gcd hψ hθ
        have hp_unit : IsUnit p := by
          exact isUnit_of_dvd_unit hp_gcd h_gcd_ψ_θ
        exact hp_prime.not_unit hp_unit
    -- In a GCD monoid, coprime factors whose product is a power are each powers up to unit.
    have h_sq : ∃ (u : MvPolynomial (Fin n) ℤ) (s : MvPolynomial (Fin n) ℤ),
        IsUnit u ∧ θ + ψ = u * s^2 := by
      have h1 : (θ + ψ) * (θ - ψ) = φ^2 := by rw [h_phi_sq]
      obtain ⟨s, hs⟩ := exists_associated_pow_of_mul_eq_pow h_coprime h1
      -- hs : Associated (s^2) (θ + ψ), meaning ∃ u : Mˣ, s^2 * u = θ + ψ
      rcases hs with ⟨u, hs_eq⟩
      use ↑u, s
      constructor
      · exact Units.isUnit u
      · have h2 : s^2 * ↑u = θ + ψ := by exact hs_eq
        have h3 : θ + ψ = ↑u * s^2 := by
          rw [← h2]
          simp [mul_comm]
        exact h3
    -- Evaluate at point a: θ+ψ = u * s² means eval a (θ+ψ) = eval a u * (eval a s)² = ±(square).
    -- But eval a (θ+ψ) = 8 or -8, neither of which is ±(square). Contradiction!
    rcases h_sq with ⟨u, s, hu, hsq⟩
    have h_eval_sq : eval a (θ + ψ) = eval a u * (eval a s)^2 := by
      rw [hsq]
      simp [eval_mul]
    have h_u_val : eval a u = 1 ∨ eval a u = -1 := by
      have h_unit : IsUnit (eval a u) := by
        apply RingHom.isUnit_map
        exact hu
      have : eval a u = 1 ∨ eval a u = -1 := by
        have h1 : eval a u ∣ 1 := by
          exact isUnit_iff_dvd_one.1 h_unit
        have h2 : eval a u ≤ 1 := by exact Int.le_of_dvd (by norm_num) h1
        have h3 : eval a u ≥ -1 := by
          have h4 : -eval a u ∣ 1 := Int.neg_dvd.2 h1
          have h5 : -eval a u ≤ 1 := by exact Int.le_of_dvd (by norm_num) h4
          linarith
        have h4 : eval a u = 0 ∨ eval a u = 1 ∨ eval a u = -1 := by omega
        rcases h4 with (h4 | h4 | h4)
        · rw [h4] at h1; norm_num at h1
        · left; exact h4
        · right; exact h4
      exact this
    rcases h_eval_a with (h_eval_a | h_eval_a)
    · -- eval a (θ + ψ) = 8
      rw [h_eval_a] at h_eval_sq
      rcases h_u_val with (h_u_val | h_u_val)
      · -- u = 1, so 8 = (eval a s)², impossible
        rw [h_u_val] at h_eval_sq
        have h8 : IsSquare (8 : ℤ) := by
          use eval a s
          linarith
        exfalso
        have h_not_sq : ¬IsSquare (8 : ℤ) := by
          intro h
          rcases h with ⟨k, hk⟩
          have h1 : k ≤ 3 := by nlinarith
          have h2 : k ≥ -3 := by nlinarith
          interval_cases k <;> norm_num at hk
        exact h_not_sq h8
      · -- u = -1, so 8 = -(eval a s)², impossible
        rw [h_u_val] at h_eval_sq
        have h8 : IsSquare (-8 : ℤ) := by
          use eval a s
          linarith
        exfalso
        have h_not_sq : ¬IsSquare (-8 : ℤ) := by
          intro h
          rcases h with ⟨k, hk⟩
          have h1 : k ≤ 3 := by nlinarith
          have h2 : k ≥ -3 := by nlinarith
          interval_cases k <;> norm_num at hk
        exact h_not_sq h8
    · -- eval a (θ + ψ) = -8
      rw [h_eval_a] at h_eval_sq
      rcases h_u_val with (h_u_val | h_u_val)
      · -- u = 1, so -8 = (eval a s)², impossible
        rw [h_u_val] at h_eval_sq
        have h8 : IsSquare (-8 : ℤ) := by
          use eval a s
          linarith
        exfalso
        have h_not_sq : ¬IsSquare (-8 : ℤ) := by
          intro h
          rcases h with ⟨k, hk⟩
          have h1 : k ≤ 3 := by nlinarith
          have h2 : k ≥ -3 := by nlinarith
          interval_cases k <;> norm_num at hk
        exact h_not_sq h8
      · -- u = -1, so -8 = -(eval a s)², so 8 = (eval a s)², impossible
        rw [h_u_val] at h_eval_sq
        have h8 : IsSquare (8 : ℤ) := by
          use eval a s
          linarith
        exfalso
        have h_not_sq : ¬IsSquare (8 : ℤ) := by
          intro h
          rcases h with ⟨k, hk⟩
          have h1 : k ≤ 3 := by nlinarith
          have h2 : k ≥ -3 := by nlinarith
          interval_cases k <;> norm_num at hk
        exact h_not_sq h8
