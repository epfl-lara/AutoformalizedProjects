import Mathlib

namespace IMO2026P2

theorem quadratic_identity_of_inner_eq_norm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v z k : V} {x y B C D qb qc : ℝ}
    (hkcoord : k = x • u + y • v)
    (hEq : 2 * inner ℝ z k = ‖k‖ ^ 2)
    (hB : B = inner ℝ u u) (hC : C = inner ℝ v v)
    (hD : D = inner ℝ u v)
    (hqb : qb = inner ℝ z u) (hqc : qc = inner ℝ z v) :
    2 * (x * qb + y * qc) = x ^ 2 * B + 2 * x * y * D + y ^ 2 * C := by
  have norm_sq_eq_inner (w : V) : ‖w‖ ^ 2 = inner ℝ w w := by
    symm
    exact real_inner_self_eq_norm_sq w
  rw [hkcoord, norm_sq_eq_inner] at hEq
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right] at hEq
  have hsym : inner ℝ (v) (u) = inner ℝ (u) (v) := by
    rw [real_inner_comm]
  rw [hsym, ← hB, ← hC, ← hD, ← hqb, ← hqc] at hEq
  nlinarith [hEq]

theorem scalar_cross_branch
    {a d p n G U V W Z : ℝ}
    (ha : 0 < a) (hd : 0 < d) (hG : G ≠ 0)
    (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hZ : 0 < Z)
    (hfac : (d * n - a * p) * G * (d * n + a * p) = 0)
    (hcos : p * U * V = W * Z * n) : d * n - a * p = 0 := by
  by_cases h : d * n - a * p = 0
  · exact h
  · have hother : d * n + a * p = 0 := by
      rcases mul_eq_zero.mp hfac with hAG | hother
      · have hG' : G = 0 :=
          (mul_eq_zero.mp hAG).resolve_left h
        exact (hG hG').elim
      · exact hother
    have hpos : 0 < d * (U * V) + (W * Z) * a := by positivity
    have hdiff : p * (U * V) - W * Z * n = 0 := by
      rw [sub_eq_zero]
      simpa [mul_assoc] using hcos
    have hp_mul : p * (d * (U * V) + (W * Z) * a) = 0 := by
      calc
        _ = d * (p * (U * V) - W * Z * n) +
            (W * Z) * (d * n + a * p) := by ring
        _ = 0 := by rw [hdiff, hother]; ring
    have hp : p = 0 :=
      (mul_eq_zero.mp hp_mul).resolve_right (ne_of_gt hpos)
    have hn_mul : d * n = 0 := by
      calc
        d * n = (d * n + a * p) - a * p := by ring
        _ = 0 := by rw [hother, hp]; ring
    have hn : n = 0 :=
      (mul_eq_zero.mp hn_mul).resolve_left (ne_of_gt hd)
    exact False.elim (h (by rw [hp, hn]; ring))

theorem scalar_factor_one
    {x y s t B C D : ℝ}
    (heq :
      ((1 - x) * B - y * D) ^ 2 * C *
          (s ^ 2 * B + 2 * s * (t - 1) * D + (t - 1) ^ 2 * C) =
        ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) * B *
          ((1 - t) * C - s * D) ^ 2) :
    (y * (1 - t) * C - s * (1 - x) * B) *
        (B * C - D ^ 2) *
        (s * (x - 1) * B + y * (t - 1) * C + 2 * s * y * D) = 0 := by
  calc
    _ = ((1 - x) * B - y * D) ^ 2 * C *
          (s ^ 2 * B + 2 * s * (t - 1) * D + (t - 1) ^ 2 * C) -
        ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) * B *
          ((1 - t) * C - s * D) ^ 2 := by ring
    _ = 0 := by rw [heq]; ring

theorem scalar_factor_two
    {x y s t B C D : ℝ}
    (heq :
      ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) ^ 2 *
          (s ^ 2 * B + 2 * s * (t - 1 / 2) * D +
            (t - 1 / 2) ^ 2 * C) * C =
        ((s - 1) ^ 2 * B + 2 * (s - 1) * t * D + t ^ 2 * C) *
          ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) *
          (s * D + (t - 1 / 2) * C) ^ 2) :
    let p := (s - 1) * (x - 1) * B +
      ((s - 1) * y + t * (x - 1)) * D + t * y * C
    let n := s * D + (t - 1 / 2) * C
    let d := t * (1 - x) - y * (1 - s)
    (d * n - s * p) * (B * C - D ^ 2) * (d * n + s * p) = 0 := by
  dsimp
  calc
    _ = -(
        ((s - 1) * (x - 1) * B +
            ((s - 1) * y + t * (x - 1)) * D + t * y * C) ^ 2 *
            (s ^ 2 * B + 2 * s * (t - 1 / 2) * D +
              (t - 1 / 2) ^ 2 * C) * C -
          ((s - 1) ^ 2 * B + 2 * (s - 1) * t * D + t ^ 2 * C) *
            ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) *
            (s * D + (t - 1 / 2) * C) ^ 2) := by ring
    _ = 0 := by rw [heq]; ring

theorem scalar_factor_three
    {x y s t B C D : ℝ}
    (heq :
      (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) ^ 2 * B *
          ((x - 1 / 2) ^ 2 * B + 2 * (x - 1 / 2) * y * D +
            y ^ 2 * C) =
        (s ^ 2 * B + 2 * s * (t - 1) * D +
            (t - 1) ^ 2 * C) *
          (x ^ 2 * B + 2 * x * (y - 1) * D +
            (y - 1) ^ 2 * C) *
          ((x - 1 / 2) * B + y * D) ^ 2) :
    let p := s * x * B + (s * (y - 1) + (t - 1) * x) * D +
      (t - 1) * (y - 1) * C
    let n := (x - 1 / 2) * B + y * D
    let d := x * (1 - t) - s * (1 - y)
    (d * n - y * p) * (B * C - D ^ 2) * (d * n + y * p) = 0 := by
  dsimp
  calc
    _ = -(
        (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
            (t - 1) * (y - 1) * C) ^ 2 * B *
            ((x - 1 / 2) ^ 2 * B + 2 * (x - 1 / 2) * y * D +
              y ^ 2 * C) -
          (s ^ 2 * B + 2 * s * (t - 1) * D +
              (t - 1) ^ 2 * C) *
            (x ^ 2 * B + 2 * x * (y - 1) * D +
              (y - 1) ^ 2 * C) *
            ((x - 1 / 2) * B + y * D) ^ 2) := by ring
    _ = 0 := by rw [heq]; ring

theorem coordinate_cycle_positivity
    {x y s t : ℝ} {w w₁ w₂ w₃ : Fin 3 → ℝ}
    (hw : ∀ i, 0 < w i) (hw₁ : ∀ i, 0 < w₁ i)
    (hw₂ : ∀ i, 0 < w₂ i) (hw₃ : ∀ i, 0 < w₃ i)
    (hw_sum : ∑ i, w i = 1) (hw₁_sum : ∑ i, w₁ i = 1)
    (hw₂_sum : ∑ i, w₂ i = 1) (hw₃_sum : ∑ i, w₃ i = 1)
    (hxdef : x = w 0 + w 1 / 2)
    (htdef : t = w₁ 1 / 2 + w₁ 2)
    (hxcoord : x = w₂ 1 + w₂ 2 * s)
    (hycoord : y = w₂ 2 * t)
    (hscoord : s = w₃ 1 * x)
    (htcoord : t = w₃ 1 * y + w₃ 2) :
    0 < x ∧ 0 < t ∧ 0 < y ∧ 0 < s ∧ 0 < 1 - x ∧ 0 < 1 - t ∧
      0 < t * (1 - x) - y * (1 - s) ∧
      0 < x * (1 - t) - s * (1 - y) ∧
      0 < x * t - y * s ∧ x ≠ 1 ∧ t ≠ 1 := by
  have hw_sum' : w 0 + w 1 + w 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hw_sum
  have hw₁_sum' : w₁ 0 + w₁ 1 + w₁ 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hw₁_sum
  have hw₂_sum' : w₂ 0 + w₂ 1 + w₂ 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hw₂_sum
  have hw₃_sum' : w₃ 0 + w₃ 1 + w₃ 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hw₃_sum
  have hxpos : 0 < x := by
    rw [hxdef]
    exact add_pos (hw 0) (div_pos (hw 1) (by norm_num))
  have htpos : 0 < t := by
    rw [htdef]
    exact add_pos (div_pos (hw₁ 1) (by norm_num)) (hw₁ 2)
  have hypos : 0 < y := by
    rw [hycoord]
    exact mul_pos (hw₂ 2) htpos
  have hspos : 0 < s := by
    rw [hscoord]
    exact mul_pos (hw₃ 1) hxpos
  have h1xpos : 0 < 1 - x := by
    calc
      0 < w 1 / 2 + w 2 := add_pos (div_pos (hw 1) (by norm_num)) (hw 2)
      _ = 1 - (w 0 + w 1 / 2) := by linarith only [hw_sum']
      _ = 1 - x := by rw [← hxdef]
  have h1tpos : 0 < 1 - t := by
    calc
      0 < w₁ 0 + w₁ 1 / 2 :=
        add_pos (hw₁ 0) (div_pos (hw₁ 1) (by norm_num))
      _ = 1 - (w₁ 1 / 2 + w₁ 2) := by linarith only [hw₁_sum']
      _ = 1 - t := by rw [← htdef]
  have hd2pos : 0 < t * (1 - x) - y * (1 - s) := by
    rw [hycoord, hxcoord]
    calc
      t * (1 - (w₂ 1 + w₂ 2 * s)) - w₂ 2 * t * (1 - s) =
          t * (1 - w₂ 1 - w₂ 2) := by ring
      _ = t * w₂ 0 := by rw [← hw₂_sum']; ring
      _ > 0 := mul_pos htpos (hw₂ 0)
  have hd3pos : 0 < x * (1 - t) - s * (1 - y) := by
    rw [htcoord, hscoord]
    calc
      x * (1 - (w₃ 1 * y + w₃ 2)) - w₃ 1 * x * (1 - y) =
          x * (1 - w₃ 1 - w₃ 2) := by ring
      _ = x * w₃ 0 := by rw [← hw₃_sum']; ring
      _ > 0 := mul_pos hxpos (hw₃ 0)
  have hdetpos : 0 < x * t - y * s := by
    rw [hycoord, hscoord]
    calc
      0 < x * t * (1 - w₂ 2 * w₃ 1) := by
        have hab : w₂ 2 * w₃ 1 < 1 := by
          have ha : w₂ 2 < 1 := by linarith [hw₂ 0, hw₂ 1, hw₂_sum']
          have hb : w₃ 1 < 1 := by linarith [hw₃ 0, hw₃ 2, hw₃_sum']
          have h₁ : w₂ 2 * w₃ 1 < 1 * w₃ 1 :=
            mul_lt_mul_of_pos_right ha (hw₃ 1)
          have h₂ : 1 * w₃ 1 < 1 := by simpa using hb
          exact lt_trans h₁ h₂
        exact mul_pos (mul_pos hxpos htpos) (sub_pos.mpr hab)
      _ = x * t - (w₂ 2 * t) * (w₃ 1 * x) := by ring
  exact ⟨hxpos, htpos, hypos, hspos, h1xpos, h1tpos, hd2pos, hd3pos,
    hdetpos, (by linarith), (by linarith)⟩

theorem scalar_equation_one
    {x y s t B C D U V W Z : ℝ}
    (hy : 0 < y) (hs : 0 < s) (hG : B * C - D ^ 2 ≠ 0)
    (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hZ : 0 < Z)
    (hcos : ((1 - x) * B - y * D) * U * V =
      W * Z * ((1 - t) * C - s * D))
    (heq :
      ((1 - x) * B - y * D) ^ 2 * C *
          (s ^ 2 * B + 2 * s * (t - 1) * D + (t - 1) ^ 2 * C) =
        ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) * B *
          ((1 - t) * C - s * D) ^ 2) :
    y * (1 - t) * C - s * (1 - x) * B = 0 := by
  let u : ℝ := (1 - x) * B - y * D
  let v : ℝ := (1 - t) * C - s * D
  have hfac0 := scalar_factor_one heq
  have hfac : (y * v - s * u) * (B * C - D ^ 2) *
      (y * v + s * u) = 0 := by
    calc
      _ = -((y * (1 - t) * C - s * (1 - x) * B) *
          (B * C - D ^ 2) *
          (s * (x - 1) * B + y * (t - 1) * C + 2 * s * y * D)) := by
            dsimp [u, v]
            ring
      _ = 0 := by rw [hfac0]; ring
  have hcos' : u * U * V = W * Z * v := by
    simpa [u, v] using hcos
  have hcross : y * v - s * u = 0 :=
    scalar_cross_branch hs hy hG hU hV hW hZ hfac hcos'
  calc
    y * (1 - t) * C - s * (1 - x) * B = y * v - s * u := by
      dsimp [u, v]
      ring
    _ = 0 := hcross

theorem scalar_equation_two
    {x y s t B C D U V W Z : ℝ}
    (hd : 0 < t * (1 - x) - y * (1 - s)) (hs : 0 < s)
    (hG : B * C - D ^ 2 ≠ 0)
    (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hZ : 0 < Z)
    (hcos :
      ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) * U * V =
        W * Z * (s * D + (t - 1 / 2) * C))
    (heq :
      ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) ^ 2 *
          (s ^ 2 * B + 2 * s * (t - 1 / 2) * D +
            (t - 1 / 2) ^ 2 * C) * C =
        ((s - 1) ^ 2 * B + 2 * (s - 1) * t * D + t ^ 2 * C) *
          ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) *
          (s * D + (t - 1 / 2) * C) ^ 2) :
    (t * (1 - x) - y * (1 - s)) * (s * D + (t - 1 / 2) * C) -
        s * ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) = 0 := by
  let p : ℝ := (s - 1) * (x - 1) * B +
    ((s - 1) * y + t * (x - 1)) * D + t * y * C
  let n : ℝ := s * D + (t - 1 / 2) * C
  let d : ℝ := t * (1 - x) - y * (1 - s)
  have hfac : (d * n - s * p) * (B * C - D ^ 2) *
      (d * n + s * p) = 0 := by
    simpa [p, n, d] using scalar_factor_two heq
  have hcos' : p * U * V = W * Z * n := by
    simpa [p, n] using hcos
  have hcross : d * n - s * p = 0 :=
    scalar_cross_branch hs hd hG hU hV hW hZ hfac hcos'
  simpa [p, n, d] using hcross

theorem scalar_equation_three
    {x y s t B C D U V W Z : ℝ}
    (hd : 0 < x * (1 - t) - s * (1 - y)) (hy : 0 < y)
    (hG : B * C - D ^ 2 ≠ 0)
    (hU : 0 < U) (hV : 0 < V) (hW : 0 < W) (hZ : 0 < Z)
    (hcos :
      (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) * U * V =
        W * Z * ((x - 1 / 2) * B + y * D))
    (heq :
      (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) ^ 2 * B *
          ((x - 1 / 2) ^ 2 * B + 2 * (x - 1 / 2) * y * D +
            y ^ 2 * C) =
        (s ^ 2 * B + 2 * s * (t - 1) * D +
            (t - 1) ^ 2 * C) *
          (x ^ 2 * B + 2 * x * (y - 1) * D +
            (y - 1) ^ 2 * C) *
          ((x - 1 / 2) * B + y * D) ^ 2) :
    (x * (1 - t) - s * (1 - y)) * ((x - 1 / 2) * B + y * D) -
        y * (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) = 0 := by
  let p : ℝ := s * x * B + (s * (y - 1) + (t - 1) * x) * D +
    (t - 1) * (y - 1) * C
  let n : ℝ := (x - 1 / 2) * B + y * D
  let d : ℝ := x * (1 - t) - s * (1 - y)
  have hfac : (d * n - y * p) * (B * C - D ^ 2) *
      (d * n + y * p) = 0 := by
    simpa [p, n, d] using scalar_factor_three heq
  have hcos' : p * U * V = W * Z * n := by
    simpa [p, n] using hcos
  have hcross : d * n - y * p = 0 :=
    scalar_cross_branch hy hd hG hU hV hW hZ hfac hcos'
  simpa [p, n, d] using hcross

theorem coordinate_norm_identities
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {A B C K L : P} {x y s t Bq Cq Dq : ℝ}
    (hKsubBq : K -ᵥ B = (x - 1) • (B -ᵥ A) + y • (C -ᵥ A))
    (hKsubCq : K -ᵥ C = x • (B -ᵥ A) + (y - 1) • (C -ᵥ A))
    (hLsubBq : L -ᵥ B = (s - 1) • (B -ᵥ A) + t • (C -ᵥ A))
    (hLsubCq : L -ᵥ C = s • (B -ᵥ A) + (t - 1) • (C -ᵥ A))
    (hKsubMq : K -ᵥ midpoint ℝ A B =
      (x - 1 / 2) • (B -ᵥ A) + y • (C -ᵥ A))
    (hLsubNq : L -ᵥ midpoint ℝ A C =
      s • (B -ᵥ A) + (t - 1 / 2) • (C -ᵥ A))
    (hABv : A -ᵥ B = -(B -ᵥ A)) (hACv : A -ᵥ C = -(C -ᵥ A))
    (hBq : Bq = inner ℝ (B -ᵥ A) (B -ᵥ A))
    (hCq : Cq = inner ℝ (C -ᵥ A) (C -ᵥ A))
    (hDq : Dq = inner ℝ (B -ᵥ A) (C -ᵥ A)) :
    (‖K -ᵥ B‖ ^ 2 =
        (x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq) ∧
      (‖L -ᵥ C‖ ^ 2 =
        s ^ 2 * Bq + 2 * s * (t - 1) * Dq + (t - 1) ^ 2 * Cq) ∧
      (‖L -ᵥ B‖ ^ 2 =
        (s - 1) ^ 2 * Bq + 2 * (s - 1) * t * Dq + t ^ 2 * Cq) ∧
      (‖K -ᵥ C‖ ^ 2 =
        x ^ 2 * Bq + 2 * x * (y - 1) * Dq + (y - 1) ^ 2 * Cq) ∧
      (‖K -ᵥ midpoint ℝ A B‖ ^ 2 =
        (x - 1 / 2) ^ 2 * Bq + 2 * (x - 1 / 2) * y * Dq + y ^ 2 * Cq) ∧
      (‖L -ᵥ midpoint ℝ A C‖ ^ 2 =
        s ^ 2 * Bq + 2 * s * (t - 1 / 2) * Dq +
          (t - 1 / 2) ^ 2 * Cq) ∧
      (‖A -ᵥ B‖ ^ 2 = Bq) ∧
      (‖A -ᵥ C‖ ^ 2 = Cq) ∧
      (inner ℝ (K -ᵥ B) (A -ᵥ B) = (1 - x) * Bq - y * Dq) ∧
      (inner ℝ (A -ᵥ C) (L -ᵥ C) = (1 - t) * Cq - s * Dq) := by
  have norm_sq_eq_inner (z : V) : ‖z‖ ^ 2 = inner ℝ z z := by
    symm
    exact real_inner_self_eq_norm_sq z
  have hnorm_KB : ‖K -ᵥ B‖ ^ 2 =
      (x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq := by
    rw [hKsubBq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LC : ‖L -ᵥ C‖ ^ 2 =
      s ^ 2 * Bq + 2 * s * (t - 1) * Dq + (t - 1) ^ 2 * Cq := by
    rw [hLsubCq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LB : ‖L -ᵥ B‖ ^ 2 =
      (s - 1) ^ 2 * Bq + 2 * (s - 1) * t * Dq + t ^ 2 * Cq := by
    rw [hLsubBq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_KC : ‖K -ᵥ C‖ ^ 2 =
      x ^ 2 * Bq + 2 * x * (y - 1) * Dq + (y - 1) ^ 2 * Cq := by
    rw [hKsubCq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_KM : ‖K -ᵥ midpoint ℝ A B‖ ^ 2 =
      (x - 1 / 2) ^ 2 * Bq + 2 * (x - 1 / 2) * y * Dq + y ^ 2 * Cq := by
    rw [hKsubMq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LN : ‖L -ᵥ midpoint ℝ A C‖ ^ 2 =
      s ^ 2 * Bq + 2 * s * (t - 1 / 2) * Dq +
        (t - 1 / 2) ^ 2 * Cq := by
    rw [hLsubNq, hBq, hCq, hDq, real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_AB : ‖A -ᵥ B‖ ^ 2 = Bq := by
    rw [hABv, norm_sq_eq_inner, hBq]
    simp only [inner_neg_left, inner_neg_right]
    ring
  have hnorm_AC : ‖A -ᵥ C‖ ^ 2 = Cq := by
    rw [hACv, norm_sq_eq_inner, hCq]
    simp only [inner_neg_left, inner_neg_right]
    ring
  have hi1 : inner ℝ (K -ᵥ B) (A -ᵥ B) =
      (1 - x) * Bq - y * Dq := by
    rw [hKsubBq, hABv, hBq, hDq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hi2 : inner ℝ (A -ᵥ C) (L -ᵥ C) =
      (1 - t) * Cq - s * Dq := by
    rw [hACv, hLsubCq, hCq, hDq]
    simp only [inner_add_right, real_inner_smul_right, inner_neg_left]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  exact ⟨hnorm_KB, hnorm_LC, hnorm_LB, hnorm_KC, hnorm_KM, hnorm_LN,
    hnorm_AB, hnorm_AC, hi1, hi2⟩

end IMO2026P2