import Mathlib

theorem LeanFlowProofs.PB016.crossed_lines
    (r q m : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hrq : r * q < 1)
    (hne : r ≠ q)
    (hm : m ≠ -(2 + r + q) / (q - r)) :
    let N : ℝ := r + q + 2 * r * q
    let l : ℝ := N / (q - r)
    let D : ℝ := 1 - r * q + r * q * m ^ 2
    let x : ℝ := q * l * (1 + r - r * m) / D
    let y : ℝ := -r * l * (1 + q + q * m) / D
    ∀ p t : ℝ,
      (x - q) * (t + 1 + q) -
          (l + m * x + 1 + q) * (p - q) = 0 →
      (y - r) * (t - 1 - r) -
          (l + m * y - 1 - r) * (p - r) = 0 →
      p = N / D ∧ t = m * N / D ∧
      x - y = l * p ∧
      (l + m * x) - (l + m * y) = l * t ∧
      p ≠ 0 ∧ x ≠ y := by 
  dsimp only
  let N := r + q + 2 * r * q
  let l := N / (q - r)
  let D := 1 - r * q + r * q * m ^ 2
  let x := q * l * (1 + r - r * m) / D
  let y := -r * l * (1 + q + q * m) / D
  change ∀ p t : ℝ, (x - q) * (t + 1 + q) -
    (l + m * x + 1 + q) * (p - q) = 0 →
    (y - r) * (t - 1 - r) - (l + m * y - 1 - r) * (p - r) = 0 → _
  have hqr : q - r ≠ 0 := sub_ne_zero.mpr hne.symm
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 < D := by
    dsimp [D]
    have := mul_nonneg (le_of_lt (mul_pos hr hq)) (sq_nonneg m)
    linarith
  have hD0 : D ≠ 0 := ne_of_gt hD
  have hl : l ≠ 0 := div_ne_zero (ne_of_gt hN) hqr
  have hmn : m + (2 + r + q) / (q - r) ≠ 0 := by
    intro h
    apply hm
    rw [neg_div]
    linarith
  let a := x - q
  let b := l + m * x + 1 + q
  let c := y - r
  let d := l + m * y - 1 - r
  have hdet : a * d - b * c =
      r * q * N * (m + (2 + r + q) / (q - r)) ^ 2 / D := by
    dsimp [a, b, c, d, x, y, l, N, D]
    field_simp
    <;> ring
  have hdet0 : a * d - b * c ≠ 0 := by
    rw [hdet]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (ne_of_gt hr)
      (ne_of_gt hq)) (ne_of_gt hN)) (pow_ne_zero 2 hmn)) hD0
  have he1 : a * (m * N / D + 1 + q) - b * (N / D - q) = 0 := by
    have hD1 : 1 - q * r + q * r * m ^ 2 ≠ 0 := by simpa [mul_comm q r] using hD0
    dsimp [a, b, x, l, N, D]
    field_simp [show 1 - r * q + r * q * m ^ 2 ≠ 0 from hD0, hD1, hqr]
    <;> ring
  have he2 : c * (m * N / D - 1 - r) - d * (N / D - r) = 0 := by
    dsimp [c, d, y, l, N, D]
    field_simp [show 1 - r * q + r * q * m ^ 2 ≠ 0 from hD0, hqr]
    <;> ring
  intro p t hp ht
  change a * (t + 1 + q) - b * (p - q) = 0 at hp
  change c * (t - 1 - r) - d * (p - r) = 0 at ht
  have e1 : a * (t - m * N / D) - b * (p - N / D) = 0 := by
    nlinarith only [hp, he1]
  have e2 : c * (t - m * N / D) - d * (p - N / D) = 0 := by
    nlinarith only [ht, he2]
  have ep : (a * d - b * c) * (p - N / D) = 0 := by
    linear_combination c * e1 - a * e2
  have et : (a * d - b * c) * (t - m * N / D) = 0 := by
    linear_combination d * e1 - b * e2
  have hp' : p = N / D := sub_eq_zero.mp ((mul_eq_zero.mp ep).resolve_left hdet0)
  have ht' : t = m * N / D := sub_eq_zero.mp ((mul_eq_zero.mp et).resolve_left hdet0)
  have hxy : x - y = l * (N / D) := by
    dsimp [x, y, l, N, D]
    ring
  refine ⟨hp', ht', ?_, ?_, ?_, ?_⟩
  · change x - y = l * p
    rw [hp', hxy]
  · change (l + m * x) - (l + m * y) = l * t
    rw [ht']
    calc
      _ = m * (x - y) := by ring
      _ = _ := by rw [hxy]; ring
  · rw [hp']
    exact div_ne_zero (ne_of_gt hN) hD0
  · change x ≠ y
    apply sub_ne_zero.mp
    rw [hxy]
    exact mul_ne_zero hl (div_ne_zero (ne_of_gt hN) hD0)
