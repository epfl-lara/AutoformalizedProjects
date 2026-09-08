import Mathlib

theorem LeanFlowProofs.PB009.firstCircleCertificates
    (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hacute : b * c < a ^ 2) (hbc : b ≠ c) :
    let d : ℝ := c - b
    let m : ℝ := b + c
    let e : ℝ := a ^ 2 - b * c
    let T : ℝ := a ^ 2 + b * c
    let U : ℝ := 4 * a ^ 2 + d ^ 2
    let ix : ℝ := d * (2 * a ^ 2 - b * d) / U
    let iy : ℝ := a * d * m / U
    let jx : ℝ := d * (2 * a ^ 2 + c * d) / U
    let jy : ℝ := -(a * d * m) / U
    let ex : ℝ := c * e / (a ^ 2 + c ^ 2)
    let ey : ℝ := a * c * m / (a ^ 2 + c ^ 2)
    let fx : ℝ := -b * e / (a ^ 2 + b ^ 2)
    let fy : ℝ := a * b * m / (a ^ 2 + b ^ 2)
    let f1 : ℝ := 3 * a ^ 2 + b ^ 2 - 2 * b * c
    let f2 : ℝ := 3 * a ^ 2 + c ^ 2 - 2 * b * c
    let n1 : ℝ := a ^ 2 * (c - 2 * b) - b * (c ^ 2 - b * c + b ^ 2)
    let n2 : ℝ := a ^ 2 * (2 * c - b) + c * (b ^ 2 - b * c + c ^ 2)
    let z1 : ℝ := a ^ 2 * T - b ^ 2 * c * d
    let z2 : ℝ := a ^ 2 * T + b * c ^ 2 * d
    let F1 : ℝ → ℝ → ℝ := fun x y =>
      a * f1 * (x ^ 2 + y ^ 2) - a * n1 * x - z1 * y
    let F2 : ℝ → ℝ → ℝ := fun x y =>
      a * f2 * (x ^ 2 + y ^ 2) - a * n2 * x - z2 * y
    0 < f1 ∧ 0 < f2 ∧
      F1 ix iy = 0 ∧ F1 fx fy = 0 ∧
      F2 jx jy = 0 ∧ F2 ex ey = 0 ∧
      ix * fy - iy * fx ≠ 0 ∧ jx * ey - jy * ex ≠ 0 := by 
  dsimp only
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hU : 4 * a ^ 2 + (c - b) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hB : a ^ 2 + b ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hC : a ^ 2 + c ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hf1 : 0 < 3 * a ^ 2 + b ^ 2 - 2 * b * c := by
    nlinarith [sq_nonneg b, mul_pos hb hc]
  have hf2 : 0 < 3 * a ^ 2 + c ^ 2 - 2 * b * c := by
    nlinarith [sq_nonneg c, mul_pos hb hc]
  refine ⟨hf1, hf2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp [hU]
    <;> ring
  · field_simp [hB]
    <;> ring
  · field_simp [hU]
    <;> ring
  · field_simp [hC]
    <;> ring
  · have hid : (c - b) * (2 * a ^ 2 - b * (c - b)) / (4 * a ^ 2 + (c - b) ^ 2) *
          (a * b * (b + c) / (a ^ 2 + b ^ 2)) -
        a * (c - b) * (b + c) / (4 * a ^ 2 + (c - b) ^ 2) *
          (-b * (a ^ 2 - b * c) / (a ^ 2 + b ^ 2)) =
        a * b * (b + c) * (c - b) * (3 * a ^ 2 + b ^ 2 - 2 * b * c) /
          ((4 * a ^ 2 + (c - b) ^ 2) * (a ^ 2 + b ^ 2)) := by
        field_simp [hU, hB]
        <;> ring
    rw [hid]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (ne_of_gt ha) (ne_of_gt hb)) (ne_of_gt (add_pos hb hc)))
      (sub_ne_zero.mpr hbc.symm)) (ne_of_gt hf1)) (mul_ne_zero hU hB)
  · have hid : (c - b) * (2 * a ^ 2 + c * (c - b)) / (4 * a ^ 2 + (c - b) ^ 2) *
          (a * c * (b + c) / (a ^ 2 + c ^ 2)) -
        (-(a * (c - b) * (b + c)) / (4 * a ^ 2 + (c - b) ^ 2)) *
          (c * (a ^ 2 - b * c) / (a ^ 2 + c ^ 2)) =
        a * c * (b + c) * (c - b) * (3 * a ^ 2 + c ^ 2 - 2 * b * c) /
          ((4 * a ^ 2 + (c - b) ^ 2) * (a ^ 2 + c ^ 2)) := by
        field_simp [hU, hC]
        <;> ring
    rw [hid]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (ne_of_gt ha) (ne_of_gt hc)) (ne_of_gt (add_pos hb hc)))
      (sub_ne_zero.mpr hbc.symm)) (ne_of_gt hf2)) (mul_ne_zero hU hC)

