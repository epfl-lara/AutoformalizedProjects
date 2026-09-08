import Mathlib

theorem LeanFlowProofs.PB009.pencilCertificates
    (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hacute : b * c < a ^ 2) :
    let d : ℝ := c - b
    let e : ℝ := a ^ 2 - b * c
    let T : ℝ := a ^ 2 + b * c
    let U : ℝ := 4 * a ^ 2 + d ^ 2
    let lx : ℝ := d * e / U
    let ly : ℝ := a * (2 * T + d ^ 2) / U
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
    let F0 : ℝ → ℝ → ℝ := fun x y =>
      a * d * (x ^ 2 + y ^ 2) - a * (T + d ^ 2) * x - b * c * d * y
    (∀ x y : ℝ, F2 x y - F1 x y = (b + c) * F0 x y) ∧
      F0 lx ly = 0 ∧ 0 < F1 lx ly ∧ 0 < ly := by 
  dsimp only
  have hU : 0 < 4 * a ^ 2 + (c - b) ^ 2 := by positivity
  have hUne : 4 * a ^ 2 + (c - b) ^ 2 ≠ 0 := ne_of_gt hU
  have hT : 0 < a ^ 2 + b * c := by positivity
  have he : 0 < a ^ 2 - b * c := sub_pos.mpr hacute
  have hW : 0 < a ^ 2 * (c - b) ^ 2 + (a ^ 2 + b * c) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    ring
  · field_simp
    <;> ring
  · have hid :
        a * (3 * a ^ 2 + b ^ 2 - 2 * b * c) *
            (((c - b) * (a ^ 2 - b * c) / (4 * a ^ 2 + (c - b) ^ 2)) ^ 2 +
             (a * (2 * (a ^ 2 + b * c) + (c - b) ^ 2) / (4 * a ^ 2 + (c - b) ^ 2)) ^ 2) -
          a * (a ^ 2 * (c - 2 * b) - b * (c ^ 2 - b * c + b ^ 2)) *
            ((c - b) * (a ^ 2 - b * c) / (4 * a ^ 2 + (c - b) ^ 2)) -
          (a ^ 2 * (a ^ 2 + b * c) - b ^ 2 * c * (c - b)) *
            (a * (2 * (a ^ 2 + b * c) + (c - b) ^ 2) / (4 * a ^ 2 + (c - b) ^ 2)) =
        a * (a ^ 2 - b * c) * (a ^ 2 * (c - b) ^ 2 + (a ^ 2 + b * c) ^ 2) /
          (4 * a ^ 2 + (c - b) ^ 2) := by
      field_simp
      <;> ring
    rw [hid]
    exact div_pos (mul_pos (mul_pos ha he) hW) hU
  · exact div_pos (mul_pos ha (by positivity)) hU
