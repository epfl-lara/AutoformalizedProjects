import Mathlib

theorem LeanFlowProofs.pb015_circumcircle_coordinates
    (m n ox oy R : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hp : 4 < m * n)
    (hδ : (n - m) ^ 2 = (m * n) ^ 2 - 4 * (m * n) - 1)
    (hR : 0 ≤ R)
    (hB : (-m - ox) ^ 2 + oy ^ 2 = R ^ 2)
    (hC : (n - ox) ^ 2 + oy ^ 2 = R ^ 2)
    (hA : (-(n - m) / (m * n - 1) - ox) ^ 2 +
      (2 * m * n / (m * n - 1) - oy) ^ 2 = R ^ 2) :
    ox = (n - m) / 2 ∧ oy = 1 / 2 ∧ R = m * n / 2 := by 
  have hx : ox = (n - m) / 2 := by
    have h : (m + n) * (2 * ox - (n - m)) = 0 := by nlinarith [hB, hC]
    have hz : 2 * ox - (n - m) = 0 := (mul_eq_zero.mp h).resolve_left (ne_of_gt (by linarith))
    linarith
  have hd : m * n - 1 ≠ 0 := by linarith
  have hcirc : (-(n - m) / (m * n - 1)) ^ 2 +
      (2 * m * n / (m * n - 1)) ^ 2 -
      (n - m) * (-(n - m) / (m * n - 1)) -
      2 * m * n / (m * n - 1) - m * n = 0 := by
    field_simp [hd, show n * m - 1 ≠ 0 by nlinarith]
    nlinarith [congrArg (fun z : ℝ => (m * n) * z) hδ]
  have hypos : 0 < 2 * m * n / (m * n - 1) := by
    exact div_pos (by positivity) (by linarith)
  have hy : oy = 1 / 2 := by
    rw [hx] at hA hB
    have hh : (2 * m * n / (m * n - 1)) * (2 * oy - 1) = 0 := by
      nlinarith [hA, hB, hcirc]
    have := (mul_eq_zero.mp hh).resolve_left (ne_of_gt hypos)
    linarith
  refine ⟨hx, hy, ?_⟩
  rw [hx, hy] at hB
  nlinarith [hδ]
