import Mathlib

theorem LeanFlowProofs.pb015_orthic_equations
    (m n ex ey fx fy : ℝ)
    (hm : 0 < m) (hn : 0 < n) (hp : 1 < m * n)
    (hEline : -2 * n * ex + (1 - n ^ 2) * ey + 2 * n ^ 2 = 0)
    (hEperp : (1 - n ^ 2) * (ex + m) + 2 * n * ey = 0)
    (hFline : 2 * m * fx + (1 - m ^ 2) * fy + 2 * m ^ 2 = 0)
    (hFperp : (1 - m ^ 2) * (fx - n) - 2 * m * fy = 0) :
    let p := m * n
    let δ := n - m
    let a := 2 * δ * (p + 1)
    let b := δ ^ 2 - (p + 1) ^ 2
    let c := 4 * p * (p - 1) - 2 * δ ^ 2
    a * ex + b * ey + c = 0 ∧
    a * fx + b * fy + c = 0 ∧
    0 < a ^ 2 + b ^ 2 ∧
    a ^ 2 + b ^ 2 = (δ ^ 2 + (p + 1) ^ 2) ^ 2 := by 
  dsimp only
  have hid : (2 * (n - m) * (m * n + 1)) ^ 2 +
      ((n - m) ^ 2 - (m * n + 1) ^ 2) ^ 2 =
      ((n - m) ^ 2 + (m * n + 1) ^ 2) ^ 2 := by ring
  refine ⟨?_, ?_, ?_, hid⟩
  · linear_combination (m ^ 2 - 1) * hEline - 2 * m * hEperp
  · linear_combination (n ^ 2 - 1) * hFline + 2 * n * hFperp
  · rw [hid]
    have hs : 0 < (m * n + 1) ^ 2 := sq_pos_of_pos (by linarith)
    exact sq_pos_of_pos (add_pos_of_nonneg_of_pos (sq_nonneg (n - m)) hs)

