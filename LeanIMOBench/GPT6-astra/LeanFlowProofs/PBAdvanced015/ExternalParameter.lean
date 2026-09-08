import Mathlib

theorem LeanFlowProofs.pb015_external_parameter
    (p t : ℝ) (hp : 4 < p) (ht : t ≠ 0)
    (hext : t ^ 2 * (2 * p / (p - 1) - 1) -
      t * (p + 2 * p / (p - 1)) = p * |t|) :
    t = 2 * p ^ 2 / (p + 1) ∧ 0 < t := by 
  have hd : p - 1 ≠ 0 := by linarith
  have hd' : p + 1 ≠ 0 := by linarith
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [abs_of_neg hneg] at hext
    field_simp [hd] at hext
    have hf : t * (t * (p + 1) - 2 * p) = 0 := by nlinarith [hext]
    have hc := (mul_eq_zero.mp hf).resolve_left ht
    have hs : t * (p + 1) < 0 := mul_neg_of_neg_of_pos hneg (by linarith)
    exfalso
    nlinarith
  · rw [abs_of_pos hpos] at hext
    field_simp [hd] at hext
    have hf : t * (t * (p + 1) - 2 * p ^ 2) = 0 := by nlinarith [hext]
    have hc := (mul_eq_zero.mp hf).resolve_left ht
    constructor
    · apply (eq_div_iff hd').2
      nlinarith
    · exact hpos
