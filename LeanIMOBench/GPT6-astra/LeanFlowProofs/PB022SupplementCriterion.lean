import Mathlib

theorem LeanFlowProofs.PB022.supplementCriterion
    (U V P Q : EuclideanSpace ℝ (Fin 2))
    (ℓ : ℝ) (hℓ : 0 < ℓ)
    (hPQ : P 0 * Q 1 - P 1 * Q 0 ≠ 0)
    (hdet : U 0 * V 1 - U 1 * V 0 = ℓ * (P 0 * Q 1 - P 1 * Q 0))
    (hdot : U 0 * V 0 + U 1 * V 1 = -ℓ * (P 0 * Q 0 + P 1 * Q 1)) :
    EuclideanGeometry.angle U (0 : EuclideanSpace ℝ (Fin 2)) V +
      EuclideanGeometry.angle P (0 : EuclideanSpace ℝ (Fin 2)) Q = Real.pi := by 
  have hi (X Y : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ X Y = X 0 * Y 0 + X 1 * Y 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]
  have hn (X : EuclideanSpace ℝ (Fin 2)) : ‖X‖ ^ 2 = X 0 ^ 2 + X 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hi]
    ring
  have gram (X Y : EuclideanSpace ℝ (Fin 2)) :
      (‖X‖ * ‖Y‖) ^ 2 = (X 0 * Y 0 + X 1 * Y 1) ^ 2 +
        (X 0 * Y 1 - X 1 * Y 0) ^ 2 := by
    rw [mul_pow, hn, hn]
    ring
  have hs : (‖U‖ * ‖V‖) ^ 2 = (ℓ * (‖P‖ * ‖Q‖)) ^ 2 := by
    rw [gram, hdot, hdet, mul_pow ℓ (‖P‖ * ‖Q‖), gram]
    ring
  have he : ‖U‖ * ‖V‖ = ℓ * (‖P‖ * ‖Q‖) := by
    nlinarith [mul_nonneg (norm_nonneg U) (norm_nonneg V),
      mul_nonneg (le_of_lt hℓ) (mul_nonneg (norm_nonneg P) (norm_nonneg Q))]
  have hd : inner ℝ U V / (‖U‖ * ‖V‖) =
      -(inner ℝ P Q / (‖P‖ * ‖Q‖)) := by
    rw [hi, hi, hdot, he]
    rw [neg_mul, neg_div, mul_div_mul_left _ _ (ne_of_gt hℓ)]
  simp only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero,
    InnerProductGeometry.angle]
  rw [hd, Real.arccos_neg]
  ring
