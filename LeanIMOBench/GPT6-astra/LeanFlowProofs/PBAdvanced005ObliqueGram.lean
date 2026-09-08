import Mathlib

theorem LeanFlowProofs.PBAdvanced005.obliqueGramIdentity
    (u v : EuclideanSpace ℝ (Fin 2))
    (k p q t s : ℝ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = k) :
    let b := t • u - (p • u + q • v);
    let c := s • v - (p • u + q • v);
    let F : ℝ := t * s - t * q - s * p;
    let T : ℝ := p ^ 2 + q ^ 2 + 2 * k * p * q -
      t * (p + k * q) - s * (q + k * p) + k * t * s;
    inner ℝ b c = T ∧
      (‖b‖ * ‖c‖) ^ 2 = T ^ 2 + (1 - k ^ 2) * F ^ 2 := by 
  have huu : inner ℝ u u = 1 := by simp [real_inner_self_eq_norm_sq, hu]
  have hvv : inner ℝ v v = 1 := by simp [real_inner_self_eq_norm_sq, hv]
  have hvu : inner ℝ v u = k := by rw [real_inner_comm, huv]
  dsimp
  constructor
  · simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huu, hvv, huv, hvu]
    ring
  · rw [mul_pow, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huu, hvv, huv, hvu]
    ring
