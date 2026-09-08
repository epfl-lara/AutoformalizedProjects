import Mathlib

theorem LeanFlowProofs.pb015_tangency_relation
    (p δ : ℝ) (hp : 1 < p)
    (ht : (4 * p * (p - 1) - (δ ^ 2 + (p + 1) ^ 2)) ^ 2 =
      (δ ^ 2 + (p + 1) ^ 2) ^ 2) :
    δ ^ 2 = p ^ 2 - 4 * p - 1 ∧ 4 < p := by 
  have hpos : 0 < 4 * p * (p - 1) := by positivity
  have hf : (4 * p * (p - 1)) *
      (4 * p * (p - 1) - 2 * (δ ^ 2 + (p + 1) ^ 2)) = 0 := by
    nlinarith only [ht]
  have hz := (mul_eq_zero.mp hf).resolve_left (ne_of_gt hpos)
  have hd : δ ^ 2 = p ^ 2 - 4 * p - 1 := by nlinarith only [hz]
  refine ⟨hd, ?_⟩
  by_contra hn
  have hle : p ≤ 4 := le_of_not_gt hn
  have hm : 0 ≤ p * (4 - p) := mul_nonneg (by linarith) (by linarith)
  nlinarith [sq_nonneg δ]
