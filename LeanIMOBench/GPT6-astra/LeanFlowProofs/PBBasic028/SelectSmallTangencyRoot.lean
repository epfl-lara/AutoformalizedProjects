import Mathlib

theorem LeanFlowProofs.PBBasic028.selectSmallTangencyRoot
    (a b c q k : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hql : -1 < q) (hqu : q < 1)
    (hlaw : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * q)
    (hk : 0 ≤ k)
    (hinside : k * (b + c) ≤ b * c)
    (hquad : 2 * k ^ 2 * (1 + q) ^ 2 -
      k * ((b + c) * (1 + 2 * q) + a) + b * c * q = 0) :
    (a + b + c) * k * (1 + q) = b * c * q ∧ 0 ≤ q := by 
  have hbc : 0 < b * c := mul_pos hb hc
  have hq : 0 < 1 + q := by linarith
  have hbound : 2 * k * (1 + q) * (b + c) < (b + c) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hinside hq.le
    have h₂ := mul_pos hbc (sub_pos.mpr hqu)
    nlinarith [sq_nonneg (b - c)]
  have hsmall : 2 * k * (1 + q) < a + b + c := by
    have hs : 0 < b + c := by linarith
    have : 2 * k * (1 + q) < b + c := by
      nlinarith
    linarith
  have hfactor : (2 * k * (1 + q) - (a + b + c)) *
      ((a + b + c) * k * (1 + q) - b * c * q) = 0 := by
    linear_combination (a + b + c) * hquad - k * q * hlaw
  have heq : (a + b + c) * k * (1 + q) = b * c * q := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith
  refine ⟨heq, ?_⟩
  have hnonneg : 0 ≤ (a + b + c) * k * (1 + q) := by positivity
  have : 0 ≤ b * c * q := by rw [← heq]; exact hnonneg
  exact nonneg_of_mul_nonneg_right this hbc
