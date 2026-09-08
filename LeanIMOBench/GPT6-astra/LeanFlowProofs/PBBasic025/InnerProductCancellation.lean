import Mathlib

theorem LeanFlowProofs.pbbasic025_innerProductCancellation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b c : ℝ) (u v q : V)
    (hb : b ≠ 0) (hc : c ≠ 0) (hS : a + b + c ≠ 0)
    (hu : inner ℝ u u = c ^ 2)
    (hv : inner ℝ v v = b ^ 2)
    (huv : 2 * inner ℝ u v = b ^ 2 + c ^ 2 - a ^ 2)
    (hqu : 2 * inner ℝ q u = c ^ 2)
    (hqv : 2 * inner ℝ q v = b ^ 2) :
    inner ℝ
      (q - ((b / (a + b + c)) • u + (c / (a + b + c)) • v))
      ((1 - a / b) • v - (1 - a / c) • u) = 0 := by 
  have huv' : inner ℝ u v = (b ^ 2 + c ^ 2 - a ^ 2) / 2 := by linarith
  have hqu' : inner ℝ q u = c ^ 2 / 2 := by linarith
  have hqv' : inner ℝ q v = b ^ 2 / 2 := by linarith
  simp only [inner_sub_left, inner_sub_right, inner_add_left,
    real_inner_smul_left, real_inner_smul_right]
  rw [← real_inner_comm v u, hu, hv, huv', hqu', hqv']
  field_simp [hb, hc, hS]
  <;> ring
