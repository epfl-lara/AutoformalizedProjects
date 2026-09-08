import Mathlib

theorem LeanFlowProofs.PB022.sideParameters
    (a b c u v : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hv : 0 < v)
    (hc_sq : c ^ 2 = u ^ 2 + v ^ 2)
    (hb_sq : b ^ 2 = (a - u) ^ 2 + v ^ 2) :
    let s : ℝ := (a + b + c) / 2;
    let x : ℝ := s - a;
    let y : ℝ := s - b;
    let z : ℝ := s - c;
    let r : ℝ := a * v / (2 * s);
    0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < r ∧
    a = y + z ∧ b = x + z ∧ c = x + y ∧ s = x + y + z ∧
    s * r ^ 2 = x * y * z ∧
    u = y + x * (y - z) / a ∧
    v = 2 * s * r / a ∧
    (a * u + a * c) / (2 * s) = y := by 
  have hv2 : 0 < v ^ 2 := sq_pos_of_pos hv
  have hcu : u < c := by nlinarith [sq_nonneg (c + u)]
  have hcu' : -u < c := by nlinarith [sq_nonneg (c - u)]
  have hbu : a - u < b := by nlinarith [sq_nonneg (b + (a - u))]
  have hbu' : u - a < b := by nlinarith [sq_nonneg (b - (a - u))]
  have ht1 : a < b + c := by linarith
  have ht2 : b < a + c := by
    nlinarith [mul_pos ha (show 0 < c + u by linarith), sq_nonneg (a + c - b)]
  have ht3 : c < a + b := by
    nlinarith [mul_pos ha (show 0 < b + a - u by linarith), sq_nonneg (a + b - c)]
  have hp : 0 < a + b + c := by linarith
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hp0 : a + b + c ≠ 0 := ne_of_gt hp
  dsimp only
  refine ⟨by linarith, by linarith, by linarith, ?_, by ring, by ring, by ring, by ring, ?_, ?_, ?_, ?_⟩
  · exact div_pos (mul_pos ha hv) (by linarith)
  · field_simp
    nlinarith
  · field_simp
    nlinarith
  · field_simp
    <;> ring
  · field_simp
    nlinarith
