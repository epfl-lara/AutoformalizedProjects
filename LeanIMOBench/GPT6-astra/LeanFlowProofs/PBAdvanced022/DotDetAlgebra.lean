import Mathlib

theorem LeanFlowProofs.PB022.dotDetAlgebra
    (x y z r : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hr : 0 < r)
    (h_radius : (x + y + z) * r ^ 2 = x * y * z) :
    let a : ℝ := y + z;
    let s : ℝ := x + y + z;
    let u : ℝ := (x * (y - z) - a * y) / (2 * a);
    let v : ℝ := (x * (y - z) + a * z) / (2 * a);
    let h : ℝ := x * r / a;
    let p : ℝ := a * (y - z - x) / (2 * s);
    let q : ℝ := a * (y - z + x) / (2 * s);
    let k : ℝ := a * r / (2 * x);
    let ℓ : ℝ := x * s / a ^ 2;
    0 < ℓ ∧
    p * k - k * q ≠ 0 ∧
    u * h - h * v = ℓ * (p * k - k * q) ∧
    u * v + h ^ 2 = -ℓ * (p * q + k ^ 2) := by 
  dsimp only
  have ha : 0 < y + z := by positivity
  have hs : 0 < x + y + z := by positivity
  have hx0 := ne_of_gt hx
  have ha0 := ne_of_gt ha
  have hs0 := ne_of_gt hs
  have hd : (y + z) * (y - z - x) / (2 * (x + y + z)) *
      ((y + z) * r / (2 * x)) - (y + z) * r / (2 * x) *
      ((y + z) * (y - z + x) / (2 * (x + y + z))) =
      -((y + z)^2 * r / (2 * (x + y + z))) := by
    field_simp
    <;> ring
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [hd]
    exact neg_ne_zero.mpr (ne_of_gt (by positivity))
  · rw [hd]
    field_simp
    <;> ring
  · have hfactor :
        (x * (y - z) - (y + z) * y) / (2 * (y + z)) *
          ((x * (y - z) + (y + z) * z) / (2 * (y + z))) +
          (x * r / (y + z)) ^ 2 +
          (x * (x + y + z) / (y + z)^2) *
          ((y + z) * (y - z - x) / (2 * (x + y + z)) *
           ((y + z) * (y - z + x) / (2 * (x + y + z))) +
           ((y + z) * r / (2 * x))^2) =
        (4*x^3 + (y+z)^2*(x+y+z)) * ((x+y+z)*r^2-x*y*z) /
          (4*(y+z)^2*(x+y+z)*x) := by
      field_simp
      <;> ring
    rw [h_radius, sub_self, mul_zero, zero_div] at hfactor
    linarith
