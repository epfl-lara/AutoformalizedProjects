import Mathlib

theorem LeanFlowProofs.PB003.cyclicCoefficientCollinearity
    (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    let s : ℝ := x + y + z;
    let p : ℝ := x * y * z;
    let q : ℝ := x * y + y * z + z * x;
    let N : ℝ → ℝ := fun t =>
      (s * q + 3 * p) * p - (s * q - 5 * p) * s * t ^ 2;
    let m : ℝ → ℝ := fun t => (s - t) / (s + t);
    let n : ℝ → ℝ → ℝ → ℝ := fun a b c =>
      (s - a) ^ 2 * N a / ((s + a) * a * (c - b));
    (m y - m x) * (n z x y - n x y z) =
      (m z - m x) * (n y z x - n x y z) := by 
  dsimp
  have hsx : x + y + z + x ≠ 0 := ne_of_gt (by linarith)
  have hsy : x + y + z + y ≠ 0 := ne_of_gt (by linarith)
  have hsz : x + y + z + z ≠ 0 := ne_of_gt (by linarith)
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hzy : z - y ≠ 0 := sub_ne_zero.mpr hyz.symm
  have hxz : x - z ≠ 0 := sub_ne_zero.mpr hzx.symm
  field_simp [hsx, hsy, hsz, hyx, hzy, hxz, ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
  <;> ring
