import Mathlib

theorem LeanFlowProofs.pb015_secant_coordinates
    (p δ t u qx qy : ℝ)
    (hp : 4 < p)
    (hδ : δ ^ 2 = p ^ 2 - 4 * p - 1)
    (ht : 0 ≤ t)
    (hqx : qx = -t * δ / (p - 1))
    (hqy : qy = 1 - t)
    (hQ : qx ^ 2 + qy ^ 2 - δ * qx - qy - p = 0)
    (hu : u ≠ 1)
    (hX : (u * qx) ^ 2 + (u * qy) ^ 2 -
      δ * (u * qx) - u * qy - p = 0) :
    t = (p - 1) / (p - 3) ∧
    qx = -δ / (p - 3) ∧ qy = -2 / (p - 3) ∧
    u * qx = p * δ / (p - 1) ∧
    u * qy = 2 * p / (p - 1) := by 
  have h1 : p - 1 ≠ 0 := by linarith
  have h3 : p - 3 ≠ 0 := by linarith
  have hQ' := hQ
  rw [hqx, hqy] at hQ'
  field_simp at hQ'
  have hf : ((p - 3) * t - (p - 1)) * (2 * t + p - 1) = 0 := by
    rw [hδ] at hQ'
    have he : p * (((p - 3) * t - (p - 1)) * (2 * t + p - 1)) = 0 := by
      nlinarith only [hQ']
    exact (mul_eq_zero.mp he).resolve_left (by linarith)
  have ht' : t = (p - 1) / (p - 3) := by
    have hz := (mul_eq_zero.mp hf).resolve_right (by nlinarith : 2 * t + p - 1 ≠ 0)
    apply (eq_div_iff h3).mpr
    nlinarith
  have hx : qx = -δ / (p - 3) := by rw [hqx, ht']; field_simp
  have hy : qy = -2 / (p - 3) := by rw [hqy, ht']; field_simp; ring
  have hn : (qx ^ 2 + qy ^ 2) * (p - 3) = p - 1 := by
    rw [hx, hy]
    field_simp
    nlinarith [hδ]
  have hfU : (u - 1) * (u * (qx ^ 2 + qy ^ 2) + p) = 0 := by
    nlinarith only [hX, congrArg (fun z : ℝ => u * z) hQ]
  have hu' : u * (qx ^ 2 + qy ^ 2) + p = 0 :=
    (mul_eq_zero.mp hfU).resolve_left (sub_ne_zero.mpr hu)
  have huv : u * (p - 1) = -p * (p - 3) := by
    nlinarith only [congrArg (fun z : ℝ => (p - 3) * z) hu', congrArg (fun z : ℝ => u * z) hn]
  refine ⟨ht', hx, hy, ?_, ?_⟩
  · rw [hx]
    field_simp
    nlinarith only [congrArg (fun z : ℝ => δ * z) huv]
  · rw [hy]
    field_simp
    nlinarith [huv]
