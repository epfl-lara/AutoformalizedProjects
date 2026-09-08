import Mathlib

theorem LeanFlowProofs.PB016.weighted_circle_equation
    (α β κ l u v k : ℝ)
    (hκ : κ ≠ 0) (hl : l ≠ 0) (hu : u ≠ 0)
    (e : (ℝ × ℝ) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hmetric : ∀ z t : ℝ × ℝ,
      dist (e z) (e t) ^ 2 =
        κ * (α * (z.1 - t.1) ^ 2 + β * (z.2 - t.2) ^ 2))
    (hbase : α * u ^ 2 + β * v ^ 2 - k * u - β * l * v = 0)
    (z : ℝ × ℝ)
    (hz : EuclideanGeometry.Cospherical
      {e z, e (0, 0), e (0, l), e (u, v)}) :
    α * z.1 ^ 2 + β * z.2 ^ 2 - k * z.1 - β * l * z.2 = 0 := by 
  rcases hz with ⟨c, R, hc⟩
  obtain ⟨t, rfl⟩ := e.surjective c
  have h0 := hc (e (0, 0)) (by simp)
  have heq (w : ℝ × ℝ) (hw : e w ∈ ({e z, e (0, 0), e (0, l), e (u, v)} : Set _)) :
      α * w.1 ^ 2 + β * w.2 ^ 2 - 2 * α * t.1 * w.1 - 2 * β * t.2 * w.2 = 0 := by
    have hd : dist (e w) (e t) ^ 2 = dist (e (0, 0)) (e t) ^ 2 := by
      rw [hc (e w) hw, h0]
    rw [hmetric, hmetric] at hd
    have hh := (mul_left_cancel₀ hκ hd)
    dsimp at hh
    nlinarith only [hh]
  have hy := heq (0, l) (by simp)
  have hv := heq (u, v) (by simp)
  have hz' := heq z (by simp)
  dsimp at hy hv
  have hy' : β * l - 2 * β * t.2 = 0 := by
    apply (mul_eq_zero.mp (show l * (β * l - 2 * β * t.2) = 0 by nlinarith only [hy])).resolve_left hl
  have hx' : k - 2 * α * t.1 = 0 := by
    apply (mul_eq_zero.mp (show u * (k - 2 * α * t.1) = 0 by
      nlinarith only [hv, hbase, congrArg (fun a : ℝ => a * v) hy'])).resolve_left hu
  nlinarith only [hz', congrArg (fun a : ℝ => a * z.1) hx',
    congrArg (fun a : ℝ => a * z.2) hy']
