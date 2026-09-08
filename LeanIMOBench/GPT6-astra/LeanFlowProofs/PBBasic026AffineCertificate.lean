import Mathlib

theorem LeanFlowProofs.PBBasic026_affine_certificate
    (u v : EuclideanSpace ℝ (Fin 2)) (t k : ℝ) (hk : 1 < k) :
    let U := t ^ 2 + (k + 1) ^ 2
    let V := t ^ 2 + k ^ 2
    let H := t ^ 2 + k * (k + 1)
    let rho := U / (4 * (k - 1))
    let beta := 2 * V / (3 * H)
    let o := (t / 2) • u + (rho - (k + 1) / 2) • v
    let d := (2 * t * (k + 1) / U) • u +
      ((t ^ 2 - (k + 1) ^ 2) / U) • v
    let x := (-2 * k * t / V) • u +
      ((k ^ 2 - t ^ 2) / V) • v
    (-(1 / (3 * rho))) • o = (1 - beta) • d + beta • x := by 
  have hU : t ^ 2 + (k + 1) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t, sq_nonneg k]
  have hV : t ^ 2 + k ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg t, sq_nonneg (k - 1)]
  have hH : t ^ 2 + k * (k + 1) ≠ 0 := by
    nlinarith [sq_nonneg t, sq_nonneg k]
  have hk' : k - 1 ≠ 0 := by linarith
  dsimp only
  simp only [smul_add, smul_smul]
  rw [add_add_add_comm, ← add_smul, ← add_smul]
  congr 1 <;> congr 1 <;> field_simp <;> ring
