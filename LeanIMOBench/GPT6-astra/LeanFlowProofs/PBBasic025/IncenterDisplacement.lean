import LeanFlowProofs.PBBasic025.HeightProducts
import Mathlib

theorem LeanFlowProofs.pbbasic025_incenterDisplacement
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    let a := dist (s.points 1) (s.points 2)
    let b := dist (s.points 0) (s.points 2)
    let c := dist (s.points 0) (s.points 1)
    let S := a + b + c
    Affine.Simplex.incenter s - s.points 0 =
      (b / S) • (s.points 1 - s.points 0) +
      (c / S) • (s.points 2 - s.points 0) := by classical
  obtain ⟨D, hD, h0, h1, h2⟩ := LeanFlowProofs.pbbasic025_heightProducts s
  have invheight (x h : ℝ) (hh : 0 < h) (hx : x * h = D) : h⁻¹ = x / D := by
    apply (eq_div_iff (ne_of_gt hD)).2
    rw [← hx]
    field_simp
  have e0 := invheight _ _ (s.height_pos 0) h0
  have e1 := invheight _ _ (s.height_pos 1) h1
  have e2 := invheight _ _ (s.height_pos 2) h2
  dsimp only
  rw [s.incenter_eq_affineCombination]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ _ s.excenterExists_empty.sum_excenterWeights_eq_one (s.points 0)]
  simp only [vadd_eq_add, add_sub_cancel_right]
  simp [Finset.weightedVSubOfPoint_apply, Fin.sum_univ_succ,
    Affine.Simplex.excenterWeights, e0, e1, e2]
  simp only [← mul_smul]
  congr 2 <;> rw [← add_div, ← add_div, inv_div] <;>
    field_simp <;> ring
