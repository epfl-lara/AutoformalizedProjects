import Mathlib

theorem LeanFlowProofs.PBBasic028.unitRayTriangleIncenter
    (A E F e f : EuclideanSpace ℝ (Fin 2))
    (u v : ℝ)
    (hu : 0 < u) (hv : 0 < v)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hE : E - A = u • f) (hF : F - A = v • e)
    (tri : AffineIndependent ℝ ![A, E, F]) :
    Affine.Simplex.incenter
        (⟨![A, E, F], tri⟩ :
          Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) - A =
      (u * v / (dist E F + u + v)) • (e + f) := by classical
  let det (x y : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0 * y 1 - x 1 * y 0
  have gram (x y z : EuclideanSpace ℝ (Fin 2)) :
      det x y ^ 2 * ‖z‖ ^ 2 =
        ‖y‖ ^ 2 * (inner ℝ x z) ^ 2 + ‖x‖ ^ 2 * (inner ℝ y z) ^ 2 -
          2 * inner ℝ x y * inner ℝ x z * inner ℝ y z := by
    simp only [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two, star_trivial, det]
    ring
  let t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨![A, E, F], tri⟩
  have area (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) :
      (t.height i * dist (t.points j) (t.points k)) ^ 2 =
        det (t.points i - t.points j) (t.points i - t.points k) ^ 2 := by
    let x := t.points i - t.points j
    let y := t.points i - t.points k
    let z := t.points i - t.altitudeFoot i
    have hx : inner ℝ x z = t.height i ^ 2 :=
      t.inner_vsub_vsub_altitudeFoot_eq_height_sq hij
    have hy : inner ℝ y z = t.height i ^ 2 :=
      t.inner_vsub_vsub_altitudeFoot_eq_height_sq hik
    have hz : ‖z‖ ^ 2 = t.height i ^ 2 := by
      rfl
    have hd : dist (t.points j) (t.points k) ^ 2 =
        ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * inner ℝ x y := by
      have hxy : y - x = t.points j - t.points k := by dsimp [x, y]; abel
      rw [dist_eq_norm, ← hxy, norm_sub_sq_real, real_inner_comm y x]
      ring
    have hg := gram x y z
    rw [hx, hy, hz] at hg
    have hp := t.height_pos i
    nlinarith [sq_pos_of_pos hp]
  have h01 := area 0 1 2 (by decide) (by decide)
  have h10 := area 1 0 2 (by decide) (by decide)
  have h20 := area 2 0 1 (by decide) (by decide)
  have hd10 : det (E - A) (E - F) = -det (A - E) (A - F) := by
    dsimp [det]
    ring
  have hd20 : det (F - A) (F - E) = det (A - E) (A - F) := by
    dsimp [det]
    ring
  have hAE : dist A E = u := by
    rw [dist_comm, dist_eq_norm, hE, norm_smul, hf, Real.norm_eq_abs,
      abs_of_pos hu, mul_one]
  have hAF : dist A F = v := by
    rw [dist_comm, dist_eq_norm, hF, norm_smul, he, Real.norm_eq_abs,
      abs_of_pos hv, mul_one]
  change (t.height 0 * dist E F) ^ 2 = det (A - E) (A - F) ^ 2 at h01
  change (t.height 1 * dist A F) ^ 2 = det (E - A) (E - F) ^ 2 at h10
  change (t.height 2 * dist A E) ^ 2 = det (F - A) (F - E) ^ 2 at h20
  rw [hd10, neg_sq, hAF] at h10
  rw [hd20, hAE] at h20
  have hp0 := t.height_pos 0
  have hp1 := t.height_pos 1
  have hp2 := t.height_pos 2
  have hd : 0 < dist E F := by
    apply dist_pos.mpr
    exact tri.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have hr1 : t.height 1 * v = t.height 0 * dist E F := by
    nlinarith [mul_pos hp0 hd, mul_pos hp1 hv]
  have hr2 : t.height 2 * u = t.height 0 * dist E F := by
    nlinarith [mul_pos hp0 hd, mul_pos hp2 hu]
  have hi0 : (t.height 0)⁻¹ = dist E F / (t.height 0 * dist E F) := by
    field_simp
  have hi1 : (t.height 1)⁻¹ = v / (t.height 0 * dist E F) := by
    rw [← hr1]
    field_simp
  have hi2 : (t.height 2)⁻¹ = u / (t.height 0 * dist E F) := by
    rw [← hr2]
    field_simp
  have hs : ∑ i, t.excenterWeightsUnnorm ∅ i =
      (dist E F + u + v) / (t.height 0 * dist E F) := by
    change (∑ i : Fin 3, t.excenterWeightsUnnorm ∅ i) = _
    rw [Fin.sum_univ_three]
    simp only [Affine.Simplex.excenterWeightsUnnorm_empty_apply, hi0, hi1, hi2]
    ring
  have hw1 : t.excenterWeights ∅ 1 = v / (dist E F + u + v) := by
    change (∑ i, t.excenterWeightsUnnorm ∅ i)⁻¹ * t.excenterWeightsUnnorm ∅ 1 = _
    rw [hs, Affine.Simplex.excenterWeightsUnnorm_empty_apply, hi1]
    field_simp
  have hw2 : t.excenterWeights ∅ 2 = u / (dist E F + u + v) := by
    change (∑ i, t.excenterWeightsUnnorm ∅ i)⁻¹ * t.excenterWeightsUnnorm ∅ 2 = _
    rw [hs, Affine.Simplex.excenterWeightsUnnorm_empty_apply, hi2]
    field_simp
  change t.incenter - A = _
  rw [t.incenter_eq_affineCombination]
  change (Finset.univ.affineCombination ℝ t.points (t.excenterWeights ∅)) -ᵥ A = _
  rw [← Finset.sum_smul_vsub_const_eq_affineCombination_vsub Finset.univ
    (t.excenterWeights ∅) t.points A t.excenterExists_empty.sum_excenterWeights_eq_one]
  change (∑ i : Fin 3, t.excenterWeights ∅ i • (t.points i - A)) = _
  rw [Fin.sum_univ_three]
  change t.excenterWeights ∅ 0 • (A - A) +
    t.excenterWeights ∅ 1 • (E - A) + t.excenterWeights ∅ 2 • (F - A) = _
  rw [sub_self, smul_zero, zero_add, hw1, hw2, hE, hF, smul_smul, smul_smul]
  module
