import Mathlib

theorem LeanFlowProofs.PBBasic028.altitudeFootVectors
    (A B C e f : EuclideanSpace ℝ (Fin 2))
    (b c q : ℝ)
    (tri : AffineIndependent ℝ ![A, B, C])
    (hB : B - A = c • e) (hC : C - A = b • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hq : inner ℝ e f = q) :
    Affine.Simplex.altitudeFoot
        (⟨![A, B, C], tri⟩ :
          Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) 1 - A =
      (c * q) • f ∧
    Affine.Simplex.altitudeFoot
        (⟨![A, B, C], tri⟩ :
          Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) 2 - A =
      (b * q) • e := by 
  classical
  have proj (P D g : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
      (ht : t ≠ 0) (hD : D - A = t • g) (hg : ‖g‖ = 1) :
      (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, D}) P : EuclideanSpace ℝ (Fin 2)) - A =
        (inner ℝ g (P - A)) • g := by
    have hm : (inner ℝ g (P - A)) • g + A ∈ affineSpan ℝ {A, D} := by
      have hh := AffineMap.lineMap_mem_affineSpan_pair (inner ℝ g (P - A) / t) A D
      simpa [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hD, smul_smul, ht] using hh
    have hp : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, D}) P : EuclideanSpace ℝ (Fin 2)) =
        (inner ℝ g (P - A)) • g + A := by
      apply EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr
      refine ⟨hm, ?_⟩
      rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
      change inner ℝ (A - D) (P - ((inner ℝ g (P - A)) • g + A)) = 0
      rw [show A - D = -(t • g) by rw [← hD]; abel,
        show P - ((inner ℝ g (P - A)) • g + A) = (P - A) - (inner ℝ g (P - A)) • g by abel]
      simp [inner_neg_left, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hg]
      <;> ring
    rw [hp, add_sub_cancel_right]
  have hb : b ≠ 0 := by
    intro hz
    have hh : C = A := sub_eq_zero.mp (by simpa [hz] using hC)
    have hi := tri.injective
    have : (2 : Fin 3) = 0 := hi (by simpa using hh)
    omega
  have hc : c ≠ 0 := by
    intro hz
    have hh : B = A := sub_eq_zero.mp (by simpa [hz] using hB)
    have hi := tri.injective
    have : (1 : Fin 3) = 0 := hi (by simpa using hh)
    omega
  have hs1 : (![A, B, C] : Fin 3 → _) '' ({1}ᶜ : Set (Fin 3)) = {A, C} := by
    ext x
    simp [Set.mem_image, Fin.exists_fin_succ, eq_comm]
  have hs2 : (![A, B, C] : Fin 3 → _) '' ({2}ᶜ : Set (Fin 3)) = {A, B} := by
    ext x
    simp [Set.mem_image, Fin.exists_fin_succ, eq_comm]
  constructor
  · unfold Affine.Simplex.altitudeFoot Affine.Simplex.orthogonalProjectionSpan
    simp only [Affine.Simplex.range_faceOpposite_points]
    simp only [hs1]
    have hq' : inner ℝ f e = q := (real_inner_comm e f).trans hq
    simpa [hB, real_inner_smul_right, hq'] using proj B C f b hb hC hf
  · unfold Affine.Simplex.altitudeFoot Affine.Simplex.orthogonalProjectionSpan
    simp only [Affine.Simplex.range_faceOpposite_points]
    simp only [hs2]
    simpa [hC, real_inner_smul_right, hq] using proj C B e c hc hB he
