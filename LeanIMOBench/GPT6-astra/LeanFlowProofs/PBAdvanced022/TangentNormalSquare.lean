import Mathlib

theorem LeanFlowProofs.PB022.tangentNormalSquare
    (A C X : EuclideanSpace ℝ (Fin 2))
    (ω : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (t : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (F : AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
    (n₀ n₁ : ℝ)
    (hAC : A ≠ C)
    (hn : 0 < n₀ ^ 2 + n₁ ^ 2)
    (h_normal : n₀ * ((F C) 0 - (F A) 0) + n₁ * ((F C) 1 - (F A) 1) = 0)
    (h_parallel : t.Parallel (affineSpan ℝ {A, C}))
    (h_tangent : ω.IsTangent t)
    (hX : X ∈ t) :
    (n₀ * ((F X) 0 - (F ω.center) 0) +
      n₁ * ((F X) 1 - (F ω.center) 1)) ^ 2 =
      ω.radius ^ 2 * (n₀ ^ 2 + n₁ ^ 2) := by 
  obtain ⟨T, hT⟩ := h_tangent
  have hd : C -ᵥ A ∈ t.direction := by
    rw [h_parallel.direction_eq, direction_affineSpan]
    exact vsub_rev_mem_vectorSpan_pair ℝ A C
  have hY : (C -ᵥ A) +ᵥ T ∈ t := t.vadd_mem_of_mem_direction hd hT.mem_space
  have ho := hT.inner_left_eq_zero_of_mem hY
  simp only [vadd_vsub] at ho
  have hoF := F.linearIsometryEquiv.inner_map_map (C -ᵥ A) (T -ᵥ ω.center)
  rw [F.map_vsub, F.map_vsub, ho] at hoF
  have hxdir := t.vsub_mem_direction hX hT.mem_space
  rw [h_parallel.direction_eq, direction_affineSpan, mem_vectorSpan_pair_rev] at hxdir
  obtain ⟨k, hk⟩ := hxdir
  have hkF := congrArg F.linearIsometryEquiv hk
  simp only [map_smul, F.map_vsub] at hkF
  have hr : dist (F T) (F ω.center) = ω.radius := by
    rw [F.dist_map]
    exact hT.mem_sphere
  simp only [vsub_eq_sub, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_two, Pi.star_apply, star_trivial, PiLp.sub_apply] at hoF
  have hk0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hkF
  have hk1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hkF
  simp only [vsub_eq_sub, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hk0 hk1
  have hrsq : ((F T) 0 - (F ω.center) 0)^2 + ((F T) 1 - (F ω.center) 1)^2 = ω.radius^2 := by
    rw [← hr, dist_eq_norm]
    rw [← real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      Pi.star_apply, star_trivial, PiLp.sub_apply]
    ring
  have hdne : (F C) 0 - (F A) 0 ≠ 0 ∨ (F C) 1 - (F A) 1 ≠ 0 := by
    by_contra! h
    apply hAC
    apply F.injective
    ext i
    fin_cases i
    · exact (sub_eq_zero.mp h.1).symm
    · exact (sub_eq_zero.mp h.2).symm
  have hdet : n₀ * ((F T) 1 - (F ω.center) 1) - n₁ * ((F T) 0 - (F ω.center) 0) = 0 := by
    rcases hdne with hdne | hdne
    · apply (mul_eq_zero.mp (show ((F C) 0 - (F A) 0) * (n₀ * ((F T) 1 - (F ω.center) 1) - n₁ * ((F T) 0 - (F ω.center) 0)) = 0 by
        nlinarith only [congrArg (fun z : ℝ => z * ((F T) 1 - (F ω.center) 1)) h_normal,
          congrArg (fun z : ℝ => n₁ * z) hoF])).resolve_left hdne
    · apply (mul_eq_zero.mp (show ((F C) 1 - (F A) 1) * (n₀ * ((F T) 1 - (F ω.center) 1) - n₁ * ((F T) 0 - (F ω.center) 0)) = 0 by
        nlinarith only [congrArg (fun z : ℝ => z * ((F T) 0 - (F ω.center) 0)) h_normal,
          congrArg (fun z : ℝ => n₀ * z) hoF])).resolve_left hdne
  have hxnormal : n₀ * ((F X) 0 - (F ω.center) 0) + n₁ * ((F X) 1 - (F ω.center) 1) = n₀ * ((F T) 0 - (F ω.center) 0) + n₁ * ((F T) 1 - (F ω.center) 1) := by
    nlinarith only [congrArg (fun z : ℝ => k * z) h_normal,
      congrArg (fun z : ℝ => n₀ * z) hk0, congrArg (fun z : ℝ => n₁ * z) hk1]
  rw [hxnormal, ← hrsq]
  nlinarith [sq_nonneg (n₀ * ((F T) 1 - (F ω.center) 1) - n₁ * ((F T) 0 - (F ω.center) 0))]
