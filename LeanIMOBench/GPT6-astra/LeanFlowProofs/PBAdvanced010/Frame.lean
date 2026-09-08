import Mathlib

theorem LeanFlowProofs.PBAdvanced010.normalizedFrame
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C])
    (hne : dist A B ≠ dist A C) :
    ∃ (f : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2))
      (ρ a b : ℝ),
      0 < ρ ∧ a ≠ 0 ∧ b ≠ 0 ∧
      (f A) 0 = a ∧ (f A) 1 = b ∧
      (f B) 0 = -1 ∧ (f B) 1 = 0 ∧
      (f C) 0 = 1 ∧ (f C) 1 = 0 ∧
      (∀ U V : EuclideanSpace ℝ (Fin 2),
        dist (f U) (f V) = ρ * dist U V) := by 
  classical
  let e := Complex.orthonormalBasisOneI.repr
  have hBC : B ≠ C := by
    intro h
    have hh := tri.injective (show (![A,B,C] : Fin 3 → _) 1 = ![A,B,C] 2 by simpa using h)
    have hh' := congrArg Fin.val hh
    norm_num at hh'
  let d : ℂ := e.symm C - e.symm B
  have hd : d ≠ 0 := sub_ne_zero.mpr (fun h => hBC (e.symm.injective h).symm)
  let q : ℂ := 2 / d
  have hq : q ≠ 0 := div_ne_zero (by norm_num) hd
  let g : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] ℂ :=
    ((e.symm.toLinearEquiv.toAffineEquiv.trans
      (AffineEquiv.constVAdd ℝ ℂ (-e.symm B))).trans
      ((LinearEquiv.smulOfNeZero ℂ ℂ q hq).restrictScalars ℝ).toAffineEquiv).trans
      (AffineEquiv.constVAdd ℝ ℂ (-1))
  have hg (U : EuclideanSpace ℝ (Fin 2)) : g U = q * (e.symm U - e.symm B) - 1 := by
    simp [g, sub_eq_add_neg, add_comm]
  have hgB : g B = -1 := by rw [hg]; simp
  have hgC : g C = 1 := by rw [hg]; change 2 / d * d - 1 = 1; field_simp; ring
  have hscale (U V : EuclideanSpace ℝ (Fin 2)) :
      dist (g U) (g V) = ‖q‖ * dist U V := by
    rw [dist_eq_norm, hg, hg]
    have heq : q * (e.symm U - e.symm B) - 1 - (q * (e.symm V - e.symm B) - 1) = q * (e.symm U - e.symm V) := by ring
    rw [heq, norm_mul, ← dist_eq_norm, e.symm.isometry.dist_eq]
  have htri : AffineIndependent ℝ ![g A, (-1 : ℂ), 1] := by
    have heq : g ∘ ![A,B,C] = ![g A, (-1 : ℂ), 1] := by
      funext i
      fin_cases i <;> simp [Function.comp_def, hgB, hgC]
    rw [← heq]
    exact g.affineIndependent_iff.mpr tri
  have ha : (g A).re ≠ 0 := by
    intro ha0
    apply hne
    have hdist : dist (g A) (g B) = dist (g A) (g C) := by
      rw [hgB, hgC, dist_eq_norm, dist_eq_norm]
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ha0]
    rw [hscale, hscale] at hdist
    exact mul_left_cancel₀ (norm_ne_zero_iff.mpr hq) hdist
  have hb : (g A).im ≠ 0 := by
    intro hb0
    let w : Fin 3 → ℝ := ![2, (g A).re - 1, -(g A).re - 1]
    have hw : ∑ i, w i = 0 := by simp [w, Fin.sum_univ_succ]; ring
    have hv : Finset.univ.weightedVSub ![g A, (-1 : ℂ), 1] w = (0 : ℂ) := by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw (0 : ℂ), Finset.weightedVSubOfPoint_apply]
      simp only [Fin.sum_univ_succ]
      apply Complex.ext <;> simp [w, Complex.real_smul, hb0] <;> ring
    have hh := (affineIndependent_iff_of_fintype ℝ _).mp htri w hw hv 0
    norm_num [w] at hh
  let f := g.trans e.toLinearEquiv.toAffineEquiv
  have hf (U : EuclideanSpace ℝ (Fin 2)) : f U = e (g U) := rfl
  have hf0 (U : EuclideanSpace ℝ (Fin 2)) : (f U) 0 = (g U).re := by
    simpa [hf, e] using congrFun (Complex.orthonormalBasisOneI_repr_apply (g U)) 0
  have hf1 (U : EuclideanSpace ℝ (Fin 2)) : (f U) 1 = (g U).im := by
    simpa [hf, e] using congrFun (Complex.orthonormalBasisOneI_repr_apply (g U)) 1
  refine ⟨f, ‖q‖, (g A).re, (g A).im, norm_pos_iff.mpr hq, ha, hb, hf0 A, hf1 A, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hf0, hgB]
  · simp [hf1, hgB]
  · simp [hf0, hgC]
  · simp [hf1, hgC]
  · intro U V
    rw [hf, hf, e.isometry.dist_eq, hscale]

