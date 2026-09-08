import Mathlib

theorem LeanFlowProofs.PB003.forwardBisectorOfInternalTangency
    (A B C T : EuclideanSpace ℝ (Fin 2))
    (hABC : AffineIndependent ℝ ![A, B, C])
    (ω c : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (hA : A ∈ ω) (hB : B ∈ ω) (hC : C ∈ ω)
    (hAB : c.IsTangent (affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2)))))
    (hAC : c.IsTangent (affineSpan ℝ ({A, C} : Set (EuclideanSpace ℝ (Fin 2)))))
    (hT : c.IsIntTangentAt ω T) :
    (c.radius = 0 ∧ c.center = A ∧ T = A) ∨
      (0 < c.radius ∧ ∃ t : ℝ, 0 < t ∧
        c.center = A + t •
          (‖B - A‖⁻¹ • (B - A) + ‖C - A‖⁻¹ • (C - A))) := by classical
  have hli : LinearIndependent ℝ ![B - A, C - A] := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0).mp hABC
    let f : Fin 2 → {i : Fin 3 // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
    have hf : Function.Injective f := by
      intro i j hij
      exact Fin.succ_injective _ (congrArg Subtype.val hij)
    convert! h.comp f hf using 1
    ext i
    fin_cases i <;> rfl
  have hb : 0 < ‖B - A‖ := norm_pos_iff.mpr (hli.ne_zero 0)
  have hc : 0 < ‖C - A‖ := norm_pos_iff.mpr (hli.ne_zero 1)
  have hspan : Submodule.span ℝ ({B - A, C - A} : Set _) = ⊤ := by
    simpa [Set.pair_comm, finrank_euclideanSpace] using
      hli.span_eq_top_of_card_eq_finrank (by simp [finrank_euclideanSpace])
  have hext : ∀ v : EuclideanSpace ℝ (Fin 2),
      inner ℝ v (B - A) = 0 → inner ℝ v (C - A) = 0 → v = 0 := by
    intro v hvb hvc
    have hv : v ∈ Submodule.span ℝ ({B - A, C - A} : Set _) := by rw [hspan]; trivial
    obtain ⟨a, b, hv⟩ := Submodule.mem_span_pair.mp hv
    have hz : inner ℝ v v = 0 := by
      conv_lhs => rhs; rw [← hv]
      simp [inner_add_right, real_inner_smul_right, hvb, hvc]
    simpa using hz
  have hr : 0 ≤ c.radius := c.radius_nonneg_of_mem hT.mem_left
  have hcontain : ∀ P ∈ c, dist P ω.center ≤ ω.radius := by
    intro P hP
    have hdist := hT.isIntTangent.dist_center
    have hh := dist_triangle P c.center ω.center
    have hp : dist P c.center = c.radius := hP
    linarith
  obtain ⟨P, hP⟩ := hAB
  obtain ⟨Q, hQ⟩ := hAC
  have hequal : dist A P = dist A Q :=
    hP.dist_eq_of_mem_of_mem hQ (left_mem_affineSpan_pair ℝ A B)
      (left_mem_affineSpan_pair ℝ A C)
  have hfoot : ∀ (D F : EuclideanSpace ℝ (Fin 2)), D ∈ ω → 0 < ‖D - A‖ →
      c.IsTangentAt F (affineSpan ℝ ({A, D} : Set _)) →
      inner ℝ (c.center - A) (‖D - A‖⁻¹ • (D - A)) = dist A F := by
    intro D F hD hn hF
    obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hF.mem_space
    have hf : F = u • (D - A) + A := by
      simpa [AffineMap.lineMap_apply] using hu.symm
    have hnormA : ‖A - ω.center‖ ^ 2 = ω.radius ^ 2 := by
      have hh : dist A ω.center = ω.radius := hA
      simpa [dist_eq_norm] using congrArg (fun x : ℝ => x ^ 2) hh
    have hnormD : ‖(D - A) + (A - ω.center)‖ ^ 2 = ω.radius ^ 2 := by
      have hh : dist D ω.center = ω.radius := hD
      simpa [dist_eq_norm] using congrArg (fun x : ℝ => x ^ 2) hh
    have hnormF : ‖u • (D - A) + (A - ω.center)‖ ^ 2 ≤ ω.radius ^ 2 := by
      have hh := hcontain F hF.mem_sphere
      have hh2 := sq_le_sq₀ dist_nonneg (ω.radius_nonneg_of_mem hA) |>.mpr hh
      simpa [dist_eq_norm, hf, add_sub_assoc] using hh2
    rw [norm_add_sq_real] at hnormD hnormF
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at hnormF
    have hprod : u * (u - 1) * ‖D - A‖ ^ 2 ≤ 0 := by
      nlinarith [congrArg (fun x : ℝ => u * x) hnormD,
        congrArg (fun x : ℝ => u * x) hnormA]
    have hu0 : 0 ≤ u := by
      by_contra hh
      have hh' : 0 < u * (u - 1) := mul_pos_of_neg_of_neg (lt_of_not_ge hh) (by linarith)
      have := mul_pos hh' (sq_pos_of_pos hn)
      linarith
    have hdist : dist A F = u * ‖D - A‖ := by
      rw [dist_comm, dist_eq_norm, hf, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hu0]
    have hperpA := hF.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ A D)
    have hperpD := hF.inner_left_eq_zero_of_mem (right_mem_affineSpan_pair ℝ A D)
    have hperp : inner ℝ (D - A) (F - c.center) = 0 := by
      have he : D - A = (D - F) - (A - F) := by abel
      rw [he, inner_sub_left]
      exact sub_eq_zero.mpr (hperpD.trans hperpA.symm)
    have he : F - c.center = u • (D - A) - (c.center - A) := by rw [hf]; abel
    rw [he, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hperp
    rw [real_inner_smul_right, real_inner_comm (D - A) (c.center - A), hdist]
    have hn0 : ‖D - A‖ ≠ 0 := ne_of_gt hn
    field_simp
    nlinarith
  have hpb := hfoot B P hB hb hP
  have hqc := hfoot C Q hC hc hQ
  rw [← hequal] at hqc
  let U := ‖B - A‖⁻¹ • (B - A)
  let V := ‖C - A‖⁻¹ • (C - A)
  have hU : ‖U‖ = 1 := norm_smul_inv_norm (hli.ne_zero 0)
  have hV : ‖V‖ = 1 := norm_smul_inv_norm (hli.ne_zero 1)
  have hliUV : LinearIndependent ℝ ![U, V] := by
    convert! hli.units_smul (fun i => Units.mk0 (‖![B - A, C - A] i‖⁻¹)
      (inv_ne_zero (norm_ne_zero_iff.mpr (hli.ne_zero i)))) using 1
    ext i
    fin_cases i <;> rfl
  have hplusne : U + V ≠ 0 := by
    intro hh
    apply (linearIndependent_fin2.mp hliUV).2 (-1)
    simpa using (eq_neg_of_add_eq_zero_left hh).symm
  have hminusne : U - V ≠ 0 := by
    intro hh
    apply (linearIndependent_fin2.mp hliUV).2 1
    simpa using (sub_eq_zero.mp hh).symm
  have hplus : 0 < 1 + inner ℝ U V := by
    have hh := norm_add_sq_real U V
    rw [hU, hV] at hh
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hplusne)]
  have hminus : 0 < 1 - inner ℝ U V := by
    have hh := norm_sub_sq_real U V
    rw [hU, hV] at hh
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hminusne)]
  have hextUV : ∀ W : EuclideanSpace ℝ (Fin 2),
      inner ℝ W U = 0 → inner ℝ W V = 0 → W = 0 := by
    intro W hwU hwV
    apply hext
    · simpa only [U, real_inner_smul_right, mul_eq_zero, inv_eq_zero,
        ne_of_gt hb, false_or] using hwU
    · simpa only [V, real_inner_smul_right, mul_eq_zero, inv_eq_zero,
        ne_of_gt hc, false_or] using hwV
  have hpyth := hP.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ A B)
  by_cases hd : dist A P = 0
  · have hcenter : c.center = A := by
      apply sub_eq_zero.mp
      apply hextUV
      · exact hpb.trans hd
      · exact hqc.trans hd
    have hr0 : c.radius = 0 := by
      rw [hcenter, dist_self, hd] at hpyth
      nlinarith
    left
    refine ⟨hr0, hcenter, ?_⟩
    have hh : dist T c.center = c.radius := hT.mem_left
    simpa [hr0, hcenter] using hh
  · have hdpos : 0 < dist A P := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
    let t := dist A P / (1 + inner ℝ U V)
    have ht : 0 < t := div_pos hdpos hplus
    have htval : t * (1 + inner ℝ U V) = dist A P :=
      div_mul_cancel₀ _ (ne_of_gt hplus)
    have hcenter : c.center - A = t • (U + V) := by
      apply sub_eq_zero.mp
      apply hextUV
      · rw [inner_sub_left, hpb, real_inner_smul_left, inner_add_left,
          real_inner_self_eq_norm_sq, hU, real_inner_comm U V]
        nlinarith
      · rw [inner_sub_left, hqc, real_inner_smul_left, inner_add_left,
          real_inner_self_eq_norm_sq, hV]
        nlinarith
    have hnorm : ‖c.center - A‖ ^ 2 = t ^ 2 * (2 + 2 * inner ℝ U V) := by
      rw [hcenter, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        norm_add_sq_real, hU, hV]
      ring
    have hrpos : 0 < c.radius := by
      have hd2 : dist A P ^ 2 = t ^ 2 * (1 + inner ℝ U V) ^ 2 := by
        rw [← htval]; ring
      rw [dist_comm A c.center, dist_eq_norm] at hpyth
      have heq : c.radius ^ 2 = t ^ 2 * ((1 + inner ℝ U V) * (1 - inner ℝ U V)) := by
        nlinarith [hnorm, hd2]
      have hh := mul_pos (sq_pos_of_pos ht) (mul_pos hplus hminus)
      nlinarith
    right
    refine ⟨hrpos, t, ht, ?_⟩
    change c.center = A + t • (U + V)
    rw [← hcenter]
    abel
