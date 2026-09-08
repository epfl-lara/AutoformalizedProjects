import Mathlib

theorem LeanFlowProofs.PBBasic028.normalizedFrame
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C]) :
    let a : ℝ := dist B C
    let b : ℝ := dist A C
    let c : ℝ := dist A B
    let e : EuclideanSpace ℝ (Fin 2) := c⁻¹ • (B - A)
    let f : EuclideanSpace ℝ (Fin 2) := b⁻¹ • (C - A)
    let q : ℝ := inner ℝ e f
    0 < a ∧ 0 < b ∧ 0 < c ∧
      B - A = c • e ∧ C - A = b • f ∧
      ‖e‖ = 1 ∧ ‖f‖ = 1 ∧
      -1 < q ∧ q < 1 ∧
      a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * q := by   classical
  dsimp only
  let a := dist B C
  let b := dist A C
  let c := dist A B
  let e := c⁻¹ • (B - A)
  let f := b⁻¹ • (C - A)
  change 0 < a ∧ 0 < b ∧ 0 < c ∧ B - A = c • e ∧ C - A = b • f ∧
    ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ -1 < inner ℝ e f ∧ inner ℝ e f < 1 ∧ _
  have hAB : A ≠ B := by
    intro h
    have := tri.injective (show ![A, B, C] 0 = ![A, B, C] 1 from h)
    norm_num at this
  have hAC : A ≠ C := by
    intro h
    have hh := tri.injective (show ![A, B, C] 0 = ![A, B, C] 2 from h)
    exact (by decide : (0 : Fin 3) ≠ 2) hh
  have hBC : B ≠ C := by
    intro h
    have hh := tri.injective (show ![A, B, C] 1 = ![A, B, C] 2 from h)
    exact (by decide : (1 : Fin 3) ≠ 2) hh
  have ha : 0 < a := dist_pos.mpr hBC
  have hb : 0 < b := dist_pos.mpr hAC
  have hc : 0 < c := dist_pos.mpr hAB
  have hB : B - A = c • e := by simp [e, smul_smul, ne_of_gt hc]
  have hC : C - A = b • f := by simp [f, smul_smul, ne_of_gt hb]
  have hnB : ‖B - A‖ = c := by simp [c, dist_eq_norm, norm_sub_rev]
  have hnC : ‖C - A‖ = b := by simp [b, dist_eq_norm, norm_sub_rev]
  have he : ‖e‖ = 1 := by simp [e, norm_smul, Real.norm_eq_abs, abs_of_pos hc, hnB, ne_of_gt hc]
  have hf : ‖f‖ = 1 := by simp [f, norm_smul, Real.norm_eq_abs, abs_of_pos hb, hnC, ne_of_gt hb]
  have li : LinearIndependent ℝ ![B - A, C - A] := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] 0).mp tri
    let g : Fin 2 → {i : Fin 3 // i ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
    have hg : Function.Injective g := by
      intro i j hij
      exact Fin.succ_injective 2 (congrArg Subtype.val hij)
    convert! h.comp g hg using 1
    ext i
    fin_cases i <;> rfl
  have hparallel : ∀ t : ℝ, t • (C - A) ≠ B - A := (linearIndependent_fin2.mp li).2
  have hsub : e - f ≠ 0 := by
    intro h
    have hef : e = f := sub_eq_zero.mp h
    apply hparallel (c * b⁻¹)
    rw [mul_smul]
    change c • f = B - A
    rw [hB, hef]
  have hadd : e + f ≠ 0 := by
    intro h
    have hef : e = -f := eq_neg_of_add_eq_zero_left h
    apply hparallel (-(c * b⁻¹))
    rw [neg_smul, mul_smul]
    change -(c • f) = B - A
    rw [hB, hef, smul_neg]
  have hlow : -1 < inner ℝ e f := by
    have h := norm_pos_iff.mpr hadd
    have hh := norm_add_sq_real e f
    rw [he, hf] at hh
    nlinarith [sq_pos_of_pos h]
  have hupp : inner ℝ e f < 1 := by
    have h := norm_pos_iff.mpr hsub
    have hh := norm_sub_sq_real e f
    rw [he, hf] at hh
    nlinarith [sq_pos_of_pos h]
  refine ⟨ha, hb, hc, hB, hC, he, hf, hlow, hupp, ?_⟩
  have hid : B - C = (B - A) - (C - A) := by abel
  have hh := norm_sub_sq_real (B - A) (C - A)
  rw [← hid, hnB, hnC, hB, hC, real_inner_smul_left, real_inner_smul_right] at hh
  change (dist B C) ^ 2 = _
  rw [dist_eq_norm]
  nlinarith [hh]

