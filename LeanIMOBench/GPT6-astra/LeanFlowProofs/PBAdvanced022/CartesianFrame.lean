import Mathlib

theorem LeanFlowProofs.PB022.cartesianFrame
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C]) :
    ∃ F : AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)),
      (F B) 0 = 0 ∧ (F B) 1 = 0 ∧
      (F C) 0 = dist B C ∧ (F C) 1 = 0 ∧
      0 < (F A) 1 := by 
  classical
  let f : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![C - B, A - B]
  have hf : LinearIndependent ℝ f := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (1 : Fin 3),
      ← linearIndependent_equiv (finSuccAboveEquiv (1 : Fin 3))] at tri
    have ht : LinearIndependent ℝ ![A - B, C - B] := by
      convert! tri using 1
      funext i
      fin_cases i <;> rfl
    convert ht.comp (fun i : Fin 2 => (1 - i : Fin 2)) (by decide) using 1
    funext i
    fin_cases i <;> rfl
  have hd : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Fintype.card (Fin 2) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hd f
  have hb (i : Fin 2) : b i = InnerProductSpace.gramSchmidtNormed ℝ f i := by
    apply InnerProductSpace.gramSchmidtOrthonormalBasis_apply
    exact (InnerProductSpace.gramSchmidtNormed_linearIndependent hf).ne_zero i
  let F := (AffineIsometryEquiv.vaddConst ℝ B).symm.trans b.repr.toAffineIsometryEquiv
  refine ⟨F, ?_, ?_, ?_, ?_, ?_⟩
  · change b.repr (B - B) 0 = 0
    simp
  · change b.repr (B - B) 1 = 0
    simp
  · change b.repr (f 0) 0 = dist B C
    rw [OrthonormalBasis.repr_apply_apply, hb]
    simp only [InnerProductSpace.gramSchmidtNormed, real_inner_smul_left]
    have hz : InnerProductSpace.gramSchmidt ℝ f 0 = f 0 :=
      InnerProductSpace.gramSchmidt_bot ℝ f
    rw [hz, real_inner_self_eq_norm_sq]
    have hn : ‖f 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hf.ne_zero 0)
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [inv_mul_eq_div, sq, mul_div_cancel_right₀ _ hn]
    simp [f, dist_eq_norm, norm_sub_rev]
  · change b.repr (f 0) 1 = 0
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular' hd f (by decide)
  · change 0 < b.repr (f 1) 1
    rw [OrthonormalBasis.repr_apply_apply, hb]
    simp only [InnerProductSpace.gramSchmidtNormed, real_inner_smul_left]
    have hg : InnerProductSpace.gramSchmidt ℝ f 1 ≠ 0 :=
      InnerProductSpace.gramSchmidt_ne_zero 1 hf
    have he : inner ℝ (InnerProductSpace.gramSchmidt ℝ f 1) (f 1) =
        ‖InnerProductSpace.gramSchmidt ℝ f 1‖ ^ 2 := by
      conv_lhs => rhs; rw [InnerProductSpace.gramSchmidt_def'' ℝ f 1]
      simp only [RCLike.ofReal_real_eq_id, id_eq]
      rw [inner_add_right, real_inner_self_eq_norm_sq]
      suffices inner ℝ (InnerProductSpace.gramSchmidt ℝ f 1)
          (∑ i ∈ Finset.Iio (1 : Fin 2),
            (inner ℝ (InnerProductSpace.gramSchmidt ℝ f i) (f 1) /
              ‖InnerProductSpace.gramSchmidt ℝ f i‖ ^ 2) •
                InnerProductSpace.gramSchmidt ℝ f i) = 0 by rw [this, add_zero]
      rw [inner_sum]
      apply Finset.sum_eq_zero
      intro i hi
      rw [inner_smul_right, InnerProductSpace.gramSchmidt_orthogonal ℝ f
        (ne_of_gt (Finset.mem_Iio.mp hi)), mul_zero]
    rw [he]
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hg)) (sq_pos_of_pos (norm_pos_iff.mpr hg))
