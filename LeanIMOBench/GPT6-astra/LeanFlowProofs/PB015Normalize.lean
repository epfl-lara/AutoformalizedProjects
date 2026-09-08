import Mathlib

theorem LeanFlowProofs.pb015_normalize
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C]) :
    ∃ (r m n : ℝ)
      (Φ : AffineEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))),
      r = Affine.Simplex.inradius ⟨![A, B, C], tri⟩ ∧
      0 < r ∧ 0 < m ∧ 0 < n ∧ 1 < m * n ∧
      (∀ U V : EuclideanSpace ℝ (Fin 2), dist (Φ U) (Φ V) = dist U V / r) ∧
      Φ (Affine.Simplex.touchpoint ⟨![A, B, C], tri⟩ ∅ 0) = 0 ∧
      Φ (Affine.Simplex.incenter ⟨![A, B, C], tri⟩) 0 = 0 ∧
      Φ (Affine.Simplex.incenter ⟨![A, B, C], tri⟩) 1 = 1 ∧
      Φ B 0 = -m ∧ Φ B 1 = 0 ∧
      Φ C 0 = n ∧ Φ C 1 = 0 ∧
      Φ A 0 = -(n - m) / (m * n - 1) ∧
      Φ A 1 = 2 * m * n / (m * n - 1) := by set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
  classical
  have map_orth (Φ : AffineEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (r : ℝ) (hd : ∀ U V, dist (Φ U) (Φ V) = dist U V / r)
      (U V W : EuclideanSpace ℝ (Fin 2)) (h : inner ℝ (U-W) (V-W) = 0) :
      inner ℝ (Φ U-Φ W) (Φ V-Φ W) = 0 := by
    rw [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two] at h ⊢
    simp only [sub_sub_sub_cancel_right, ← dist_eq_norm] at h ⊢
    rw [hd, hd, hd]
    calc
      _ = (dist U W * dist U W + dist V W * dist V W - dist U V * dist U V) / 2 / r ^ 2 := by ring
      _ = 0 := by rw [h]; simp
  have tangent_algebra (x y m u v : ℝ) (hy : 0 < y)
      (hc : u^2 + (v-1)^2 = 1)
      (hb : (-m-u)*u + (-v)*(v-1) = 0)
      (ha : (x-u)*u + (y-v)*(v-1) = 0) :
      2*m*x+(1-m^2)*y+2*m^2 = 0 := by
    have hv : v = -m*u := by nlinarith
    have hu : u ≠ 0 := by
      intro h
      rw [h] at hv ha
      simp only [mul_zero, neg_zero] at hv
      rw [hv] at ha
      nlinarith
    have hu' : (m^2+1)*u = -2*m := by
      have hh : u*((m^2+1)*u+2*m) = 0 := by rw [hv] at hc; nlinarith [hc]
      have := (mul_eq_zero.mp hh).resolve_left hu
      linarith
    have hh : x*u+y*(-m*u-1)+m*u = 0 := by rw [hv] at ha hc; nlinarith
    linear_combination (x-m*y+m)*hu' - (m^2+1)*hh
  have side_eq (A B I T : EuclideanSpace ℝ (Fin 2))
      (Φ : AffineEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (r m : ℝ) (hr : 0 < r)
      (hd : ∀ U V, dist (Φ U) (Φ V) = dist U V / r)
      (hI : Φ I = !₂[0,1]) (hB : Φ B = !₂[-m,0]) (hy : 0 < Φ A 1)
      (hc : dist I T = r)
      (hA : inner ℝ (A-T) (I-T) = 0) (hBt : inner ℝ (B-T) (I-T) = 0) :
      2*m*Φ A 0+(1-m^2)*Φ A 1+2*m^2 = 0 := by
    have ha := map_orth Φ r hd A I T hA
    have hb := map_orth Φ r hd B I T hBt
    have hct := hd I T
    rw [hc, div_self hr.ne', hI] at hct
    have hc' : (Φ T 0)^2+(Φ T 1-1)^2=1 := by
      have hh := congrArg (fun z : ℝ => z^2) hct
      rw [dist_eq_norm, EuclideanSpace.norm_eq] at hh
      simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_two] at hh
      rw [Real.sq_sqrt (by positivity)] at hh
      simp at hh
      nlinarith
    rw [hI] at ha
    rw [hI, hB] at hb
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail] at ha hb
    apply tangent_algebra (Φ A 0) (Φ A 1) m (Φ T 0) (Φ T 1) hy hc'
    · nlinarith [hb]
    · nlinarith [ha]
  have frame (D I C : EuclideanSpace ℝ (Fin 2)) (r c : ℝ)
      (hr : 0 < r) (hc : 0 < c)
      (hI : ‖I-D‖ = r) (hC : ‖C-D‖ = c)
      (horth : inner ℝ (C-D) (I-D) = 0) :
      ∃ Φ : AffineEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)),
        (∀ U V, dist (Φ U) (Φ V) = dist U V / r) ∧
        Φ D = 0 ∧ Φ I = !₂[0,1] ∧ Φ C = !₂[c/r,0] := by
    let v : Fin 2 → EuclideanSpace ℝ (Fin 2) := ![c⁻¹ • (C-D), r⁻¹ • (I-D)]
    have horth' : inner ℝ (I-D) (C-D) = 0 := by rw [real_inner_comm, horth]
    have hon : Orthonormal ℝ v := by
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;> dsimp [v] <;>
        simp [inner_smul_left, inner_smul_right, horth, horth',
          norm_smul, Real.norm_eq_abs, abs_of_pos hc, abs_of_pos hr,
          hI, hC, hr.ne', hc.ne']
    let b := OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
    let Φ := (AffineEquiv.vaddConst ℝ D).symm |>.trans
      (b.repr.toLinearEquiv.toAffineEquiv.trans
        (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 2)) r⁻¹ (inv_ne_zero hr.ne')).toAffineEquiv)
    have hΦ (P : EuclideanSpace ℝ (Fin 2)) : Φ P = r⁻¹ • b.repr (P-D) := rfl
    refine ⟨Φ, ?_, ?_, ?_, ?_⟩
    · intro U V
      rw [hΦ, hΦ, dist_smul₀, b.repr.dist_map, dist_sub_right]
      simp [Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv, mul_comm]
    · rw [hΦ]; simp
    · ext i
      rw [hΦ]
      change r⁻¹ * (b.repr (I-D) i) = (![0,1] : Fin 2 → ℝ) i
      rw [OrthonormalBasis.repr_apply_apply]
      simp only [b, OrthonormalBasis.coe_mk]
      fin_cases i <;> dsimp [v] <;>
        rw [real_inner_smul_left]
      · rw [horth]; ring
      · rw [real_inner_self_eq_norm_sq, hI]; field_simp
    · ext i
      rw [hΦ]
      change r⁻¹ * (b.repr (C-D) i) = (![c/r,0] : Fin 2 → ℝ) i
      rw [OrthonormalBasis.repr_apply_apply]
      simp only [b, OrthonormalBasis.coe_mk]
      fin_cases i <;> dsimp [v] <;>
        rw [real_inner_smul_left]
      · rw [real_inner_self_eq_norm_sq, hC]; field_simp
      · rw [horth']; ring
  have base (A B C : EuclideanSpace ℝ (Fin 2))
      (tri : AffineIndependent ℝ ![A,B,C]) :
      let s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A,B,C],tri⟩
      ∃ (r m n : ℝ) (Φ : AffineEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))),
      r = s.inradius ∧ 0 < r ∧ 0 < m ∧ 0 < n ∧
      (∀ U V, dist (Φ U) (Φ V) = dist U V / r) ∧
      Φ (s.touchpoint ∅ 0) = 0 ∧ Φ s.incenter = !₂[0,1] ∧
      Φ B = !₂[-m,0] ∧ Φ C = !₂[n,0] ∧ 0 < Φ A 1 := by
    dsimp only
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩
    let s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A,B,C],tri⟩
    let D := s.touchpoint ∅ 0
    let I := s.incenter
    let r := s.inradius
    have hr : 0 < r := s.inradius_pos
    have hbet := Affine.Triangle.sbtw_touchpoint_empty s (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)
    change Sbtw ℝ B D C at hbet
    have ht : s.insphere.IsTangentAt D (affineSpan ℝ {B,C}) := by
      change s.insphere.IsTangentAt D (affineSpan ℝ {s.points 1,s.points 2})
      rw [s.affineSpan_pair_eq_orthRadius_insphere (by decide : (0:Fin 3) ≠ 1)
        (by decide : (0:Fin 3) ≠ 2) (by decide)]
      exact EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem.mpr (s.touchpoint_mem_insphere 0)
    have hC : C ∈ affineSpan ℝ {B,C} := mem_affineSpan ℝ (by simp)
    have horth : inner ℝ (C-D) (I-D) = 0 := by
      have h := ht.inner_left_eq_zero_of_mem hC
      change inner ℝ (C-D) (D-I) = 0 at h
      rw [← neg_sub I D, inner_neg_right, neg_eq_zero] at h
      exact h
    have hc : 0 < dist C D := dist_pos.mpr hbet.ne_right.symm
    have hI : ‖I-D‖ = r := by
      simpa only [dist_eq_norm, dist_comm] using s.dist_incenter 0
    obtain ⟨Φ, hdist, hD, hI', hC'⟩ := frame D I C r (dist C D) hr hc hI
      (dist_eq_norm C D).symm horth
    let m := dist B D / r
    let n := dist C D / r
    have hm : 0 < m := div_pos (dist_pos.mpr hbet.ne_left.symm) hr
    have hn : 0 < n := div_pos hc hr
    have hB' : Φ B = !₂[-m,0] := by
      have hb := hbet.wbtw
      rw [wbtw_iff_left_eq_or_right_mem_image_Ici] at hb
      rcases hb with hb | ⟨t, ht, hte⟩
      · exact False.elim (hbet.ne_left hb.symm)
      · have he := congrArg Φ hte
        change Φ.toAffineMap (AffineMap.lineMap B D t) = Φ C at he
        rw [AffineMap.apply_lineMap] at he
        change AffineMap.lineMap (Φ B) (Φ D) t = Φ C at he
        rw [hD, hC'] at he
        have he0 := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 0) he
        have he1 := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 1) he
        simp [AffineMap.lineMap_apply] at he0 he1
        have ht1 : t ≠ 1 := by intro h; subst t; simp at he0; linarith [div_pos hc hr]
        have hb1 : Φ B 1 = 0 := by
          have hh : (t-1) * Φ B 1 = 0 := by linarith
          exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr ht1)
        have hnorm := hdist B D
        rw [hD, dist_zero_right] at hnorm
        have hnorm' : |Φ B 0| = m := by
          simpa [EuclideanSpace.norm_eq, Fin.sum_univ_two, hb1, Real.sqrt_sq_eq_abs] using hnorm
        have hb0 : Φ B 0 = -m := by
          have hh : Φ B 0 < 0 := by
            by_contra hh
            have := mul_nonneg (sub_nonneg.mpr ht) (le_of_not_gt hh)
            nlinarith [div_pos hc hr]
          rw [abs_of_neg hh] at hnorm'
          linarith
        ext i
        fin_cases i <;> simp [hb0, hb1]
    have hAy : 0 < Φ A 1 := by
      have hw := s.excenterExists_empty.sum_excenterWeights_eq_one
      have hi : Φ I = Finset.univ.affineCombination ℝ (Φ ∘ s.points) (s.excenterWeights ∅) := by
        exact Finset.univ.map_affineCombination s.points (s.excenterWeights ∅) hw Φ.toAffineMap
      rw [hI'] at hi
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hi
      have hi1 := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 1) hi
      simp [Fin.sum_univ_succ, s, hB', hC'] at hi1
      have hwpos := s.excenterWeights_empty_pos 0
      nlinarith
    exact ⟨r,m,n,Φ,rfl,hr,hm,hn,hdist,hD,hI',hB',hC',hAy⟩
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) := ⟨by simp⟩
  let s : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![A,B,C],tri⟩
  obtain ⟨r,m,n,Φ,hradius,hr,hm,hn,hd,hD,hI,hB,hC,hy⟩ := base A B C tri
  have hort (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      inner ℝ (s.points j - s.touchpoint ∅ i) (s.incenter - s.touchpoint ∅ i) = 0 ∧
      inner ℝ (s.points k - s.touchpoint ∅ i) (s.incenter - s.touchpoint ∅ i) = 0 := by
    have ht : s.insphere.IsTangentAt (s.touchpoint ∅ i) (affineSpan ℝ {s.points j,s.points k}) := by
      rw [s.affineSpan_pair_eq_orthRadius_insphere hij hik hjk]
      exact EuclideanGeometry.Sphere.isTangentAt_orthRadius_iff_mem.mpr (s.touchpoint_mem_insphere i)
    have ha := ht.inner_left_eq_zero_of_mem (mem_affineSpan ℝ (by simp : s.points j ∈ ({s.points j,s.points k} : Set _)))
    have hb := ht.inner_left_eq_zero_of_mem (mem_affineSpan ℝ (by simp : s.points k ∈ ({s.points j,s.points k} : Set _)))
    change inner ℝ (s.points j - s.touchpoint ∅ i) (s.touchpoint ∅ i - s.incenter) = 0 at ha
    change inner ℝ (s.points k - s.touchpoint ∅ i) (s.touchpoint ∅ i - s.incenter) = 0 at hb
    rw [← neg_sub s.incenter _, inner_neg_right, neg_eq_zero] at ha hb
    exact ⟨ha,hb⟩
  have hl : 2*m*Φ A 0+(1-m^2)*Φ A 1+2*m^2 = 0 := by
    have ht := hort 2 0 1 (by decide) (by decide) (by decide)
    exact side_eq A B s.incenter (s.touchpoint ∅ 2) Φ r m hr hd hI hB hy
      (by rw [hradius]; exact s.dist_incenter 2) ht.1 ht.2
  have hright : -2*n*Φ A 0+(1-n^2)*Φ A 1+2*n^2 = 0 := by
    have ht := hort 1 0 2 (by decide) (by decide) (by decide)
    have hh := side_eq A C s.incenter (s.touchpoint ∅ 1) Φ r (-n) hr hd hI
      (by simpa using hC) hy (by rw [hradius]; exact s.dist_incenter 1) ht.1 ht.2
    nlinarith only [hh]
  have heq : (m*n-1)*Φ A 1 = 2*m*n := by
    have hsum : (m+n)*((m*n-1)*Φ A 1-2*m*n) = 0 := by
      linear_combination -n*hl-m*hright
    have hh := (mul_eq_zero.mp hsum).resolve_left (ne_of_gt (add_pos hm hn))
    linarith
  have hp : 1 < m*n := by
    have hp0 := mul_pos hm hn
    by_contra hh
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hh)) hy.le
    nlinarith
  have hAy : Φ A 1 = 2*m*n/(m*n-1) := (eq_div_iff (ne_of_gt (sub_pos.mpr hp))).mpr (by nlinarith only [heq])
  have hAx : Φ A 0 = -(n-m)/(m*n-1) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr hp))).mpr
    have hh : 2*m*((m*n-1)*Φ A 0+(n-m)) = 0 := by
      linear_combination (m*n-1)*hl-(1-m^2)*heq
    have hh' := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (mul_pos (by norm_num) hm))
    nlinarith only [hh']
  refine ⟨r,m,n,Φ,hradius,hr,hm,hn,hp,hd,hD,?_,?_,?_,?_,?_,?_,hAx,hAy⟩ <;>
    simp [hI,hB,hC]

