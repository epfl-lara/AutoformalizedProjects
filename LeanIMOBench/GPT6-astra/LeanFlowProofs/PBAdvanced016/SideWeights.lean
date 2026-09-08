import Mathlib

theorem LeanFlowProofs.PB016.incenter_side_weights
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C]) :
    (dist B C + dist C A + dist A B) •
        (Affine.Simplex.incenter ⟨![A, B, C], tri⟩ - A) =
      dist C A • (B - A) + dist A B • (C - A) := by classical
  let s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨![A,B,C],tri⟩
  have dsq (P Q : EuclideanSpace ℝ (Fin 2)) :
      dist P Q ^ 2 = (P 0 - Q 0)^2 + (P 1 - Q 1)^2 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      PiLp.sub_apply, pow_two]
  have geom (P Q R F : EuclideanSpace ℝ (Fin 2))
      (hf : F ∈ affineSpan ℝ {Q,R})
      (horth : inner ℝ (R-Q) (P-F) = 0) :
      dist P F ^ 2 * dist Q R ^ 2 =
        ((P 0-Q 0)*(R 1-Q 1)-(P 1-Q 1)*(R 0-Q 0))^2 := by
    obtain ⟨t, rfl⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hf
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial,
      PiLp.sub_apply] at horth
    simp only [dsq]
    simp [AffineMap.lineMap_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
      smul_eq_mul] at horth ⊢
    nlinarith [sq_nonneg ((R 0-Q 0)*(P 0-(t*(R 0-Q 0)+Q 0)) +
      (R 1-Q 1)*(P 1-(t*(R 1-Q 1)+Q 1)))]
  have hgeom (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      s.height i ^ 2 * dist (s.points j) (s.points k) ^ 2 =
        (((s.points i) 0-(s.points j) 0)*((s.points k) 1-(s.points j) 1)-
         ((s.points i) 1-(s.points j) 1)*((s.points k) 0-(s.points j) 0))^2 := by
    apply geom
    · have he : s.points '' {i}ᶜ = {s.points j, s.points k} := by
        ext x
        simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
          Set.mem_insert_iff]
        constructor
        · rintro ⟨l, hl, rfl⟩
          have : l = j ∨ l = k := by omega
          rcases this with rfl | rfl <;> simp
        · rintro (rfl | rfl)
          · exact ⟨j, Ne.symm hij, rfl⟩
          · exact ⟨k, Ne.symm hik, rfl⟩
      rw [← he]
      exact s.altitudeFoot_mem_affineSpan_image_compl i
    · have hj := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hij
      have hk := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hik
      change inner ℝ (s.points j - s.altitudeFoot i) (s.points i - s.altitudeFoot i) = 0 at hj
      change inner ℝ (s.points k - s.altitudeFoot i) (s.points i - s.altitudeFoot i) = 0 at hk
      have hv : s.points k - s.points j =
          (s.points k-s.altitudeFoot i) - (s.points j-s.altitudeFoot i) := by abel
      rw [hv, inner_sub_left, hk, hj, sub_self]
  have h0 := hgeom 0 1 2 (by decide) (by decide) (by decide)
  have h1 := hgeom 1 2 0 (by decide) (by decide) (by decide)
  have h2 := hgeom 2 0 1 (by decide) (by decide) (by decide)
  simp only [s, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hp0 := s.height_pos 0
  have hp1 := s.height_pos 1
  have hp2 := s.height_pos 2
  have e01 : s.height 0 * dist B C = s.height 1 * dist C A := by
    apply (sq_eq_sq₀ (mul_nonneg hp0.le dist_nonneg)
      (mul_nonneg hp1.le dist_nonneg)).mp
    calc
      _ = ((A 0-B 0)*(C 1-B 1)-(A 1-B 1)*(C 0-B 0))^2 := by
        simpa only [mul_pow] using h0
      _ = ((B 0-C 0)*(A 1-C 1)-(B 1-C 1)*(A 0-C 0))^2 := by ring
      _ = _ := by simpa only [mul_pow] using h1.symm
  have e02 : s.height 0 * dist B C = s.height 2 * dist A B := by
    apply (sq_eq_sq₀ (mul_nonneg hp0.le dist_nonneg)
      (mul_nonneg hp2.le dist_nonneg)).mp
    calc
      _ = ((A 0-B 0)*(C 1-B 1)-(A 1-B 1)*(C 0-B 0))^2 := by
        simpa only [mul_pow] using h0
      _ = ((C 0-A 0)*(B 1-A 1)-(C 1-A 1)*(B 0-A 0))^2 := by ring
      _ = _ := by simpa only [mul_pow] using h2.symm
  have ha : 0 < dist B C := dist_pos.mpr (by
    intro h
    have hh := tri.injective (show (![A,B,C] : Fin 3 → _) 1 = ![A,B,C] 2 from h)
    exact (by decide : (1 : Fin 3) ≠ 2) hh)
  let K := s.height 0 * dist B C
  have hK : K ≠ 0 := ne_of_gt (mul_pos hp0 ha)
  have hinv : ∀ i : Fin 3, (s.height i)⁻¹ = ![dist B C, dist C A, dist A B] i / K := by
    intro i
    have hh : s.height i * (![dist B C, dist C A, dist A B] : Fin 3 → ℝ) i = K := by
      fin_cases i
      · rfl
      · exact e01.symm
      · exact e02.symm
    apply (eq_div_iff hK).2
    rw [← hh]
    simp [(s.height_pos i).ne']
  have hsum : (∑ i : Fin 3, (s.height i)⁻¹) =
      (dist B C + dist C A + dist A B) / K := by
    simp [hinv, Fin.sum_univ_succ, add_div, add_assoc]
  have hper : dist B C + dist C A + dist A B ≠ 0 := by
    have := dist_nonneg (x := C) (y := A)
    have := dist_nonneg (x := A) (y := B)
    positivity
  have hw (i : Fin 3) : (dist B C + dist C A + dist A B) *
      s.excenterWeights ∅ i = ![dist B C, dist C A, dist A B] i := by
    simp only [Affine.Simplex.excenterWeights, Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply]
    rw [hsum, hinv]
    field_simp
  have hv := Finset.sum_smul_vsub_const_eq_affineCombination_vsub
    (Finset.univ : Finset (Fin 3)) (s.excenterWeights ∅) s.points A
    s.excenterExists_empty.sum_excenterWeights_eq_one
  change (∑ i : Fin 3, s.excenterWeights ∅ i • (s.points i - A)) = s.incenter - A at hv
  change _ • (s.incenter - A) = _
  rw [← hv, Finset.smul_sum]
  simp only [smul_smul, hw]
  simp [s, Fin.sum_univ_succ]

