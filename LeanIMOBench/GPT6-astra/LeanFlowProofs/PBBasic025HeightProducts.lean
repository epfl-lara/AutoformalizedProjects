import Mathlib

theorem LeanFlowProofs.pbbasic025_heightProducts
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    ∃ D : ℝ, 0 < D ∧
      dist (s.points 1) (s.points 2) * s.height 0 = D ∧
      dist (s.points 0) (s.points 2) * s.height 1 = D ∧
      dist (s.points 0) (s.points 1) * s.height 2 = D := by 
  have gram (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
      (hface : s.points '' ({i}ᶜ : Set (Fin 3)) = {s.points j, s.points k}) :
      (dist (s.points j) (s.points k) * s.height i) ^ 2 =
        inner ℝ (s.points i - s.points j) (s.points i - s.points j) *
          inner ℝ (s.points k - s.points j) (s.points k - s.points j) -
        (inner ℝ (s.points i - s.points j) (s.points k - s.points j)) ^ 2 := by
    have hf := s.altitudeFoot_mem_affineSpan_image_compl i
    rw [hface] at hf
    have hm := vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hf
      (mem_affineSpan ℝ (Set.mem_insert (s.points j) {s.points k}))
    rw [vectorSpan_pair_rev, Submodule.mem_span_singleton] at hm
    obtain ⟨t, ht⟩ := hm
    change t • (s.points k - s.points j) = s.altitudeFoot i - s.points j at ht
    let r := s.points i - s.points j
    let w := s.points k - s.points j
    have he : s.points i - s.altitudeFoot i = r - t • w := by
      dsimp [r, w]
      rw [ht]
      abel
    have ho1 := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hij
    have ho2 := s.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hik
    have ho : inner ℝ w (r - t • w) = 0 := by
      have hw : w = (s.points k - s.altitudeFoot i) -
          (s.points j - s.altitudeFoot i) := by dsimp [w]; abel
      rw [← he, hw, inner_sub_left]
      exact sub_eq_zero.mpr (ho2.trans ho1.symm)
    have hh : s.height i ^ 2 = inner ℝ (r - t • w) (r - t • w) := by
      rw [← he, real_inner_self_eq_norm_sq]
      rfl
    have hd : dist (s.points j) (s.points k) ^ 2 = inner ℝ w w := by
      rw [real_inner_self_eq_norm_sq]
      dsimp [w]
      rw [dist_comm, dist_eq_norm]
    rw [mul_pow, hd, hh]
    change inner ℝ w w * inner ℝ (r - t • w) (r - t • w) =
      inner ℝ r r * inner ℝ w w - (inner ℝ r w) ^ 2
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right] at ho ⊢
    rw [real_inner_comm r w] at ho ⊢
    have ht' : inner ℝ r w = t * inner ℝ w w := sub_eq_zero.mp ho
    rw [ht']
    ring
  have face (i j k : Fin 3) (h : ({i}ᶜ : Set (Fin 3)) = {j, k}) :
      s.points '' ({i}ᶜ : Set (Fin 3)) = {s.points j, s.points k} := by
    rw [h, Set.image_pair]
  have h02 := gram 0 1 2 (by decide) (by decide) (face 0 1 2 (by ext a; fin_cases a <;> simp))
  have h20 := gram 2 1 0 (by decide) (by decide) (face 2 1 0 (by ext a; fin_cases a <;> simp))
  have h12 := gram 1 0 2 (by decide) (by decide) (face 1 0 2 (by ext a; fin_cases a <;> simp))
  have h21 := gram 2 0 1 (by decide) (by decide) (face 2 0 1 (by ext a; fin_cases a <;> simp))
  have eq02 : dist (s.points 1) (s.points 2) * s.height 0 =
      dist (s.points 0) (s.points 1) * s.height 2 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [h02, dist_comm (s.points 0) (s.points 1), h20, real_inner_comm (s.points 0 - s.points 1) (s.points 2 - s.points 1)]
    ring
  have eq12 : dist (s.points 0) (s.points 2) * s.height 1 =
      dist (s.points 0) (s.points 1) * s.height 2 := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [h12, h21, real_inner_comm (s.points 1 - s.points 0) (s.points 2 - s.points 0)]
    ring
  refine ⟨dist (s.points 1) (s.points 2) * s.height 0, ?_, rfl,
    eq12.trans eq02.symm, eq02.symm⟩
  exact mul_pos (dist_pos.mpr (s.independent.injective.ne (by decide))) (s.height_pos 0)

