import Mathlib

theorem LeanFlowProofs.PBBasic028.insideTwoLineTangency
    (A B C e f : EuclideanSpace ℝ (Fin 2))
    (b c q : ℝ)
    (hb : 0 < b) (hc : 0 < c)
    (hB : B - A = c • e) (hC : C - A = b • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hq : inner ℝ e f = q)
    (hql : -1 < q) (hqu : q < 1)
    (W : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (X Y : EuclideanSpace ℝ (Fin 2))
    (hX : W.IsTangentAt X (affineSpan ℝ {A, B}))
    (hY : W.IsTangentAt Y (affineSpan ℝ {A, C}))
    (inside : W.center ∈ convexHull ℝ {A, B, C}) :
    ∃ k : ℝ,
      0 ≤ k ∧ k * (b + c) ≤ b * c ∧
      W.center - A = k • (e + f) ∧
      X - A = (k * (1 + q)) • e ∧
      Y - A = (k * (1 + q)) • f ∧
      0 ≤ W.radius ∧
      W.radius ^ 2 = k ^ 2 * (1 - q ^ 2) := by 
  have hull : ∃ U V : ℝ, 0 ≤ U ∧ 0 ≤ V ∧ b * U + c * V ≤ b * c ∧
      W.center - A = U • e + V • f := by
    let S : Set (EuclideanSpace ℝ (Fin 2)) := {z | ∃ U V : ℝ,
      0 ≤ U ∧ 0 ≤ V ∧ b * U + c * V ≤ b * c ∧ z - A = U • e + V • f}
    have hs : Convex ℝ S := by
      rintro x ⟨U, V, hU, hV, hUV, hx⟩ y ⟨U', V', hU', hV', hUV', hy⟩ t s ht hs hts
      refine ⟨t * U + s * U', t * V + s * V', by positivity, by positivity, ?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_left hUV ht, mul_le_mul_of_nonneg_left hUV' hs, congrArg (fun r : ℝ => r * (b * c)) hts]
      · have hx' : x = U • e + V • f + A := (sub_eq_iff_eq_add).mp hx
        have hy' : y = U' • e + V' • f + A := (sub_eq_iff_eq_add).mp hy
        rw [hx', hy']
        have ha : (t + s) • A = A := by rw [hts, one_smul]
        linear_combination (norm := module) ha
    apply convexHull_min (t := S) ?_ hs inside
    intro z hz
    rcases hz with rfl | hz
    · exact ⟨0, 0, le_rfl, le_rfl, by nlinarith [mul_pos hb hc], by simp⟩
    rcases hz with rfl | hz
    · exact ⟨c, 0, hc.le, le_rfl, by nlinarith, by simpa using hB⟩
    · rcases hz with rfl
      exact ⟨0, b, le_rfl, hb.le, by nlinarith, by simpa using hC⟩
  obtain ⟨U, V, hU, hV, hUV, hz⟩ := hull
  have linecalc : ∀ (D g P : EuclideanSpace ℝ (Fin 2)) (d : ℝ),
      0 < d → D - A = d • g → ‖g‖ = 1 →
      W.IsTangentAt P (affineSpan ℝ {A, D}) →
      ∃ t : ℝ, P - A = t • g ∧
        inner ℝ (W.center - A) g = t ∧
        ‖W.center - A‖ ^ 2 = W.radius ^ 2 + t ^ 2 := by
    intro D g P d hd hD hg hP
    have hA : A ∈ affineSpan ℝ {A, D} := subset_affineSpan ℝ _ (by simp)
    have hDm : D ∈ affineSpan ℝ {A, D} := subset_affineSpan ℝ _ (by simp)
    have hp := (affineSpan ℝ {A, D}).vsub_mem_direction hP.mem_space hA
    rw [direction_affineSpan, vectorSpan_pair_rev] at hp
    change P - A ∈ Submodule.span ℝ {D - A} at hp
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hp
    have ht : P - A = (s * d) • g := by rw [← hs, hD, smul_smul]
    refine ⟨s * d, ht, ?_, ?_⟩
    · have h1 := hP.inner_left_eq_zero_of_mem hA
      have h2 := hP.inner_left_eq_zero_of_mem hDm
      have horth : inner ℝ (D - A) (P - W.center) = 0 := by
        change inner ℝ (A - P) (P - W.center) = 0 at h1
        change inner ℝ (D - P) (P - W.center) = 0 at h2
        rw [show D - A = (D - P) - (A - P) by abel, inner_sub_left, h1, h2, sub_self]
      rw [hD, inner_smul_left] at horth
      have hgorth : inner ℝ g (P - W.center) = 0 := (mul_eq_zero.mp horth).resolve_left hd.ne'
      have hpz : P - W.center = (s * d) • g - (W.center - A) := by rw [← ht]; abel
      rw [hpz, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hg] at hgorth
      rw [real_inner_comm]
      nlinarith
    · have hdist := hP.dist_sq_eq_of_mem hA
      rw [dist_comm A W.center, dist_eq_norm, dist_comm A P, dist_eq_norm, ht,
        norm_smul, Real.norm_eq_abs, hg, mul_one, sq_abs] at hdist
      exact hdist
  obtain ⟨t, ht, hte, htr⟩ := linecalc B e X c hc hB he hX
  obtain ⟨s, hs, hsf, hsr⟩ := linecalc C f Y b hb hC hf hY
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hff : inner ℝ f f = 1 := by rw [real_inner_self_eq_norm_sq, hf]; norm_num
  have hfe : inner ℝ f e = q := by rw [real_inner_comm, hq]
  rw [hz, inner_add_left, inner_smul_left, inner_smul_left, hee, hfe] at hte
  rw [hz, inner_add_left, inner_smul_left, inner_smul_left, hff, hq] at hsf
  simp only [starRingEnd_apply, star_trivial, mul_one] at hte hsf
  have heq : U = V := by
    have hsq : (U ^ 2 - V ^ 2) * (1 - q ^ 2) = 0 := by
      rw [← hte] at htr
      rw [← hsf] at hsr
      nlinarith only [htr, hsr]
    have hpos : 0 < 1 - q ^ 2 := by nlinarith
    have huv2 : U ^ 2 = V ^ 2 := by
      have := (mul_eq_zero.mp hsq).resolve_right hpos.ne'
      linarith
    nlinarith
  subst V
  refine ⟨U, hU, by nlinarith, ?_, ?_, ?_, W.radius_nonneg_of_mem hX.mem_sphere, ?_⟩
  · rw [hz, smul_add]
  · rw [ht]; congr 1; nlinarith only [hte]
  · rw [hs]; congr 1; nlinarith only [hsf]
  · have hn : ‖W.center - A‖ ^ 2 = 2 * U ^ 2 * (1 + q) := by
      rw [← real_inner_self_eq_norm_sq, hz]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hee, hff, hq, hfe, starRingEnd_apply, star_trivial]
      ring
    rw [← hte] at htr
    nlinarith only [hn, htr]
