import Mathlib

theorem LeanFlowProofs.PBBasic026_apex_model
    (S : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (A u v : EuclideanSpace ℝ (Fin 2)) (m n : ℝ)
    (hr : 0 < S.radius)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hm : 0 < m) (hn : 0 < n)
    (hA : 0 < inner ℝ (A - S.center + S.radius • v) v)
    (hAB : S.IsTangent
      (affineSpan ℝ {A, S.center + S.radius • ((-m) • u - v)}))
    (hAC : S.IsTangent
      (affineSpan ℝ {A, S.center + S.radius • (n • u - v)})) :
    let k := m * n
    let t := n - m
    1 < k ∧
      A = S.center + S.radius •
        ((-t / (k - 1)) • u + ((k + 1) / (k - 1)) • v) := by classical
  have huu : inner ℝ u u = 1 := by simp [real_inner_self_eq_norm_sq, hu]
  have hvv : inner ℝ v v = 1 := by simp [real_inner_self_eq_norm_sq, hv]
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have hon : Orthonormal ℝ ![u, v] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu, hv, huv, hvu]
  let b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    OrthonormalBasis.mk hon (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have frame (w : EuclideanSpace ℝ (Fin 2)) :
      w = (inner ℝ w u) • u + (inner ℝ w v) • v := by
    simpa [b, OrthonormalBasis.coe_mk, Fin.sum_univ_two, real_inner_comm] using
      (b.sum_repr' w).symm
  have normframe (w : EuclideanSpace ℝ (Fin 2)) :
      (inner ℝ w u)^2 + (inner ℝ w v)^2 = ‖w‖^2 := by
    simpa [b, OrthonormalBasis.coe_mk, Fin.sum_univ_two] using b.sum_sq_inner_left w
  have height : 0 < inner ℝ (A - S.center) v + S.radius := by
    simpa [inner_add_left, inner_smul_left, hv] using hA
  have tangent (q : ℝ) (hq : S.IsTangent
      (affineSpan ℝ {A, S.center + S.radius • (q • u - v)})) :
      2*q*inner ℝ (A-S.center) u + (q^2-1)*inner ℝ (A-S.center) v =
        S.radius*(q^2+1) := by
    obtain ⟨p, hp⟩ := hq
    have hpA := hp.inner_left_eq_zero_of_mem (left_mem_affineSpan_pair ℝ A _)
    have hpB := hp.inner_left_eq_zero_of_mem (right_mem_affineSpan_pair ℝ A _)
    change inner ℝ (A-p) (p-S.center) = 0 at hpA
    change inner ℝ (S.center + S.radius • (q • u - v) - p) (p-S.center) = 0 at hpB
    have hpn : ‖p-S.center‖ = S.radius := by
      have hs : dist p S.center = S.radius := hp.mem_sphere
      simpa [dist_eq_norm] using hs
    have hunit := normframe (p-S.center)
    rw [hpn] at hunit
    have hself : inner ℝ (p-S.center) (p-S.center) = S.radius^2 := by
      rw [real_inner_self_eq_norm_sq, hpn]
    have hpa : inner ℝ (A-S.center) (p-S.center) = S.radius^2 := by
      have he : A - p = (A-S.center) - (p-S.center) := by simp
      rw [he, inner_sub_left, hself] at hpA
      linarith
    have hpb : q * inner ℝ (p-S.center) u - inner ℝ (p-S.center) v = S.radius := by
      have he : S.center + S.radius • (q • u - v) - p =
          S.radius • (q • u - v) - (p-S.center) := by abel
      rw [he, inner_sub_left, inner_smul_left, inner_sub_left, inner_smul_left,
        hself, real_inner_comm (p-S.center) u, real_inner_comm (p-S.center) v] at hpB
      simp only [starRingEnd_apply, star_trivial] at hpB
      nlinarith
    rw [frame (p-S.center), inner_add_right, inner_smul_right, inner_smul_right] at hpa
    have hpx : inner ℝ (p-S.center) u ≠ 0 := by
      intro hz
      have hy : inner ℝ (p-S.center) v = -S.radius := by rw [hz] at hpb; linarith
      rw [hz, hy] at hpa
      nlinarith [mul_pos hr height]
    have normal : (q^2+1)*inner ℝ (p-S.center) u = 2*q*S.radius := by
      apply (mul_left_cancel₀ hpx)
      linear_combination hunit +
        (q * inner ℝ (p-S.center) u + inner ℝ (p-S.center) v - S.radius) * hpb
    have normaly : (q^2+1)*inner ℝ (p-S.center) v = (q^2-1)*S.radius := by
      linear_combination q * normal - (q^2+1) * hpb
    apply (mul_left_cancel₀ (ne_of_gt hr))
    linear_combination (q^2+1)*hpa - inner ℝ (A-S.center) u * normal -
      inner ℝ (A-S.center) v * normaly
  have e₁ := tangent (-m) hAB
  have e₂ := tangent n hAC
  have ey : (m*n-1)*inner ℝ (A-S.center) v = S.radius*(m*n+1) := by
    apply mul_left_cancel₀ (ne_of_gt (add_pos hm hn))
    linear_combination n * e₁ + m * e₂
  have height_eq : (m*n-1)*(inner ℝ (A-S.center) v + S.radius) =
      2*S.radius*(m*n) := by linear_combination ey
  have hk : 1 < m*n := by
    have hp : 0 < 2*S.radius*(m*n) := mul_pos (mul_pos (by norm_num) hr) (mul_pos hm hn)
    have : 0 < m*n-1 := (mul_pos_iff_of_pos_right height).mp (height_eq ▸ hp)
    linarith
  have hd : m*n-1 ≠ 0 := ne_of_gt (sub_pos.mpr hk)
  have ex : (m*n-1)*inner ℝ (A-S.center) u = S.radius*(m-n) := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos (by norm_num : (0:ℝ)<2) hn))
    linear_combination (m*n-1)*e₂ - (n^2-1)*ey
  have ex' : inner ℝ (A-S.center) u = S.radius * (-(n-m)/(m*n-1)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hd).mpr
    linear_combination ex
  have ey' : inner ℝ (A-S.center) v = S.radius * ((m*n+1)/(m*n-1)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff hd).mpr
    nlinarith [ey]
  refine ⟨hk, ?_⟩
  have ha := frame (A-S.center)
  rw [ex', ey'] at ha
  rw [smul_add, ← mul_smul, ← mul_smul]
  exact (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)
