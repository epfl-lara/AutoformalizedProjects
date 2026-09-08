import Mathlib

theorem LeanFlowProofs.PB022.negativeArcPoint
    (A B C K : EuclideanSpace ℝ (Fin 2))
    (Ω : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (F : AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
    (a k : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hB : (F B) 0 = 0 ∧ (F B) 1 = 0)
    (hC : (F C) 0 = a ∧ (F C) 1 = 0)
    (hA_up : 0 < (F A) 1)
    (hA_eq : ((F A) 0) ^ 2 + ((F A) 1) ^ 2 - a * (F A) 0 +
      (k - a ^ 2 / (4 * k)) * (F A) 1 = 0)
    (hA_mem : A ∈ Ω) (hB_mem : B ∈ Ω) (hC_mem : C ∈ Ω)
    (hK_mem : K ∈ Ω)
    (hK_dist : dist K B = dist K C)
    (hK_side : (affineSpan ℝ {B, C}).SOppSide A K) :
    (F K) 0 = a / 2 ∧ (F K) 1 = -k := by set_option maxHeartbeats 800000 in
  have hd (P Q : EuclideanSpace ℝ (Fin 2)) : dist P Q ^ 2 =
      ((F P) 0 - (F Q) 0)^2 + ((F P) 1 - (F Q) 1)^2 := by
    rw [← F.dist_map P Q, EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
  have hs (P : EuclideanSpace ℝ (Fin 2)) (hP : P ∈ Ω) :
      ((F P) 0 - (F Ω.center) 0)^2 + ((F P) 1 - (F Ω.center) 1)^2 = Ω.radius^2 := by
    rw [← hd]
    change dist P Ω.center = Ω.radius at hP
    rw [hP]
  have hb := hs B hB_mem
  have hc := hs C hC_mem
  have haa := hs A hA_mem
  have hkk := hs K hK_mem
  simp only [hB.1, hB.2, hC.1, hC.2] at hb hc
  have hox : (F Ω.center) 0 = a / 2 := by
    nlinarith
  have hoy : 2 * (F Ω.center) 1 = -(k - a^2 / (4*k)) := by
    rw [hox] at haa hb
    nlinarith
  have heq : (F K) 0 ^ 2 + (F K) 1 ^ 2 - a * (F K) 0 +
      (k - a^2/(4*k)) * (F K) 1 = 0 := by
    rw [hox] at hb hkk
    nlinarith only [hb, hkk, congrArg (fun t : ℝ => t * (F K) 1) hoy]
  have hx : (F K) 0 = a / 2 := by
    have he := congrArg (fun t : ℝ => t^2) hK_dist
    rw [hd, hd] at he
    simp only [hB.1, hB.2, hC.1, hC.2] at he
    nlinarith only [he, ha]
  have hline (P : EuclideanSpace ℝ (Fin 2)) (hP : P ∈ affineSpan ℝ {B,C}) :
      (F P) 1 = 0 := by
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hP with ⟨t, rfl⟩
    change (F.toAffineEquiv.toAffineMap (AffineMap.lineMap B C t)) 1 = 0
    rw [AffineMap.apply_lineMap]
    simp [AffineMap.lineMap_apply, hB.2, hC.2]
  have hy : (F K) 1 ≤ 0 := by
    rcases hK_side.wOppSide.map F.toAffineEquiv.toAffineMap with ⟨P, hP, Q, hQ, hr⟩
    rcases hP with ⟨P, hP, rfl⟩
    rcases hQ with ⟨Q, hQ, rfl⟩
    rcases hr with hz | hz | ⟨r, s, hr, hs, he⟩
    · have hz' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz
      simp [hline P hP] at hz'
      linarith
    · have hz' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz
      simp [hline Q hQ] at hz'
      linarith
    · have he' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) he
      simp [hline P hP, hline Q hQ] at he'
      nlinarith only [he', hr, hs, hA_up]
  refine ⟨hx, ?_⟩
  rw [hx] at heq
  have hpos : 0 < a^2 / (4*k) := div_pos (sq_pos_of_pos ha) (by positivity)
  have hfac : ((F K) 1 + k) * ((F K) 1 - a^2/(4*k)) = 0 := by
    have hdiv : a^2/(4*k) * k = a^2/4 := by field_simp [ne_of_gt hk]
    nlinarith only [heq, hdiv]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith
