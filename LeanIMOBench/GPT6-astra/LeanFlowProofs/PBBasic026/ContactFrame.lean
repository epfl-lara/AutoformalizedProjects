import Mathlib

theorem LeanFlowProofs.PBBasic026_contact_frame
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2) :
    let I := Affine.Simplex.incenter s
    let r := Affine.Simplex.inradius s
    let D := Affine.Simplex.touchpoint s ∅ 0
    0 < r ∧
      ∃ (u v : EuclideanSpace ℝ (Fin 2)) (m n : ℝ),
        ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℝ u v = 0 ∧
        0 < m ∧ 0 < n ∧
        D = I - r • v ∧
        s.points 1 = I + r • ((-m) • u - v) ∧
        s.points 2 = I + r • (n • u - v) ∧
        0 < inner ℝ (s.points 0 - I + r • v) v := by 
  dsimp only
  let I := s.incenter
  let r := s.inradius
  let D := s.touchpoint ∅ 0
  let B := s.points 1
  let C := s.points 2
  have hr : 0 < r := s.inradius_pos
  have hnorm : ‖I - D‖ = r := by simpa [I, D, dist_eq_norm] using s.dist_incenter 0
  have hBC : B ≠ C := s.independent.injective.ne (by decide)
  have hL : 0 < ‖C - B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hBC.symm)
  have hbt : Sbtw ℝ B D C := Affine.Triangle.sbtw_touchpoint_empty s (by decide) (by decide) (by decide)
  obtain ⟨⟨t, ht, hD⟩, hDB, hDC⟩ := hbt
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro he
    subst t
    simp only [AffineMap.lineMap_apply_zero] at hD
    exact hDB hD.symm)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    simp only [AffineMap.lineMap_apply_one] at hD
    exact hDC hD.symm)
  have hD' : t • (C - B) + B = D := hD
  let u := ‖C - B‖⁻¹ • (C - B)
  let v := r⁻¹ • (I - D)
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, abs_of_pos hL, hL.ne']
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, abs_of_pos hr, hnorm, hr.ne']
  have hrv : r • v = I - D := by simp [v, smul_smul, hr.ne']
  have hLu : ‖C - B‖ • u = C - B := by simp [u, smul_smul, hL.ne']
  have hface : affineSpan ℝ (Set.range (s.faceOpposite 0).points) = affineSpan ℝ {B,C} := by
    congr 1
    simp only [Affine.Simplex.range_faceOpposite_points]
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all [B, C]
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  have htan := s.isTangentAt_insphere_touchpoint 0
  rw [hface] at htan
  have hBmem : B ∈ affineSpan ℝ {B,C} := subset_affineSpan ℝ _ (by simp)
  have hCmem : C ∈ affineSpan ℝ {B,C} := subset_affineSpan ℝ _ (by simp)
  have hBorth : inner ℝ (B-D) (I-D) = 0 := by
    have h := htan.inner_left_eq_zero_of_mem hBmem
    change inner ℝ (B-D) (D-I) = 0 at h
    rw [show D-I = -(I-D) by abel, inner_neg_right, neg_eq_zero] at h
    exact h
  have hCorth : inner ℝ (C-D) (I-D) = 0 := by
    have h := htan.inner_left_eq_zero_of_mem hCmem
    change inner ℝ (C-D) (D-I) = 0 at h
    rw [show D-I = -(I-D) by abel, inner_neg_right, neg_eq_zero] at h
    exact h
  have huv : inner ℝ u v = 0 := by
    have h : inner ℝ (C-B) (I-D) = 0 := by
      rw [show C-B = (C-D)-(B-D) by abel, inner_sub_left, hBorth, hCorth, sub_self]
    simp [u, v, inner_smul_left, inner_smul_right, h]
  refine ⟨hr, u, v, t * ‖C-B‖ / r, (1-t) * ‖C-B‖ / r, hu, hv, huv,
    div_pos (mul_pos ht0 hL) hr, div_pos (mul_pos (sub_pos.mpr ht1) hL) hr, ?_, ?_, ?_, ?_⟩
  · rw [hrv]; abel
  · rw [smul_sub, hrv, smul_smul]
    have hc : r * -(t * ‖C-B‖ / r) = -t * ‖C-B‖ := by field_simp
    rw [hc, ← smul_smul, hLu]
    rw [← hD']
    module
  · rw [smul_sub, hrv, smul_smul]
    have hc : r * ((1-t) * ‖C-B‖ / r) = (1-t) * ‖C-B‖ := by field_simp
    rw [hc, ← smul_smul, hLu]
    rw [← hD']
    module
  · have hs := s.sSameSide_incenter_point 0
    rw [hface] at hs
    obtain ⟨p, hp, q, hq, hpq⟩ := hs.wSameSide
    have hp0 : I - p ≠ 0 := by
      intro h
      apply hs.left_notMem
      change I ∈ affineSpan ℝ {B,C}
      rw [sub_eq_zero.mp h]
      exact hp
    have hq0 : s.points 0 - q ≠ 0 := by
      intro h
      exact hs.right_notMem (sub_eq_zero.mp h ▸ hq)
    obtain ⟨a, b, ha, hb, hab⟩ := hpq.exists_pos hp0 hq0
    have horth (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ affineSpan ℝ {B,C}) :
        inner ℝ (x-D) (I-D) = 0 := by
      have h := htan.inner_left_eq_zero_of_mem hx
      change inner ℝ (x-D) (D-I) = 0 at h
      rw [show D-I = -(I-D) by abel, inner_neg_right, neg_eq_zero] at h
      exact h
    have hip : inner ℝ (I-p) (I-D) = r^2 := by
      rw [show I-p = (I-D)-(p-D) by abel, inner_sub_left, horth p hp,
        sub_zero, real_inner_self_eq_norm_sq, hnorm]
    have haq : inner ℝ (s.points 0-q) (I-D) = inner ℝ (s.points 0-D) (I-D) := by
      rw [show s.points 0-q = (s.points 0-D)-(q-D) by abel, inner_sub_left,
        horth q hq, sub_zero]
    have he := congrArg (fun z => inner ℝ z (I-D)) hab
    change inner ℝ (a • (I-p)) (I-D) = inner ℝ (b • (s.points 0-q)) (I-D) at he
    rw [real_inner_smul_left, real_inner_smul_left, hip, haq] at he
    have hpos : 0 < inner ℝ (s.points 0-D) (I-D) := by
      exact (mul_pos_iff_of_pos_left hb).mp (he ▸ mul_pos ha (sq_pos_of_pos hr))
    change 0 < inner ℝ (s.points 0-I+r • v) v
    rw [hrv, show s.points 0-I+(I-D) = s.points 0-D by abel]
    simpa only [v, real_inner_smul_right] using mul_pos (inv_pos.mpr hr) hpos
