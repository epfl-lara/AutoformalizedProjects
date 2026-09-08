import Mathlib

theorem LeanFlowProofs.pbbasic025_segmentPlacement
    (X Y P : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hbetween : Sbtw ℝ X P Y) (hdist : dist Y P = a) :
    0 < dist X Y ∧
      P - X = (1 - a / dist X Y) • (Y - X) := by 
  have hne : X ≠ Y := by
    intro h
    subst Y
    exact hbetween.ne_left ((wbtw_self_iff ℝ).mp hbetween.wbtw)
  have hpos : 0 < dist X Y := dist_pos.mpr hne
  refine ⟨hpos, ?_⟩
  obtain ⟨t, ht, hp⟩ := hbetween.mem_image_Ioo
  have hd : a = (1 - t) * dist X Y := by
    rw [← hdist, ← hp]
    conv_lhs => lhs; rw [← AffineMap.lineMap_apply_one (k := ℝ) X Y]
    rw [dist_lineMap_lineMap, Real.dist_eq, abs_of_nonneg (by linarith [ht.2])]
  have ht' : 1 - a / dist X Y = t := by
    rw [hd, mul_div_cancel_right₀ _ (ne_of_gt hpos)]
    ring
  rw [ht', ← hp]
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
