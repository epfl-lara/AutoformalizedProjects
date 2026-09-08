import Mathlib

theorem LeanFlowProofs.PB009.cosphericalEquation
    (s : Set (EuclideanSpace ℝ (Fin 2)))
    (hs : EuclideanGeometry.Cospherical s) :
    ∃ u v w : ℝ, ∀ X : EuclideanSpace ℝ (Fin 2), X ∈ s →
      (X 0) ^ 2 + (X 1) ^ 2 - u * X 0 - v * X 1 + w = 0 := by 
  rcases hs with ⟨c, r, hr⟩
  refine ⟨2 * c 0, 2 * c 1, (c 0)^2 + (c 1)^2 - r^2, ?_⟩
  intro X hX
  have h := congrArg (fun t : ℝ => t^2) (hr X hX)
  rw [dist_eq_norm] at h
  rw [EuclideanSpace.norm_sq_eq] at h
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at h
  nlinarith
