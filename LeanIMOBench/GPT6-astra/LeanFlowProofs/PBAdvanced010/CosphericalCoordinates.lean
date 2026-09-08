import Mathlib

theorem LeanFlowProofs.PBAdvanced010.cosphericalCoordinateQuadratic
    (f : EuclideanSpace ℝ (Fin 2) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (hscale : ∀ U V : EuclideanSpace ℝ (Fin 2),
      dist (f U) (f V) = ρ * dist U V)
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    EuclideanGeometry.Cospherical S ↔
      ∃ α β γ : ℝ, ∀ P ∈ S,
        ((f P) 0) ^ 2 + ((f P) 1) ^ 2 +
          α * (f P) 0 + β * (f P) 1 + γ = 0 := by 
  have hd (U V : EuclideanSpace ℝ (Fin 2)) :
      dist U V ^ 2 = (U 0 - V 0)^2 + (U 1 - V 1)^2 := by
    simp [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold EuclideanGeometry.Cospherical
  constructor
  · rintro ⟨C, r, hr⟩
    refine ⟨-2 * (f C) 0, -2 * (f C) 1,
      (f C) 0 ^ 2 + (f C) 1 ^ 2 - (ρ * r)^2, ?_⟩
    intro P hP
    have hh := hd (f P) (f C)
    rw [hscale, hr P hP] at hh
    nlinarith [hh]
  · rintro ⟨α, β, γ, hq⟩
    let C : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-α/2, -β/2]
    by_cases hS : S.Nonempty
    · obtain ⟨P₀, hP₀⟩ := hS
      refine ⟨f.symm C, dist P₀ (f.symm C), ?_⟩
      intro P hP
      have h1 := hd (f P) C
      have h2 := hd (f P₀) C
      have q1 := hq P hP
      have q2 := hq P₀ hP₀
      have he : dist (f P) C ^ 2 = dist (f P₀) C ^ 2 := by
        dsimp [C] at h1 h2
        nlinarith
      have he' : dist (f P) C = dist (f P₀) C := by
        nlinarith [dist_nonneg (x := f P) (y := C), dist_nonneg (x := f P₀) (y := C)]
      have hs1 := hscale P (f.symm C)
      have hs2 := hscale P₀ (f.symm C)
      simp only [f.apply_symm_apply] at hs1 hs2
      nlinarith
    · refine ⟨0, 0, ?_⟩
      intro P hP
      exact (hS ⟨P, hP⟩).elim
