import Mathlib

theorem LeanFlowProofs.PBAdvanced027Aux.normalize_pair
    (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B) :
    ∃ (a b : ℝ) (v : EuclideanSpace ℝ (Fin 2)),
      (a ≠ 0 ∨ b ≠ 0) ∧
      (0 : EuclideanSpace ℝ (Fin 2)) =
        a • A - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-A 1, A 0]) + v ∧
      ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![(1 : ℝ), 0]) =
        a • B - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-B 1, B 0]) + v := by 
  let L : ℝ := (B 0 - A 0)^2 + (B 1 - A 1)^2
  have hL : L ≠ 0 := by
    intro h
    have hx : B 0 = A 0 := by
      dsimp [L] at h
      nlinarith [sq_nonneg (B 1 - A 1)]
    have hy : B 1 = A 1 := by
      dsimp [L] at h
      nlinarith [sq_nonneg (B 0 - A 0)]
    apply hAB
    ext i
    fin_cases i <;> simp_all
  let a := (B 0 - A 0) / L
  let b := (B 1 - A 1) / L
  refine ⟨a, b, -(a • A - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-A 1, A 0])), ?_, ?_, ?_⟩
  · by_contra h
    push_neg at h
    have hx : B 0 - A 0 = 0 := (div_eq_zero_iff.mp h.1).resolve_right hL
    have hy : B 1 - A 1 = 0 := (div_eq_zero_iff.mp h.2).resolve_right hL
    apply hL
    simp [L, hx, hy]
  · simp
  · ext i
    fin_cases i <;> simp [a, b]
    all_goals field_simp
    all_goals dsimp [L]
    all_goals ring
