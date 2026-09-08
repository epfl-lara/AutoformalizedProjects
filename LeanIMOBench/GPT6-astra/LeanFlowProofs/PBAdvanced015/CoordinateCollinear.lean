import Mathlib

theorem LeanFlowProofs.pb015_coordinate_collinear
    (p δ : ℝ) (hp : 4 < p)
    (X Y K : EuclideanSpace ℝ (Fin 2))
    (hX : X 0 = p * δ / (p - 1) ∧ X 1 = 2 * p / (p - 1))
    (hY : Y 0 = δ * (4 * p + 1) / (5 * p + 1) ∧
      Y 1 = -2 * p ^ 2 / (5 * p + 1))
    (hK : K 0 = δ ∧ K 1 = 0) :
    Collinear ℝ {X, Y, K} := by 
  have hp1 : p - 1 ≠ 0 := by linarith
  have hp5 : 5 * p + 1 ≠ 0 := by linarith
  have hid : Y = (-p * (p - 1) / (5 * p + 1)) • (X - K) +ᵥ K := by
    ext i
    fin_cases i
    · simp [hX.1, hY.1, hK.1]
      field_simp
      <;> ring
    · simp [hX.2, hY.2, hK.2]
      field_simp
      <;> ring
  apply (collinear_iff_of_mem (show K ∈ ({X, Y, K} : Set _) by simp)).2
  refine ⟨X - K, ?_⟩
  intro P hP
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨_, hid⟩
  · exact ⟨0, by simp⟩
