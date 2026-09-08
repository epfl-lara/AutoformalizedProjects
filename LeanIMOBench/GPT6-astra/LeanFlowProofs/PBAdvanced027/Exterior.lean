import LeanFlowProofs.PBAdvanced027.Normalization
import LeanFlowProofs.PBAdvanced027.Similarity
import Mathlib

theorem LeanFlowProofs.PBAdvanced027Aux.exterior_iff
    (A B C : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B) :
    (dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) ↔
      ∃ R : EuclideanSpace ℝ (Fin 2),
        (1 : ℝ) <
          dist (0 : EuclideanSpace ℝ (Fin 2)) R ^ 2 +
          dist ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![(1 : ℝ), 0]) R ^ 2 ∧
        ∃ (a b : ℝ) (v : EuclideanSpace ℝ (Fin 2)),
          (a ≠ 0 ∨ b ≠ 0) ∧
          (0 : EuclideanSpace ℝ (Fin 2)) =
            a • A - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-A 1, A 0]) + v ∧
          ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![(1 : ℝ), 0]) =
            a • B - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-B 1, B 0]) + v ∧
          R = a • C - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-C 1, C 0]) + v := by 
  let U : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![(1 : ℝ), 0]
  have hunit : dist (0 : EuclideanSpace ℝ (Fin 2)) U ^ 2 = 1 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [U, Fin.sum_univ_two]
  have transfer (a b : ℝ) (v R : EuclideanSpace ℝ (Fin 2))
      (hab : a ≠ 0 ∨ b ≠ 0)
      (hA : (0 : EuclideanSpace ℝ (Fin 2)) = a • A - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-A 1, A 0]) + v)
      (hB : U = a • B - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-B 1, B 0]) + v)
      (hC : R = a • C - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-C 1, C 0]) + v) :
      (dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2) ↔
        1 < dist (0 : EuclideanSpace ℝ (Fin 2)) R ^ 2 + dist U R ^ 2 := by
    have hp : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with ha | hb
      · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
      · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
    have h1 := similarity_dist_sq a b v A B
    have h2 := similarity_dist_sq a b v A C
    have h3 := similarity_dist_sq a b v B C
    rw [← hA, ← hB, hunit] at h1
    rw [← hA, ← hC] at h2
    rw [← hB, ← hC] at h3
    rw [h2, h3, ← mul_add, h1]
    exact (mul_lt_mul_iff_right₀ hp).symm
  constructor
  · intro h
    obtain ⟨a, b, v, hab, hA, hB⟩ := normalize_pair A B hAB
    let R := a • C - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-C 1, C 0]) + v
    exact ⟨R, (transfer a b v R hab hA hB rfl).mp h, a, b, v, hab, hA, hB, rfl⟩
  · rintro ⟨R, h, a, b, v, hab, hA, hB, hC⟩
    exact (transfer a b v R hab hA hB hC).mpr h
