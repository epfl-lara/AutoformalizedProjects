import Mathlib

theorem LeanFlowProofs.PBAdvanced027Aux.similarity_dist_sq
    (a b : ℝ) (v X Y : EuclideanSpace ℝ (Fin 2)) :
    dist
      (a • X - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-X 1, X 0]) + v)
      (a • Y - b • ((WithLp.equiv 2 (Fin 2 → ℝ)).symm ![-Y 1, Y 0]) + v) ^ 2 =
      (a ^ 2 + b ^ 2) * dist X Y ^ 2 := by 
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
  simp
  ring
