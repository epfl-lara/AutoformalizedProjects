import Mathlib

theorem LeanFlowProofs.PBBasic030.discriminantSwap
    (b d e h t s : ℝ) :
    let q : ℝ := b + e - d
    let U : ℝ := b ^ 2 + h ^ 2
    let V : ℝ := q ^ 2 + h ^ 2
    let H : ℝ → ℝ → ℝ := fun z w =>
      (d + e - h * (z + w)) ^ 2 + (b * z + q * w) ^ 2
    (H t s - U * (1 + t ^ 2) - V * (1 + s ^ 2)) ^ 2 -
        4 * U * V * (1 + t ^ 2) * (1 + s ^ 2) =
      (H s t - U * (1 + s ^ 2) - V * (1 + t ^ 2)) ^ 2 -
        4 * U * V * (1 + s ^ 2) * (1 + t ^ 2) := by (dsimp; ring)
