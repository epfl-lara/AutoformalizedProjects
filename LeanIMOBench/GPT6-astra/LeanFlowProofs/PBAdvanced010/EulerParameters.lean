import Mathlib

theorem LeanFlowProofs.PBAdvanced010.eulerParameters
    (a b s t r w : ℝ)
    (hr : r = t * (1 - w))
    (hw : w = s * (1 - r)) :
    let n : ℝ := a ^ 2 + b ^ 2 - 1
    let L : ℝ := 3 - 3 * a ^ 2 - b ^ 2
    L * (a - (a + 1) * r + (1 - a) * w) -
        2 * a * b * (b * (1 - r - w)) + a * n = 0 →
      4 * a * n * s * t - (L + 3 * a * n) * s +
        (L - 3 * a * n) * t + 2 * a * n = 0 := by 
  dsimp
  intro h
  have hr' : (1 - s * t) * r = t * (1 - s) := by
    linear_combination hr - t * hw
  have hw' : (1 - s * t) * w = s * (1 - t) := by
    linear_combination hw - s * hr
  linear_combination
    -(1 - s * t) * h +
      (-(a + 1) * (3 - 3 * a ^ 2 - b ^ 2) + 2 * a * b ^ 2) * hr' +
      ((1 - a) * (3 - 3 * a ^ 2 - b ^ 2) + 2 * a * b ^ 2) * hw'
