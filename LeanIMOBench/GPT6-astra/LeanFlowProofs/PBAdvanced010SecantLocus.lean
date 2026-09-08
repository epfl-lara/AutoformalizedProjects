import Mathlib

theorem LeanFlowProofs.PBAdvanced010.secantLocus
    (a b e px py tx ty : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hpy : py ≠ 0)
    (hside : b * (px - 1) + (1 - a) * py = 0)
    (hP : px ^ 2 + py ^ 2 - a * px + e * py = 0)
    (hT : tx ^ 2 + ty ^ 2 - a * tx + e * ty = 0)
    (hcol : (a * px - 1) * ty - py * (a * tx - 1) = 0)
    (hne : (tx, ty) ≠ (px, py)) :
    a * b * (tx ^ 2 + ty ^ 2) + b * (a - 1) * tx +
      (1 - a ^ 2) * ty - b = 0 := by 
  let j : ℝ := 1 / a
  let u : ℝ := ty / py
  have haj : a * j = 1 := by dsimp [j]; field_simp
  have hy : ty = u * py := by dsimp [u]; field_simp
  have hx : tx = j + u * (px - j) := by
    apply (mul_left_cancel₀ (mul_ne_zero ha hpy))
    rw [hy] at hcol
    linear_combination -hcol + py * (u - 1) * haj
  have hu : u - 1 ≠ 0 := by
    intro h
    have he : u = 1 := by linarith
    apply hne
    apply Prod.ext
    · rw [hx, he]; ring
    · rw [hy, he]; ring
  rw [hx, hy] at hT ⊢
  have hf : (u - 1) * (((px - j) ^ 2 + py ^ 2) * u - (j ^ 2 - a * j)) = 0 := by
    linear_combination hT - u * hP
  have hf' : ((px - j) ^ 2 + py ^ 2) * u - (j ^ 2 - a * j) = 0 :=
    (mul_eq_zero.mp hf).resolve_left hu
  linear_combination a * b * u * hf' + u * (a + 1) * hside +
    b * (j + 1 + u * (2 * px - j - a - 1)) * haj

