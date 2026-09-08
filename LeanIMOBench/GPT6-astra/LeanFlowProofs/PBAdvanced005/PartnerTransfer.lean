import Mathlib

theorem LeanFlowProofs.PBAdvanced005.partnerInterceptTransfer
    (k p q t s : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1)
    (hp : 0 < p) (hq : 0 < q) :
    let H : ℝ := 2 * k;
    let R : ℝ := p ^ 2 + q ^ 2 + 2 * k * p * q;
    let P : ℝ := p + H * q;
    let Q : ℝ := q + H * p;
    let U : ℝ := Q - H * t;
    let V : ℝ := P - H * s;
    let r : ℝ := q / H;
    let w : ℝ := p / H;
    let G : ℝ := t * s - t * w - s * r;
    let T : ℝ := r ^ 2 + w ^ 2 + 2 * k * r * w -
      t * (r + k * w) - s * (w + k * r) + k * t * s;
    H * t * s - P * t - Q * s + R = 0 →
    0 < U →
    0 < V →
    U * V = p * q →
    G < 0 ∧
      T = (k - 1 / H) * G ∧
      T ^ 2 + (1 - k ^ 2) * G ^ 2 = G ^ 2 / H ^ 2 := by 
  intro H R P Q U V r w G T hloc hU hV hUV
  have hH : 0 < H := by dsimp [H]; positivity
  have hH0 : H ≠ 0 := ne_of_gt hH
  have hH2 : H < 2 := by dsimp [H]; linarith
  have hpq : 0 < p * q := mul_pos hp hq
  have hprod : (q * U) * (p * V) = (p * q) ^ 2 := by
    calc
      (q * U) * (p * V) = (p * q) * (U * V) := by ring
      _ = (p * q) ^ 2 := by rw [hUV]; ring
  have hsumpos : 0 < q * U + p * V := add_pos (mul_pos hq hU) (mul_pos hp hV)
  have hsum : 2 * (p * q) ≤ q * U + p * V := by
    nlinarith [sq_nonneg (q * U - p * V)]
  have hG : H * G = H * p * q - q * U - p * V := by
    dsimp [G, r, w, U, V, Q, P]
    field_simp
    dsimp [R, P, Q] at hloc
    nlinarith [hloc]
  have hGneg : G < 0 := by
    have : H * p * q < 2 * (p * q) := by nlinarith [mul_pos (sub_pos.mpr hH2) hpq]
    have : H * G < 0 := by linarith
    by_contra hn
    have hn' : 0 ≤ G := le_of_not_gt hn
    have := mul_nonneg (le_of_lt hH) hn'
    linarith
  have hT : T = (k - 1 / H) * G := by
    dsimp [T, r, w, G]
    field_simp
    dsimp [R, P, Q, H] at hloc ⊢
    nlinarith [hloc]
  refine ⟨hGneg, hT, ?_⟩
  rw [hT]
  dsimp [H]
  field_simp
  <;> ring

