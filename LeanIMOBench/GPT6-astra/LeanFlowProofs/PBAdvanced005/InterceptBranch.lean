import Mathlib

theorem LeanFlowProofs.PBAdvanced005.admissibleInterceptBranch
    (k p q t s : ℝ)
    (hk0 : 0 < k) (hk1 : k < 1)
    (hp : 0 < p) (hq : 0 < q)
    (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hF : t * s - t * q - s * p ≠ 0)
    (hT : p ^ 2 + q ^ 2 + 2 * k * p * q -
      t * (p + k * q) - s * (q + k * p) + k * t * s =
      k * |t * s - t * q - s * p|) :
    let H : ℝ := 2 * k;
    let R : ℝ := p ^ 2 + q ^ 2 + 2 * k * p * q;
    let P : ℝ := p + H * q;
    let Q : ℝ := q + H * p;
    let U : ℝ := Q - H * t;
    let V : ℝ := P - H * s;
    t * s - t * q - s * p < 0 ∧
      H * t * s - P * t - Q * s + R = 0 ∧
      0 < U ∧ 0 < V ∧ U * V = p * q := by 
  have hpq : 0 < p * q := mul_pos hp hq
  have amgm (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (ha : 0 < a) (hxy : a ^ 2 ≤ x * y) : 2 * a ≤ x + y := by
    by_contra hn
    have hh : 0 < (2 * a - (x + y)) * (2 * a + (x + y)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (x - y)]
  have hf : t * s - t * q - s * p < 0 := by
    by_contra hn
    have hfpos : 0 < t * s - t * q - s * p := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hF)
    rw [abs_of_pos hfpos] at hT
    have htp : p < t := by
      by_contra hh
      have := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hh)) hs
      have := mul_nonneg ht (le_of_lt hq)
      nlinarith
    have hsq : q < s := by
      by_contra hh
      have := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hh)) ht
      have := mul_nonneg hs (le_of_lt hp)
      nlinarith
    have he : p * (t - p) + q * (s - q) = 2 * k * (p * q) := by nlinarith [hT]
    have hm : p * q < (t - p) * (s - q) := by nlinarith
    have hm' := mul_le_mul_of_nonneg_left (le_of_lt hm) (le_of_lt hpq)
    have ha := amgm (p * (t - p)) (q * (s - q)) (p * q)
      (le_of_lt (mul_pos hp (sub_pos.mpr htp)))
      (le_of_lt (mul_pos hq (sub_pos.mpr hsq))) hpq (by nlinarith [hm'])
    have := mul_pos (sub_pos.mpr hk1) hpq
    nlinarith
  rw [abs_of_neg hf] at hT
  dsimp only
  have hl : 2 * k * t * s - (p + 2 * k * q) * t -
      (q + 2 * k * p) * s + (p ^ 2 + q ^ 2 + 2 * k * p * q) = 0 := by
    nlinarith [hT]
  let U := q + 2 * k * p - 2 * k * t
  let V := p + 2 * k * q - 2 * k * s
  have hmul := congrArg (fun x : ℝ => (2 * k) * x) hl
  have huv : U * V = p * q := by
    dsimp [U, V]
    nlinarith [hmul]
  have hid : (2 * k) ^ 2 * (t * s - t * q - s * p) =
      (2 - (2 * k) ^ 2) * p * q - p * U - q * V := by
    dsimp [U, V]
    nlinarith [hmul]
  have hu : 0 < U := by
    by_contra hn
    have hu0 : U < 0 := by
      have : U ≠ 0 := by intro h; rw [h, zero_mul] at huv; linarith
      exact lt_of_le_of_ne (le_of_not_gt hn) this
    have hv0 : V < 0 := by
      by_contra hn
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hu0) (le_of_not_gt hn)
      nlinarith [huv]
    have ha := amgm (-p * U) (-q * V) (p * q)
      (by nlinarith [mul_pos hp (neg_pos.mpr hu0)])
      (by nlinarith [mul_pos hq (neg_pos.mpr hv0)]) hpq
      (by nlinarith [congrArg (fun x : ℝ => x * (p * q)) huv])
    have hk : 0 < 4 - (2 * k) ^ 2 := by nlinarith
    have hpos := mul_pos hk hpq
    have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos (show 0 < 2 * k by linarith)) hf
    nlinarith [hid]
  have hv : 0 < V := by
    have hprod : 0 < U * V := by rw [huv]; exact hpq
    exact ((mul_pos_iff.mp hprod).resolve_right (by rintro ⟨h, _⟩; linarith)).2
  exact ⟨hf, hl, hu, hv, huv⟩
