import Mathlib

theorem LeanFlowProofs.PBBasic026_circumcenter_model
    (I O u v : EuclideanSpace ℝ (Fin 2)) (r m n : ℝ)
    (hr : 0 < r) (hm : 0 < m) (hn : 0 < n) (hprod : 1 < m * n)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    let k := m * n
    let t := n - m
    let U := t ^ 2 + (k + 1) ^ 2
    let rho := U / (4 * (k - 1))
    let A := I + r •
      ((-t / (k - 1)) • u + ((k + 1) / (k - 1)) • v)
    let B := I + r • ((-m) • u - v)
    let C := I + r • (n • u - v)
    dist O A = dist O B →
    dist O B = dist O C →
    O = I + r • ((t / 2) • u + (rho - (k + 1) / 2) • v) ∧
      dist O A = r * rho := by 
  classical
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have frame (w : EuclideanSpace ℝ (Fin 2))
      (hwu : inner ℝ w u = 0) (hwv : inner ℝ w v = 0) : w = 0 := by
    have hu' := huu
    have hv' := hvv
    have huv' := huv
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial] at hu' hv' huv' hwu hwv
    have hd : (u 0 * v 1 - u 1 * v 0)^2 = 1 := by
      nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0)]
    have hd' : u 0 * v 1 - u 1 * v 0 ≠ 0 := by intro h; rw [h] at hd; norm_num at hd
    have hw0 : w 0 = 0 := by
      apply (mul_eq_zero.mp (show w 0 * (u 0 * v 1 - u 1 * v 0) = 0 by
        linear_combination v 1 * hwu - u 1 * hwv)).resolve_right hd'
    have hw1 : w 1 = 0 := by
      apply (mul_eq_zero.mp (show w 1 * (u 0 * v 1 - u 1 * v 0) = 0 by
        linear_combination u 0 * hwv - v 0 * hwu)).resolve_right hd'
    ext i
    fin_cases i
    · simpa using hw0
    · simpa using hw1
  dsimp only
  intro hAB hBC
  let w := O - I
  let x := inner ℝ w u
  let y := inner ℝ w v
  let q := inner ℝ w w
  have hd (a b : ℝ) :
      dist O (I + r • (a • u + b • v)) ^ 2 =
        q - 2*r*(a*x+b*y) + r^2*(a^2+b^2) := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    have he : O - (I + r • (a • u + b • v)) = w - r • (a • u + b • v) := by dsimp [w]; module
    rw [he]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, huu, hvv, huv, hvu]
    dsimp [q, x, y]
    rw [real_inner_comm u w, real_inner_comm v w]
    ring
  have hB : (-m) • u - v = (-m) • u + (-1 : ℝ) • v := by module
  have hC : n • u - v = n • u + (-1 : ℝ) • v := by module
  have eAB := congrArg (fun z : ℝ => z^2) hAB
  have eBC := congrArg (fun z : ℝ => z^2) hBC
  rw [hB, hd, hd] at eAB
  rw [hB, hC, hd, hd] at eBC
  have hx : x = r * ((n-m)/2) := by
    have he : r * (m+n) * (2*x-r*(n-m)) = 0 := by nlinarith [eBC]
    have hp : r * (m+n) ≠ 0 := ne_of_gt (mul_pos hr (by linarith))
    have := (mul_eq_zero.mp he).resolve_left hp
    linarith
  have hk : m*n-1 ≠ 0 := ne_of_gt (by linarith)
  have hy : y = r * (((n-m)^2+(m*n+1)^2)/(4*(m*n-1)) - (m*n+1)/2) := by
    rw [hx] at eAB
    have hkn : n*m-1 ≠ 0 := by nlinarith
    field_simp [hk, hkn] at eAB ⊢
    apply (mul_left_cancel₀ (show r*m*n ≠ 0 by positivity))
    linear_combination -2 * eAB
  have hw : w = x • u + y • v := by
    apply sub_eq_zero.mp
    apply frame
    · simp [inner_sub_left, inner_add_left, real_inner_smul_left, hu, hvu, x]
    · simp [inner_sub_left, inner_add_left, real_inner_smul_left, huv, hv, y]
  have hq : q = x^2+y^2 := by
    dsimp only [q]
    rw [hw]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, huu, hvv, huv, hvu]
    ring
  constructor
  · have he : O = I + (x • u + y • v) := by rw [← hw]; dsimp [w]; module
    rw [he, hx, hy]
    module
  · rw [hAB]
    have hs : dist O (I + r • ((-m) • u - v)) ^ 2 =
        (r * (((n-m)^2+(m*n+1)^2)/(4*(m*n-1))))^2 := by
      rw [hB, hd, hq, hx, hy]
      have hkn : n*m-1 ≠ 0 := by nlinarith
      field_simp [hk, hkn]
      <;> ring
    have hp : 0 ≤ r * (((n-m)^2+(m*n+1)^2)/(4*(m*n-1))) := by
      apply mul_nonneg (le_of_lt hr)
      apply div_nonneg (by positivity)
      positivity
    exact (sq_eq_sq₀ dist_nonneg hp).mp hs

