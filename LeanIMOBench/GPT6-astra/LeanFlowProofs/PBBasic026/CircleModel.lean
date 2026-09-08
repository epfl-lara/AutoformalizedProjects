import Mathlib

theorem LeanFlowProofs.PBBasic026_circle_model
    (S W : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (X u v : EuclideanSpace ℝ (Fin 2)) (m n : ℝ)
    (hr : 0 < S.radius)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0)
    (hm : 0 < m) (hn : 0 < n)
    (hB : S.center + S.radius • ((-m) • u - v) ∈ W)
    (hC : S.center + S.radius • (n • u - v) ∈ W)
    (ht : S.IsIntTangentAt W X) :
    let k := m * n
    let t := n - m
    let V := t ^ 2 + k ^ 2
    X = S.center + S.radius •
      ((-2 * k * t / V) • u + ((k ^ 2 - t ^ 2) / V) • v) := by 
  classical
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  have hon : Orthonormal ℝ ![u, v] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu, hv, huv, hvu]
  let b := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)).ge
  have frame (z : EuclideanSpace ℝ (Fin 2)) :
      z = (inner ℝ u z) • u + (inner ℝ v z) • v := by
    simpa [b, Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply] using (b.sum_repr z).symm
  let r := S.radius
  let a := inner ℝ u (W.center - S.center)
  let c := inner ℝ v (W.center - S.center)
  let d := dist S.center W.center
  have hw : W.center = S.center + (a • u + c • v) := by
    have := frame (W.center - S.center)
    dsimp [a, c]
    exact (sub_eq_iff_eq_add.mp this).trans (add_comm _ _)
  have norm_frame (x y : ℝ) : ‖x • u + y • v‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      huu, hvv, huv, hvu]
    ring
  have dist_frame (x y z t : ℝ) :
      dist (S.center + (x • u + y • v)) (S.center + (z • u + t • v)) ^ 2 =
        (x-z)^2 + (y-t)^2 := by
    rw [dist_eq_norm]
    have he : S.center + (x • u + y • v) - (S.center + (z • u + t • v)) =
        (x-z) • u + (y-t) • v := by module
    rw [he, norm_frame]
  have hd : d ^ 2 = a ^ 2 + c ^ 2 := by
    dsimp [d]
    rw [hw]
    simpa using dist_frame 0 0 a c
  have hR : W.radius = d + r := by
    have := ht.isIntTangent.dist_center
    dsimp [d, r]
    linarith
  have hb : (-r*m-a)^2 + (-r-c)^2 = (d+r)^2 := by
    have := congrArg (fun x : ℝ => x^2) (show dist (S.center + S.radius • ((-m) • u - v)) W.center = W.radius from hB)
    rw [hw, hR] at this
    have he : S.center + S.radius • ((-m) • u - v) =
        S.center + ((-r*m) • u + (-r) • v) := by dsimp [r]; module
    rw [he, dist_frame] at this
    exact this
  have hc : (r*n-a)^2 + (-r-c)^2 = (d+r)^2 := by
    have := congrArg (fun x : ℝ => x^2) (show dist (S.center + S.radius • (n • u - v)) W.center = W.radius from hC)
    rw [hw, hR] at this
    have he : S.center + S.radius • (n • u - v) =
        S.center + ((r*n) • u + (-r) • v) := by dsimp [r]; module
    rw [he, dist_frame] at this
    exact this
  have hr' : 0 < r := hr
  have ha : 2*a = r*(n-m) := by
    have he : r*(m+n)*(2*a-r*(n-m)) = 0 := by nlinarith [hb, hc]
    have hp : r*(m+n) ≠ 0 := ne_of_gt (mul_pos hr' (add_pos hm hn))
    have := (mul_eq_zero.mp he).resolve_left hp
    linarith
  have hcd : 2*c = 2*d-r*(m*n) := by
    have he : r*(m+n)*(2*c-2*d+r*(m*n)) = 0 := by
      nlinarith [hb, hc, hd, mul_nonneg (le_of_lt hm) (le_of_lt hn)]
    have hp : r*(m+n) ≠ 0 := ne_of_gt (mul_pos hr' (add_pos hm hn))
    have := (mul_eq_zero.mp he).resolve_left hp
    linarith
  let k := m*n
  let t := n-m
  let V := t^2+k^2
  have hk : 0 < k := mul_pos hm hn
  have hV : 0 < V := add_pos_of_nonneg_of_pos (sq_nonneg t) (sq_pos_of_pos hk)
  have ha' : 2*a = r*t := ha
  have hc' : 2*c = 2*d-r*k := hcd
  have hd' : 4*k*d = r*V := by
    have he : r*(4*k*d-r*V) = 0 := by
      dsimp [V]
      nlinarith only [hd,
        congrArg (fun x : ℝ => x^2) ha', congrArg (fun x : ℝ => x^2) hc']
    have := (mul_eq_zero.mp he).resolve_left (ne_of_gt hr')
    linarith
  let p := inner ℝ u (X-S.center)
  let q := inner ℝ v (X-S.center)
  have hx : X = S.center + (p • u + q • v) := by
    exact (sub_eq_iff_eq_add.mp (frame (X-S.center))).trans (add_comm _ _)
  have hpx : p^2+q^2 = r^2 := by
    have he := congrArg (fun x : ℝ => x^2) (show dist X S.center = r from ht.mem_left)
    rw [hx] at he
    have hf := dist_frame p q 0 0
    simp only [zero_smul, add_zero, sub_zero] at hf
    exact hf.symm.trans he
  have hqx : (p-a)^2+(q-c)^2 = (d+r)^2 := by
    have he := congrArg (fun x : ℝ => x^2) (show dist X W.center = W.radius from ht.mem_right)
    rw [hx, hw, hR, dist_frame] at he
    exact he
  have hi : p*a+q*c = -d*r := by nlinarith only [hpx, hqx, hd]
  have hz : (d*p+r*a)^2 + (d*q+r*c)^2 = 0 := by
    calc
      _ = d^2*(p^2+q^2) + r^2*(a^2+c^2) + 2*d*r*(p*a+q*c) := by ring
      _ = 0 := by rw [hpx, ← hd, hi]; ring
  have hp0 : d*p+r*a = 0 := by nlinarith only [hz, sq_nonneg (d*p+r*a), sq_nonneg (d*q+r*c)]
  have hq0 : d*q+r*c = 0 := by nlinarith only [hz, sq_nonneg (d*p+r*a), sq_nonneg (d*q+r*c)]
  have hp : p = r*(-2*k*t/V) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt hV)).2
    have he : r*(p*V+2*r*k*t) = 0 := by
      nlinarith only [congrArg (fun x : ℝ => x*p) hd',
        congrArg (fun x : ℝ => x*(2*r*k)) ha',
        congrArg (fun x : ℝ => x*(4*k)) hp0]
    have := (mul_eq_zero.mp he).resolve_left (ne_of_gt hr')
    linarith
  have hq : q = r*((k^2-t^2)/V) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt hV)).2
    have he : r*(q*V-r*(k^2-t^2)) = 0 := by
      dsimp [V] at hd' ⊢
      nlinarith only [congrArg (fun x : ℝ => x*q) hd',
        congrArg (fun x : ℝ => x*(2*r*k)) hc',
        congrArg (fun x : ℝ => x*(4*k)) hq0,
        congrArg (fun x : ℝ => x*r) hd']
    have := (mul_eq_zero.mp he).resolve_left (ne_of_gt hr')
    linarith
  change X = S.center + r • ((-2*k*t/V) • u + ((k^2-t^2)/V) • v)
  rw [hx, hp, hq]
  module

