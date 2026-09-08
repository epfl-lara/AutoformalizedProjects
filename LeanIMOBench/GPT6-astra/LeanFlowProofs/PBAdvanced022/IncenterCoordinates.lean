import Mathlib

theorem LeanFlowProofs.PB022.incenterCoordinates
    (A B C : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C])
    (F : AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
    (a u v : ℝ) (ha : 0 < a) (hv : 0 < v)
    (hB : (F B) 0 = 0 ∧ (F B) 1 = 0)
    (hC : (F C) 0 = a ∧ (F C) 1 = 0)
    (hA : (F A) 0 = u ∧ (F A) 1 = v) :
    let b : ℝ := dist A C;
    let c : ℝ := dist A B;
    let p : ℝ := a + b + c;
    (F (Affine.Simplex.incenter ⟨![A, B, C], tri⟩)) 0 = (a * u + a * c) / p ∧
    (F (Affine.Simplex.incenter ⟨![A, B, C], tri⟩)) 1 = a * v / p ∧
    (Affine.Simplex.insphere ⟨![A, B, C], tri⟩).radius = a * v / p := by set_option maxHeartbeats 1000000 in
  exact (by
  classical
  let t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 := ⟨![A, B, C], tri⟩
  let s := t.map F.toAffineIsometry.toAffineMap F.toAffineIsometry.injective
  have hp0 : s.points 0 = F A := rfl
  have hp1 : s.points 1 = F B := rfl
  have hp2 : s.points 2 = F C := rfl
  have hd (X Y : EuclideanSpace ℝ (Fin 2)) :
      dist X Y ^ 2 = (X 0 - Y 0)^2 + (X 1 - Y 1)^2 := by
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      PiLp.sub_apply, star_trivial]
    ring
  have hi (X Y : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ X Y = X 0 * Y 0 + X 1 * Y 1 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
    <;> ring
  have hb_sq : dist A C ^ 2 = (u-a)^2 + v^2 := by
    rw [← F.dist_map A C, hd]
    simp [hA.1, hA.2, hC.1, hC.2]
  have hc_sq : dist A B ^ 2 = u^2 + v^2 := by
    rw [← F.dist_map A B, hd]
    simp [hA.1, hA.2, hB.1, hB.2]
  have hb : 0 < dist A C := by
    have := dist_nonneg (x := A) (y := C)
    nlinarith [sq_pos_of_pos hv]
  have hc : 0 < dist A B := by
    have := dist_nonneg (x := A) (y := B)
    nlinarith [sq_pos_of_pos hv]
  have hsq (i : Fin 3) :
      (s.points i 0 - s.altitudeFoot i 0)^2 +
      (s.points i 1 - s.altitudeFoot i 1)^2 = s.height i ^ 2 := by
    exact (hd _ _).symm
  have he (i j : Fin 3) (hij : i ≠ j) :
      (s.points i 0 - s.points j 0) * (s.points i 0 - s.altitudeFoot i 0) +
      (s.points i 1 - s.points j 1) * (s.points i 1 - s.altitudeFoot i 1) =
      s.height i ^ 2 := by
    simpa only [hi, vsub_eq_sub, PiLp.sub_apply] using
      s.inner_vsub_vsub_altitudeFoot_eq_height_sq hij
  have h0 : s.height 0 = v := by
    have e1 := he 0 1 (by decide)
    have e2 := he 0 2 (by decide)
    have en := hsq 0
    simp only [hp0, hp1, hp2, hA.1, hA.2, hB.1, hB.2, hC.1, hC.2,
      sub_zero] at e1 e2 en
    have ex : u - s.altitudeFoot 0 0 = 0 := by nlinarith only [e1, e2, ha]
    rw [ex] at e1 en
    have hpos := s.height_pos 0
    have ey : v - s.altitudeFoot 0 1 = v := by
      have : (v - s.altitudeFoot 0 1) * ((v - s.altitudeFoot 0 1) - v) = 0 := by nlinarith only [e1, en]
      rcases mul_eq_zero.mp this with h | h
      · rw [h] at en
        nlinarith only [en, hpos]
      · linarith only [h]
    rw [ey] at en
    nlinarith only [en, hpos, hv]
  have scalar (H d w x y : ℝ) (hH : 0 < H) (hd : 0 < d)
      (ed : d^2 = w^2 + v^2) (en : x^2 + y^2 = H^2)
      (ex : a*x = H^2) (ey : v*y = w*x) : H = a*v/d := by
    have eqn : v^2 * H^2 = d^2 * x^2 := by
      calc
        _ = v^2 * (x^2 + y^2) := by rw [en]
        _ = v^2*x^2 + (v*y)^2 := by ring
        _ = v^2*x^2 + (w*x)^2 := by rw [ey]
        _ = d^2*x^2 := by rw [ed]; ring
    have eq2 : (a*v)^2 * H^2 = (d*H)^2 * H^2 := by
      calc
        _ = a^2*(v^2*H^2) := by ring
        _ = a^2*(d^2*x^2) := by rw [eqn]
        _ = d^2*(a*x)^2 := by ring
        _ = (d*H)^2*H^2 := by rw [ex]; ring
    have eq3 := mul_right_cancel₀ (pow_ne_zero 2 hH.ne') eq2
    have eq4 : d*H = a*v := by
      nlinarith only [eq3, mul_pos ha hv, mul_pos hd hH]
    apply (eq_div_iff hd.ne').2
    nlinarith only [eq4]
  have h1 : s.height 1 = a*v / dist A C := by
    have e1 := he 1 0 (by decide)
    have e2 := he 1 2 (by decide)
    have en := hsq 1
    simp only [hp0, hp1, hp2, hA.1, hA.2, hB.1, hB.2, hC.1, hC.2,
      sub_zero, zero_sub] at e1 e2 en
    refine scalar (s.height 1) (dist A C) (a-u)
      (s.altitudeFoot 1 0) (s.altitudeFoot 1 1) (s.height_pos 1) hb ?_ ?_ ?_ ?_
    · nlinarith only [hb_sq]
    · nlinarith only [en]
    · nlinarith only [e2]
    · nlinarith only [e1, e2]
  have h2 : s.height 2 = a*v / dist A B := by
    have e1 := he 2 0 (by decide)
    have e2 := he 2 1 (by decide)
    have en := hsq 2
    simp only [hp0, hp1, hp2, hA.1, hA.2, hB.1, hB.2, hC.1, hC.2,
      sub_zero, zero_sub] at e1 e2 en
    refine scalar (s.height 2) (dist A B) (-u)
      (a - s.altitudeFoot 2 0) (-s.altitudeFoot 2 1) (s.height_pos 2) hc
      (by simpa using hc_sq) en ?_ ?_
    · nlinarith only [e2]
    · nlinarith only [e1, e2]
  let p := a + dist A C + dist A B
  have hp : 0 < p := by dsimp [p]; positivity
  have hs : (∑ i, s.excenterWeightsUnnorm ∅ i) = p / (a*v) := by
    rw [Fin.sum_univ_three]
    simp only [Affine.Simplex.excenterWeightsUnnorm_empty_apply, h0, h1, h2]
    dsimp [p]
    field_simp
    <;> ring
  have hw0 : s.excenterWeights ∅ 0 = a/p := by
    rw [Affine.Simplex.excenterWeights, hs]
    simp only [Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply, h0]
    field_simp
  have hw1 : s.excenterWeights ∅ 1 = dist A C/p := by
    rw [Affine.Simplex.excenterWeights, hs]
    simp only [Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply, h1]
    field_simp
  have hw2 : s.excenterWeights ∅ 2 = dist A B/p := by
    rw [Affine.Simplex.excenterWeights, hs]
    simp only [Pi.smul_apply, smul_eq_mul,
      Affine.Simplex.excenterWeightsUnnorm_empty_apply, h2]
    field_simp
  have hcenter : s.incenter = (a/p) • F A + (dist A C/p) • F B + (dist A B/p) • F C := by
    rw [s.incenter_eq_affineCombination,
      Finset.affineCombination_eq_linear_combination _ _ _
        s.excenterExists_empty.sum_excenterWeights_eq_one]
    rw [Fin.sum_univ_three]
    simp only [hw0, hw1, hw2, hp0, hp1, hp2]
  have hradius : s.inradius = a*v/p := by
    rw [s.inradius_eq_abs_inv_sum, hs, inv_div, abs_of_pos (div_pos (mul_pos ha hv) hp)]
  change (F t.incenter) 0 = (a*u+a*dist A B)/p ∧
    (F t.incenter) 1 = a*v/p ∧ t.inradius = a*v/p
  have hmap : s.incenter = F t.incenter := t.incenter_map F.toAffineIsometry
  rw [← hmap, ← t.inradius_map F.toAffineIsometry]
  change s.incenter 0 = _ ∧ s.incenter 1 = _ ∧ s.inradius = _
  rw [hcenter, hradius]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hA.1, hA.2,
    hB.1, hB.2, hC.1, hC.2, mul_zero, add_zero, and_true]
  constructor <;> ring)

