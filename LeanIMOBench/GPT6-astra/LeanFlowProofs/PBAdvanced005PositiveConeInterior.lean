import Mathlib

theorem LeanFlowProofs.PBAdvanced005.positiveConeInterior
    (u v : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < EuclideanGeometry.angle u 0 v)
    (hacute : EuclideanGeometry.angle u 0 v < Real.pi / 2)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (∀ t : ℝ, 0 ≤ t → p • u + q • v ≠ t • u) ∧
    (∀ t : ℝ, 0 ≤ t → p • u + q • v ≠ t • v) ∧
    EuclideanGeometry.angle u 0 (p • u + q • v) +
      EuclideanGeometry.angle (p • u + q • v) 0 v =
      EuclideanGeometry.angle u 0 v := by open InnerProductGeometry in
  simp only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero] at *
  let a := p • u + q • v
  let α := angle u v
  let β := angle u a
  let γ := angle a v
  let k := Real.cos α
  let r := ‖a‖
  have hk : inner ℝ u v = k := inner_eq_cos_angle_of_norm_eq_one hu hv
  have hk0 : 0 < k := Real.cos_pos_of_mem_Ioo ⟨by dsimp [α]; linarith [Real.pi_pos], hacute⟩
  have hαpi : α < Real.pi := by dsimp [α]; linarith [Real.pi_pos]
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hpos hαpi
  have huu : inner ℝ u u = 1 := by simp [real_inner_self_eq_norm_sq, hu]
  have hvv : inner ℝ v v = 1 := by simp [real_inner_self_eq_norm_sq, hv]
  have hvu : inner ℝ v u = k := by rw [real_inner_comm]; exact hk
  have hr2 : r ^ 2 = p ^ 2 + q ^ 2 + 2*k*p*q := by
    dsimp [r, a]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, huu, hvv, hk, hvu]
    ring
  have hr : 0 < r := by
    have : 0 ≤ r := norm_nonneg a
    nlinarith [mul_pos (mul_pos hk0 hp) hq, sq_pos_of_pos hp]
  have hb : Real.cos β * r = p + k*q := by
    have := cos_angle_mul_norm_mul_norm u a
    simpa [β, r, a, hu, inner_add_right, real_inner_smul_right, huu, hk, mul_comm] using this
  have hc : Real.cos γ * r = q + k*p := by
    have := cos_angle_mul_norm_mul_norm a v
    simpa [γ, r, a, hv, inner_add_left, real_inner_smul_left, hvv, hk, mul_comm, add_comm] using this
  have hb0 : 0 < Real.cos β := by nlinarith [mul_pos hk0 hq]
  have hc0 : 0 < Real.cos γ := by nlinarith [mul_pos hk0 hp]
  have hbnn : 0 ≤ β := angle_nonneg _ _
  have hcnn : 0 ≤ γ := angle_nonneg _ _
  have hbpi : β ≤ Real.pi := angle_le_pi _ _
  have hcpi : γ ≤ Real.pi := angle_le_pi _ _
  have hbacute : β < Real.pi / 2 := by
    by_contra h
    have := Real.strictAntiOn_cos.antitoneOn ⟨by positivity, by linarith [Real.pi_pos]⟩ ⟨hbnn, hbpi⟩ (le_of_not_gt h)
    rw [Real.cos_pi_div_two] at this
    linarith
  have hcacute : γ < Real.pi / 2 := by
    by_contra h
    have := Real.strictAntiOn_cos.antitoneOn ⟨by positivity, by linarith [Real.pi_pos]⟩ ⟨hcnn, hcpi⟩ (le_of_not_gt h)
    rw [Real.cos_pi_div_two] at this
    linarith
  have sine_calc (b c d : ℝ) (hbcos : Real.cos b * r = c + k*d)
      (hnorm : r^2 = c^2+d^2+2*k*c*d) (hd : 0 < d)
      (hsb : 0 ≤ Real.sin b) : Real.sin b * r = d * Real.sin α := by
    have h1 := Real.sin_sq_add_cos_sq b
    have h2 := Real.sin_sq_add_cos_sq α
    have he : (Real.sin b * r)^2 = (d * Real.sin α)^2 := by
      calc
        _ = r^2 - (Real.cos b * r)^2 := by
          nlinarith only [congrArg (fun x : ℝ => x * r^2) h1]
        _ = (d * Real.sin α)^2 := by
          rw [hbcos, hnorm]
          dsimp [k]
          nlinarith only [congrArg (fun x : ℝ => x * d^2) h2]
    exact (sq_eq_sq₀ (mul_nonneg hsb hr.le) (mul_nonneg hd.le hs.le)).mp he
  have hsb : Real.sin β * r = q * Real.sin α := sine_calc β p q hb hr2 hq (sin_angle_nonneg _ _)
  have hsc : Real.sin γ * r = p * Real.sin α := sine_calc γ q p hc (by nlinarith [hr2]) hp (sin_angle_nonneg _ _)
  have hsbpos : 0 < Real.sin β := by nlinarith [mul_pos hq hs]
  have hscpos : 0 < Real.sin γ := by nlinarith [mul_pos hp hs]
  have hadd : β + γ = α := by
    apply Real.injOn_cos ⟨by positivity, by linarith⟩ ⟨hpos.le, hαpi.le⟩
    rw [Real.cos_add]
    apply (mul_right_cancel₀ (ne_of_gt (sq_pos_of_pos hr)))
    calc
      _ = (p+k*q)*(q+k*p) - (q*Real.sin α)*(p*Real.sin α) := by
        calc
          _ = (Real.cos β*r)*(Real.cos γ*r) - (Real.sin β*r)*(Real.sin γ*r) := by ring
          _ = _ := by rw [hb, hc, hsb, hsc]
      _ = Real.cos α * r^2 := by
        rw [hr2]
        dsimp [k]
        nlinarith only [congrArg (fun x : ℝ => x * (p*q)) (Real.sin_sq_add_cos_sq α)]
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  refine ⟨?_, ?_, hadd⟩
  · intro t ht he
    change a = t • u at he
    rcases eq_or_lt_of_le ht with h | h
    · have : r = 0 := by simp [r, he, ← h]
      linarith
    · have : β = 0 := by simp [β, he, angle_smul_right_of_pos _ _ h, angle_self hu0]
      simp [this] at hsbpos
  · intro t ht he
    change a = t • v at he
    rcases eq_or_lt_of_le ht with h | h
    · have : r = 0 := by simp [r, he, ← h]
      linarith
    · have : γ = 0 := by simp [γ, he, angle_smul_left_of_pos _ _ h, angle_self hv0]
      simp [this] at hscpos
