import Mathlib

theorem LeanFlowProofs.PB003.negativePowerCoaxialSecant
    (v : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (c : Fin 3 → ℝ)
    (J : EuclideanSpace ℝ (Fin 2))
    (hne : v 1 ≠ v 0)
    (hcol : ∃ t : ℝ, v 2 - v 0 = t • (v 1 - v 0))
    (hsame : ∀ i : Fin 3,
      ‖J‖ ^ 2 + inner ℝ (v i) J + c i =
        ‖J‖ ^ 2 + inner ℝ (v 0) J + c 0)
    (hneg : ‖J‖ ^ 2 + inner ℝ (v 0) J + c 0 < 0) :
    ∃ X Y : EuclideanSpace ℝ (Fin 2), X ≠ Y ∧
      (∀ i : Fin 3,
        ‖X‖ ^ 2 + inner ℝ (v i) X + c i = 0 ∧
        ‖Y‖ ^ 2 + inner ℝ (v i) Y + c i = 0) ∧
      (∀ i : Fin 3, EuclideanGeometry.Cospherical
        {P : EuclideanSpace ℝ (Fin 2) |
          ‖P‖ ^ 2 + inner ℝ (v i) P + c i = 0}) := by classical
  have coord (P Q : EuclideanSpace ℝ (Fin 2)) :
      inner ℝ P Q = P 0 * Q 0 + P 1 * Q 1 := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]
  have normcoord (P : EuclideanSpace ℝ (Fin 2)) :
      ‖P‖ ^ 2 = P 0 ^ 2 + P 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, coord]
    ring
  let d := v 1 - v 0
  let u : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-d 1, d 0]
  have hu : u ≠ 0 := by
    intro h
    have h0 := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 0) h
    have h1 := congrArg (fun P : EuclideanSpace ℝ (Fin 2) => P 1) h
    apply hne
    ext j
    fin_cases j <;> simp [u, d] at h0 h1 ⊢ <;> linarith
  have hdu : inner ℝ d u = 0 := by
    simp [coord, u]
    ring
  obtain ⟨t, ht⟩ := hcol
  have hperp (i : Fin 3) : inner ℝ (v i) u = inner ℝ (v 0) u := by
    have h1 : inner ℝ (v 1 - v 0) u = 0 := hdu
    have h2 : inner ℝ (v 2 - v 0) u = 0 := by
      rw [ht, inner_smul_left, h1]
      simp
    rw [inner_sub_left] at h1 h2
    fin_cases i
    · rfl
    · exact sub_eq_zero.mp h1
    · exact sub_eq_zero.mp h2
  let a : ℝ := ‖u‖ ^ 2
  let b : ℝ := 2 * inner ℝ J u + inner ℝ (v 0) u
  let k : ℝ := ‖J‖ ^ 2 + inner ℝ (v 0) J + c 0
  have ha : 0 < a := sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hk : k < 0 := hneg
  have expand (s : ℝ) (i : Fin 3) :
      ‖J + s • u‖ ^ 2 + inner ℝ (v i) (J + s • u) + c i = a*s^2+b*s+k := by
    have hi := hsame i
    have hp := hperp i
    simp only [normcoord, coord] at hi hp
    simp [a, b, k, normcoord, coord]
    nlinarith only [hi, congrArg (fun x : ℝ => x * s) hp]
  let D := b^2 - 4*a*k
  have hD : 0 < D := by dsimp [D]; nlinarith [sq_nonneg b, mul_neg_of_pos_of_neg ha hk]
  have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt (le_of_lt hD)
  have hspos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
  let r₁ := (-b + Real.sqrt D) / (2*a)
  let r₂ := (-b - Real.sqrt D) / (2*a)
  have hr₁ : a*r₁^2+b*r₁+k = 0 := by
    dsimp [r₁]
    field_simp
    nlinarith [hs]
  have hr₂ : a*r₂^2+b*r₂+k = 0 := by
    dsimp [r₂]
    field_simp
    nlinarith [hs]
  have hrne : r₁ ≠ r₂ := by
    intro h
    have h' := (div_left_inj' (show 2*a ≠ 0 by positivity)).mp h
    linarith
  refine ⟨J + r₁ • u, J + r₂ • u, ?_, ?_, ?_⟩
  · intro h
    have h' : r₁ • u = r₂ • u := add_left_cancel h
    exact hrne ((smul_left_injective ℝ hu) h')
  · intro i
    rw [expand, expand]
    exact ⟨hr₁, hr₂⟩
  · intro i
    refine ⟨(- (1/2 : ℝ)) • v i, Real.sqrt (‖v i‖^2/4-c i), ?_⟩
    intro P hP
    change ‖P‖ ^ 2 + inner ℝ (v i) P + c i = 0 at hP
    have he : dist P ((-(1/2 : ℝ)) • v i)^2 = ‖v i‖^2/4-c i := by
      rw [dist_eq_norm]
      simp [normcoord, coord] at hP ⊢
      nlinarith
    rw [← he, Real.sqrt_sq (dist_nonneg)]
