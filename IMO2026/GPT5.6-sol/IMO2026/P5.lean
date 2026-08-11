import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

namespace IMO2026P5

notation "ℝ+" => Set.Ioi (0 : ℝ)

/-- The answer to be determined. -/
def answer : Set (ℝ+ → ℝ+) :=
  {f | ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c}

private theorem orbit_invariant (f : ℝ+ → ℝ+)
    (h : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) (y : ℝ+) :
    (f (f y) : ℝ) + (y : ℝ) = 2 * (f y : ℝ) := by
  have h' := h (f y) y
  rcases h' with ⟨hu, hl⟩
  have hy : 0 ≤ (f y : ℝ) := le_of_lt (f y).property
  rw [show (f y : ℝ) * (f y : ℝ) = (f y : ℝ) ^ 2 by ring,
      Real.sqrt_sq hy] at hl
  norm_num [Real.sqrt_sq_eq_abs, abs_of_nonneg hy] at hu
  linarith

private lemma sqrt_conditions_iff_polynomial (f : ℝ+ → ℝ+) (x y : ℝ+) :
    ((f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) ↔
    (4 * (x : ℝ) * (f y : ℝ) ≤ ((f x : ℝ) + (y : ℝ)) ^ 2 ∧
      ((f x : ℝ) + (y : ℝ)) ^ 2 ≤ 2 * ((x : ℝ) ^ 2 + (f y : ℝ) ^ 2)) := by
  have hx : 0 ≤ (x : ℝ) := le_of_lt x.property
  have hy : 0 ≤ (y : ℝ) := le_of_lt y.property
  have hfx : 0 ≤ (f x : ℝ) := le_of_lt (f x).property
  have hfy : 0 ≤ (f y : ℝ) := le_of_lt (f y).property
  have hr1 : 0 ≤ (((x : ℝ)^2 + (f y : ℝ)^2) / 2) := by positivity
  have hr2 : 0 ≤ ((x : ℝ) * (f y : ℝ)) := mul_nonneg hx hfy
  have hs1 := Real.sq_sqrt hr1
  have hs2 := Real.sq_sqrt hr2
  constructor <;> intro h
  · rcases h with ⟨h1,h2⟩
    constructor <;> nlinarith [Real.sqrt_nonneg (((x : ℝ)^2 + (f y : ℝ)^2)/2),
      Real.sqrt_nonneg ((x:ℝ)*(f y:ℝ))]
  · rcases h with ⟨h1,h2⟩
    constructor
    · nlinarith [Real.sqrt_nonneg (((x : ℝ)^2 + (f y : ℝ)^2)/2)]
    · nlinarith [Real.sqrt_nonneg ((x:ℝ)*(f y:ℝ))]

private lemma affine_satisfies_conditions (f : ℝ+ → ℝ+) {c : ℝ}
    (_hc : 0 ≤ c) (hf : ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c) :
    ∀ x y : ℝ+,
      (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
        √(x * f y) ≤ (f x + y) / 2 := by
  intro x y
  apply (sqrt_conditions_iff_polynomial f x y).2
  rw [hf x, hf y]
  constructor
  · nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]
  · nlinarith [sq_nonneg ((x : ℝ) - ((y : ℝ) + c))]

private lemma displacement_pinch {x y p q : ℝ}
    (_hx : 0 < x) (_hy : 0 < y) (_hp : 0 < p) (_hq : 0 < q)
    (hlo : 4 * x * q ≤ (p + y) ^ 2)
    (hhi : (p + y) ^ 2 ≤ 2 * (x ^ 2 + q ^ 2)) :
    |(p - x) - (q - y)| * (p + y + x + q) ≤ (x - q) ^ 2 := by
  by_cases hd : 0 ≤ (p-x)-(q-y)
  · rw [abs_of_nonneg hd]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hd)]
    nlinarith

private lemma local_displacement_bound (f : ℝ+ → ℝ+)
    (h : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) (x y : ℝ+)
    (hnear : |(y : ℝ) - (x : ℝ)| < (f x : ℝ) / 2) :
    |((f y : ℝ) - (y : ℝ)) - ((f x : ℝ) - (x : ℝ))| ≤
      ((y : ℝ) - (x : ℝ)) ^ 2 / (f x : ℝ) := by
  have hp := (sqrt_conditions_iff_polynomial f (f x) y).1 (h (f x) y)
  have horb := orbit_invariant f h x
  have horb' : (f (f x) : ℝ) = 2 * (f x : ℝ) - (x : ℝ) := by linarith
  have ha : 0 < (f x : ℝ) := (f x).property
  have hz : 0 < (f y : ℝ) := (f y).property
  rcases abs_lt.mp hnear with ⟨hn, hp'⟩
  have hn' : 0 < (y : ℝ) - (x : ℝ) + (f x : ℝ) / 2 := by linarith
  have hp'' : 0 < (f x : ℝ) / 2 - ((y : ℝ) - (x : ℝ)) := by linarith
  have hupper : ((f y : ℝ) - (y : ℝ)) - ((f x : ℝ) - (x : ℝ)) ≤
      ((y : ℝ) - (x : ℝ)) ^ 2 / (f x : ℝ) := by
    rcases hp with ⟨hlo, hhi⟩
    rw [horb'] at hlo
    field_simp
    nlinarith
  have hlower : -(((y : ℝ) - (x : ℝ)) ^ 2 / (f x : ℝ)) ≤
      ((f y : ℝ) - (y : ℝ)) - ((f x : ℝ) - (x : ℝ)) := by
    rcases hp with ⟨hlo, hhi⟩
    rw [horb'] at hhi
    by_contra hh
    push Not at hh
    have had1 : 0 ≤ (f x : ℝ) * (((y : ℝ) - (x : ℝ)) + (f x : ℝ) / 2) :=
      mul_nonneg (le_of_lt ha) (le_of_lt hn')
    have hd2 : 0 ≤ ((f x : ℝ) / 2 - ((y : ℝ) - (x : ℝ))) *
        ((f x : ℝ) / 2 + ((y : ℝ) - (x : ℝ))) :=
      mul_nonneg (le_of_lt hp'') (by nlinarith)
    have hvpos : 0 < (f x : ℝ) + ((y : ℝ) - (x : ℝ)) -
        ((y : ℝ) - (x : ℝ))^2 / (f x : ℝ) := by
      field_simp
      nlinarith
    have hzlt : (f y : ℝ) < (f x : ℝ) + ((y : ℝ) - (x : ℝ)) -
        ((y : ℝ) - (x : ℝ))^2 / (f x : ℝ) := by linarith
    have hv_sq : ((f x : ℝ) + ((y : ℝ) - (x : ℝ)) -
        ((y : ℝ) - (x : ℝ))^2 / (f x : ℝ))^2 ≤
        ((f x : ℝ) + ((y : ℝ) - (x : ℝ)))^2 - ((y : ℝ) - (x : ℝ))^2 / 2 := by
      field_simp
      nlinarith
    nlinarith [sq_nonneg ((f y : ℝ) - ((f x : ℝ) + ((y : ℝ) - (x : ℝ)) -
      ((y : ℝ) - (x : ℝ))^2 / (f x : ℝ)))]
  rw [abs_le]
  exact ⟨hlower, hupper⟩

private lemma displacement_hasDerivAt_zero (f : ℝ+ → ℝ+)
    (h : ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
      √(x * f y) ≤ (f x + y) / 2) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => if ht : 0 < t then (f ⟨t, ht⟩ : ℝ) - t else 0) 0 x := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let X : ℝ+ := ⟨x, hx⟩
  have ha : 0 < (f X : ℝ) := (f X).property
  have hr : 0 < min x ((f X : ℝ) / 2) := lt_min hx (half_pos ha)
  let L := nhdsWithin (0 : ℝ) ({0}ᶜ)
  have hev : ∀ᶠ t : ℝ in L, |t| < min x ((f X : ℝ) / 2) := by
    have hb : ∀ᶠ t : ℝ in nhds 0, t ∈ Metric.ball 0 (min x ((f X : ℝ) / 2)) :=
      Metric.ball_mem_nhds 0 hr
    filter_upwards [hb.filter_mono inf_le_left] with t ht
    simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using ht
  have hbound : ∀ᶠ t : ℝ in L,
      ‖t⁻¹ • ((if ht : 0 < x + t then (f ⟨x + t, ht⟩ : ℝ) - (x + t) else 0) -
        (if ht : 0 < x then (f ⟨x, ht⟩ : ℝ) - x else 0))‖ ≤ |t| / (f X : ℝ) := by
    filter_upwards [hev] with t ht
    have hxt : 0 < x + t := by
      have hlt := lt_min_iff.mp ht
      rw [abs_lt] at hlt
      linarith
    let Y : ℝ+ := ⟨x+t, hxt⟩
    have hnear' : |(Y : ℝ)-(X : ℝ)| < (f X : ℝ) / 2 := by
      simpa [Y, X] using (lt_of_lt_of_le ht (min_le_right _ _))
    have hn := local_displacement_bound f h X Y hnear'
    simp only [dif_pos hx, dif_pos hxt, Real.norm_eq_abs, smul_eq_mul]
    rw [abs_mul, abs_inv]
    calc
      |t|⁻¹ * |((f Y : ℝ) - (Y : ℝ)) - ((f X : ℝ) - (X : ℝ))|
          ≤ |t|⁻¹ * (((Y : ℝ) - (X : ℝ))^2 / (f X : ℝ)) :=
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr (abs_nonneg t))
      _ = |t| / (f X : ℝ) := by
        simp only [Y, X]
        by_cases ht0 : t = 0
        · simp [ht0]
        · field_simp [ht0]
          rw [show x + t - x = t by ring, sq_abs]
  apply (tendsto_zero_iff_norm_tendsto_zero).2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound
  have habs : Filter.Tendsto (fun t : ℝ => |t|) L (nhds 0) := by
    change Filter.Tendsto (fun t : ℝ => |t|) (nhds 0 ⊓ Filter.principal ({0}ᶜ)) (nhds 0)
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left inf_le_left
  simpa using habs.div_const (f X : ℝ)

theorem result : {f : ℝ+ → ℝ+ | ∀ x y : ℝ+, (f x + y) / 2 ≤ √((x ^ 2 + f y ^ 2) / 2) ∧
    √(x * f y) ≤ (f x + y) / 2} = answer := by
  ext f
  constructor
  · intro hf
    change ∃ c : ℝ, 0 ≤ c ∧ ∀ x : ℝ+, (f x : ℝ) = (x : ℝ) + c
    let D : ℝ → ℝ := fun t => if ht : 0 < t then (f ⟨t, ht⟩ : ℝ) - t else 0
    have hdiff : DifferentiableOn ℝ D (Set.Ioi 0) := by
      intro x hx
      exact (displacement_hasDerivAt_zero f hf hx).differentiableAt.differentiableWithinAt
    have hderiv : (Set.Ioi (0 : ℝ)).EqOn (deriv D) 0 := by
      intro x hx
      exact (displacement_hasDerivAt_zero f hf hx).deriv
    let x₀ : ℝ+ := ⟨1, by norm_num⟩
    let c : ℝ := (f x₀ : ℝ) - (x₀ : ℝ)
    have hconst : ∀ x : ℝ+, (f x : ℝ) - (x : ℝ) = c := by
      intro x
      have heq := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hderiv
        x.property x₀.property
      have hx : 0 < (x : ℝ) := x.property
      have hx₀ : 0 < (x₀ : ℝ) := x₀.property
      dsimp [D] at heq
      simp only [dif_pos hx, dif_pos hx₀] at heq
      simpa [c] using heq
    have hc : 0 ≤ c := by
      by_contra hc'
      push Not at hc'
      have hzpos : 0 < -c / 2 := by linarith
      let z : ℝ+ := ⟨-c / 2, hzpos⟩
      have hz := hconst z
      have hfz : 0 < (f z : ℝ) := (f z).property
      simp only [z] at hz
      linarith
    refine ⟨c, hc, ?_⟩
    intro x
    have := hconst x
    linarith
  · rintro ⟨c, hc, hf⟩
    exact affine_satisfies_conditions f hc hf

end IMO2026P5
