import OddInversion.Basic

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

/-- Basic integrability of the distance kernel against a Schwartz test function. -/
lemma dist_mul_schwartz_integrable
    (m : ℕ) (x : OddSpace m) (ψ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m => (dist y x : ℂ) * ψ y) := by
  have hpow : Integrable (fun y : OddSpace m => ‖y‖ ^ (1 : ℕ) * ‖ψ y‖) := by
    simpa using (SchwartzMap.integrable_pow_mul volume ψ 1)
  have hlin : Integrable (fun y : OddSpace m => ‖y‖ * ‖ψ y‖) := by
    simpa using hpow
  have hnormψ : Integrable (fun y : OddSpace m => ‖ψ y‖) := by
    simpa using (SchwartzMap.integrable (μ := volume) ψ).norm
  have hconst : Integrable (fun y : OddSpace m => ‖x‖ * ‖ψ y‖) := by
    simpa using hnormψ.const_mul ‖x‖
  have hdom : Integrable (fun y : OddSpace m => (‖y‖ + ‖x‖) * ‖ψ y‖) := by
    refine (hlin.add hconst).congr ?_
    filter_upwards with y
    simp only [Pi.add_apply]
    ring_nf
  refine hdom.mono' ?_ ?_
  · have hcont : Continuous (fun y : OddSpace m => (dist y x : ℂ) * ψ y) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with y
    have hdist : dist y x ≤ ‖y‖ + ‖x‖ := by
      calc
        dist y x = ‖y - x‖ := dist_eq_norm y x
        _ ≤ ‖y‖ + ‖x‖ := by
          simpa [sub_eq_add_neg, norm_neg, add_comm, add_left_comm, add_assoc] using
            (norm_add_le y (-x))
    have hcast : ‖(dist y x : ℂ)‖ = dist y x := by
      simp [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    calc
      ‖(dist y x : ℂ) * ψ y‖ = ‖(dist y x : ℂ)‖ * ‖ψ y‖ := by
        exact norm_mul _ _
      _ = dist y x * ‖ψ y‖ := by
        rw [hcast]
      _ ≤ (‖y‖ + ‖x‖) * ‖ψ y‖ := by
        exact mul_le_mul_of_nonneg_right hdist (norm_nonneg (ψ y))

/-- The actual distance-kernel integrand in the target theorem is integrable. -/
lemma dist_mul_iterated_laplacian_integrable
    (m : ℕ) (x : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m =>
      (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) := by
  exact dist_mul_schwartz_integrable m x ((Laplacian.laplacian^[m + 1]) φ)

/-- Specialization of the distance-kernel integrability bound to the origin. -/
lemma norm_mul_schwartz_integrable
    (m : ℕ) (ψ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m => (‖y‖ : ℂ) * ψ y) := by
  simpa [dist_eq_norm] using
    (dist_mul_schwartz_integrable m (0 : OddSpace m) ψ)

/-- The norm-kernel integrand in the origin theorem is integrable. -/
lemma norm_mul_iterated_laplacian_integrable
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m =>
      (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) := by
  exact norm_mul_schwartz_integrable m ((Laplacian.laplacian^[m + 1]) φ)

/-- The norm kernel `φ ↦ ∫ y, ‖y‖ * φ y` as a tempered distribution. -/
noncomputable def normKernelDistributionAtZero
    (m : ℕ) : 𝓢'(OddSpace m, ℂ) := by
  let μ : Measure (OddSpace m) := volume
  let K : ℕ := μ.integrablePower
  let S : Finset (ℕ × ℕ) := Finset.Iic (K + 1, 0)
  let C : ℝ :=
    2 ^ μ.integrablePower *
      (∫ x : OddSpace m, (1 + ‖x‖) ^ (-(μ.integrablePower : ℝ)) ∂μ) *
        (2 * 2 ^ (K + 1))
  refine ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ ?_
  refine SchwartzMap.mkCLMtoNormedSpace
    (𝕜 := ℂ) (𝕜' := ℂ) (D := OddSpace m) (E := ℂ) (G := ℂ)
    (σ := RingHom.id ℂ)
    (fun φ : 𝓢(OddSpace m, ℂ) => ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y) ?_ ?_ ?_
  · intro φ ψ
    calc
      ∫ y : OddSpace m, (‖y‖ : ℂ) * (φ + ψ) y
          = ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y + (‖y‖ : ℂ) * ψ y := by
              refine integral_congr_ae ?_
              filter_upwards with y
              simp [mul_add]
      _ = (∫ y : OddSpace m, (‖y‖ : ℂ) * φ y) +
            ∫ y : OddSpace m, (‖y‖ : ℂ) * ψ y := by
              exact integral_add (norm_mul_schwartz_integrable m φ)
                (norm_mul_schwartz_integrable m ψ)
  · intro a φ
    calc
      ∫ y : OddSpace m, (‖y‖ : ℂ) * (a • φ) y
          = ∫ y : OddSpace m, a • ((‖y‖ : ℂ) * φ y) := by
              refine integral_congr_ae ?_
              filter_upwards with y
              simp [mul_left_comm]
      _ = a • ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y := by
              exact integral_smul a (fun y : OddSpace m => (‖y‖ : ℂ) * φ y)
  · refine ⟨S, C, ?_, ?_⟩
    · dsimp [C]
      positivity
    · intro φ
      let B : ℝ := S.sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
      have hC₁ : ∀ x : OddSpace m, ‖φ x‖ ≤ 2 ^ (K + 1) * B := by
        intro x
        have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + 1, 0))
          (k := 0) (n := 0) (by omega) (by omega) φ x
        simpa [S, B] using h
      have hC₂ : ∀ x : OddSpace m,
          ‖x‖ ^ (1 + μ.integrablePower) * ‖φ x‖ ≤ 2 ^ (K + 1) * B := by
        intro x
        have hpow : ‖x‖ ^ (K + 1) * ‖φ x‖ ≤ 2 ^ (K + 1) * B := by
          have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (K + 1, 0))
            (k := K + 1) (n := 0) (by omega) (by omega) φ x
          have hle : ‖x‖ ^ (K + 1) * ‖φ x‖ ≤
              (1 + ‖x‖) ^ (K + 1) * ‖φ x‖ := by
            gcongr
            exact le_add_of_nonneg_left zero_le_one
          exact hle.trans (by simpa [S, B] using h)
        simpa [K, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hpow
      calc
        ‖∫ y : OddSpace m, (‖y‖ : ℂ) * φ y‖
            ≤ ∫ y : OddSpace m, ‖(‖y‖ : ℂ) * φ y‖ :=
              norm_integral_le_integral_norm (fun y : OddSpace m => (‖y‖ : ℂ) * φ y)
        _ = ∫ y : OddSpace m, ‖y‖ ^ (1 : ℕ) * ‖φ y‖ := by
              refine integral_congr_ae ?_
              filter_upwards with y
              simp
        _ ≤ 2 ^ μ.integrablePower *
              (∫ x : OddSpace m, (1 + ‖x‖) ^ (-(μ.integrablePower : ℝ)) ∂μ) *
                ((2 ^ (K + 1) * B) + (2 ^ (K + 1) * B)) := by
              exact integral_pow_mul_le_of_le_of_pow_mul_le (μ := μ) (k := 1)
                hC₁ hC₂
        _ ≤ C * S.sup (schwartzSeminormFamily ℂ (OddSpace m) ℂ) φ := by
              dsimp [C, B, schwartzSeminormFamily]
              ring_nf
              exact le_rfl

theorem normKernelDistributionAtZero_apply
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ)) :
    normKernelDistributionAtZero m φ =
      ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y := by
  simp only [normKernelDistributionAtZero, ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
  rfl

end CramerWoldTheorem.OddInversion
