import CramerWoldTheorem.Basic

/-!
Proof-focused subproject for replacing
`CramerWoldTheorem.averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal`.

This file is intentionally not imported by `CramerWoldTheorem.Main`.  It gives a
small proof queue for the odd-dimensional inversion fact without adding another
axiom to the main development.
-/

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

/-- The positive odd Euclidean space used by the current `Inversion.lean` axiom. -/
abbrev OddSpace (m : ℕ) := RealEuclideanSpace (2 * m + 1)

/--
The centered distance kernel whose `μ`-integral is `averageDistance μ y`.

For source dimension `d = 2 * q - 1`, the paper applies `Δ ^ q`.  In this
Lean reindexing `d = 2 * m + 1`, so the expected recovery power is `m + 1`.
-/
def centeredDistanceKernel (m : ℕ) (x y : OddSpace m) : ℝ :=
  dist y x - dist (0 : OddSpace m) x

/-- Definitional rewrite exposing `averageDistance` as the centered-distance kernel integral. -/
private theorem averageDistance_eq_integral_centeredDistanceKernel
    (m : ℕ) (μ : Measure (OddSpace m)) (y : OddSpace m) :
    averageDistance μ y = ∫ x, centeredDistanceKernel m x y ∂μ := by
  rfl

/-- Pointwise equality of average-distance potentials as equality of kernel integrals. -/
private theorem centeredDistanceKernel_integral_eq_of_averageDistance_eq
    (m : ℕ) (μ ν : Measure (OddSpace m))
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y) :
    ∀ y : OddSpace m,
      ∫ x, centeredDistanceKernel m x y ∂μ =
        ∫ x, centeredDistanceKernel m x y ∂ν := by
  intro y
  simpa [averageDistance_eq_integral_centeredDistanceKernel] using havg y

/--
Algebraic endpoint after an inversion formula: if the integral of a Schwartz
function is represented by the same weighted integral of `averageDistance`, then
pointwise equality of average-distance potentials gives equality of the Schwartz
integrals.  The missing analytic work is to construct such a formula with the
weight given by an iterated Laplacian of the test function.
-/
private theorem schwartz_integral_eq_of_potential_formula
    (m : ℕ) (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y)
    (φ : 𝓢(OddSpace m, ℂ)) (w : OddSpace m → ℂ) (c : ℂ)
    (hformula :
      ∀ η : Measure (OddSpace m),
        IsProbabilityMeasure η →
          ∫ x, φ x ∂η =
            c * ∫ y : OddSpace m, (averageDistance η y : ℂ) * w y) :
    ∫ x, φ x ∂μ = ∫ x, φ x ∂ν := by
  rw [hformula μ inferInstance, hformula ν inferInstance]
  refine congrArg (fun z : ℂ => c * z) ?_
  refine integral_congr_ae ?_
  filter_upwards with y
  rw [havg y]

/-- Iterated integration by parts for the Schwartz-space Laplacian. -/
private lemma schwartz_integral_mul_iterated_laplacian_comm
    (m k : ℕ) (φ ψ : 𝓢(OddSpace m, ℂ)) :
    ∫ y : OddSpace m, φ y * ((Laplacian.laplacian^[k]) ψ) y =
      ∫ y : OddSpace m, ((Laplacian.laplacian^[k]) φ) y * ψ y := by
  induction k generalizing φ ψ with
  | zero =>
      simp
  | succ k ih =>
      calc
        ∫ y : OddSpace m, φ y * ((Laplacian.laplacian^[Nat.succ k]) ψ) y
            = ∫ y : OddSpace m,
                (Laplacian.laplacian φ) y * ((Laplacian.laplacian^[k]) ψ) y := by
                simpa [Function.iterate_succ_apply'] using
                  (SchwartzMap.integral_mul_laplacian_right_eq_left φ
                    ((Laplacian.laplacian^[k]) ψ))
        _ = ∫ y : OddSpace m,
              ((Laplacian.laplacian^[k]) (Laplacian.laplacian φ)) y * ψ y := by
                exact ih (Laplacian.laplacian φ) ψ
        _ = ∫ y : OddSpace m,
              ((Laplacian.laplacian^[Nat.succ k]) φ) y * ψ y := by
                simp [Function.iterate_succ_apply]

/-- Basic integrability of the distance kernel against a Schwartz test function. -/
private lemma dist_mul_schwartz_integrable
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
    simpa [add_mul] using hlin.add hconst
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
private lemma dist_mul_iterated_laplacian_integrable
    (m : ℕ) (x : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m =>
      (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) := by
  exact dist_mul_schwartz_integrable m x ((Laplacian.laplacian^[m + 1]) φ)

/-- Specialization of the distance-kernel integrability bound to the origin. -/
private lemma norm_mul_schwartz_integrable
    (m : ℕ) (ψ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m => (‖y‖ : ℂ) * ψ y) := by
  simpa [dist_eq_norm] using
    (dist_mul_schwartz_integrable m (0 : OddSpace m) ψ)

/-- The norm-kernel integrand in the origin theorem is integrable. -/
private lemma norm_mul_iterated_laplacian_integrable
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ)) :
    Integrable (fun y : OddSpace m =>
      (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) := by
  exact norm_mul_schwartz_integrable m ((Laplacian.laplacian^[m + 1]) φ)

/-- Iterating the distributional Laplacian amounts to moving the same iterate to
Schwartz test functions. -/
private lemma temperedDistribution_iterated_laplacian_apply_apply
    (m k : ℕ) (T : 𝓢'(OddSpace m, ℂ)) (φ : 𝓢(OddSpace m, ℂ)) :
    ((Laplacian.laplacian^[k]) T) φ =
      T ((Laplacian.laplacian^[k]) φ) := by
  induction k generalizing T φ with
  | zero =>
      simp
  | succ k ih =>
      calc
        ((Laplacian.laplacian^[Nat.succ k]) T) φ
            = (Laplacian.laplacian ((Laplacian.laplacian^[k]) T)) φ := by
                simp [Function.iterate_succ_apply']
        _ = ((Laplacian.laplacian^[k]) T) (Laplacian.laplacian φ) := by
                exact TemperedDistribution.laplacian_apply_apply ((Laplacian.laplacian^[k]) T) φ
        _ = T ((Laplacian.laplacian^[k]) (Laplacian.laplacian φ)) := by
                exact ih T (Laplacian.laplacian φ)
        _ = T ((Laplacian.laplacian^[Nat.succ k]) φ) := by
                simp [Function.iterate_succ_apply]

/-- The norm kernel `φ ↦ ∫ y, ‖y‖ * φ y` as a tempered distribution. -/
private noncomputable def normKernelDistributionAtZero
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
      let B : ℝ := S.sup (schwartzSeminormFamily ℂ (OddSpace m) ℂ) φ
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
              dsimp [C, B]
              ring_nf
              exact le_rfl

private theorem normKernelDistributionAtZero_apply
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ)) :
    normKernelDistributionAtZero m φ =
      ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y := by
  simp only [normKernelDistributionAtZero, ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
  rfl

/--
If the norm-kernel distribution has the expected iterated-Laplacian identity,
then the pointwise Schwartz pairing statement follows immediately.
-/
private theorem norm_iterated_laplacian_pairing_at_zero_of_distributional_identity
    (m : ℕ)
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m) =
          c • TemperedDistribution.delta (0 : OddSpace m))) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ 0 := by
  rcases h with ⟨c, hc, hdist⟩
  refine ⟨c, hc, ?_⟩
  intro φ
  calc
    ∫ y : OddSpace m,
        (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y
        = normKernelDistributionAtZero m ((Laplacian.laplacian^[m + 1]) φ) := by
            exact (normKernelDistributionAtZero_apply m
              ((Laplacian.laplacian^[m + 1]) φ)).symm
    _ = ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m)) φ := by
            exact (temperedDistribution_iterated_laplacian_apply_apply
              m (m + 1) (normKernelDistributionAtZero m) φ).symm
    _ = (c • TemperedDistribution.delta (0 : OddSpace m)) φ := by
            rw [hdist]
    _ = c * φ 0 := by
            simp

/--
Fourier-domain version of the same blocker.  Since
`𝓕 δ₀ = volume.toTemperedDistribution` is already in Mathlib, it suffices to
prove that the Fourier transform of the iterated Laplacian of the norm-kernel
is a nonzero constant multiple of the constant distribution.
-/
private theorem norm_iterated_laplacian_pairing_at_zero_of_fourier_laplacian_identity
    (m : ℕ)
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        𝓕 ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m)) =
          c • ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ))) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ 0 := by
  rcases h with ⟨c, hc, hfourier⟩
  refine norm_iterated_laplacian_pairing_at_zero_of_distributional_identity m
    ⟨c, hc, ?_⟩
  calc
    ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m))
        = 𝓕⁻ (𝓕 ((Laplacian.laplacian^[m + 1])
            (normKernelDistributionAtZero m))) := by
            rw [FourierTransform.fourierInv_fourier_eq]
    _ = 𝓕⁻ (c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ))) := by
            rw [hfourier]
    _ = 𝓕⁻ (𝓕 (c • TemperedDistribution.delta (0 : OddSpace m))) := by
            congr 1
            rw [FourierTransform.fourier_smul,
              TemperedDistribution.fourier_delta_zero]
    _ = c • TemperedDistribution.delta (0 : OddSpace m) := by
            rw [FourierTransform.fourierInv_fourier_eq]

/-- Fourier-side multiplication by `‖ξ‖²` on tempered distributions. -/
private noncomputable def fourierNormSqMultiplier
    (m : ℕ) : 𝓢'(OddSpace m, ℂ) →L[ℂ] 𝓢'(OddSpace m, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ
    (fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2))

/-- A single distributional Laplacian becomes multiplication by `-(2π)^2 ‖ξ‖²`
after Fourier transform. -/
private lemma fourier_laplacian_eq_smulLeftCLM_normSq
    (m : ℕ) (T : 𝓢'(OddSpace m, ℂ)) :
    𝓕 (Laplacian.laplacian T) =
      ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ) •
        fourierNormSqMultiplier m (𝓕 T) := by
  rw [TemperedDistribution.laplacian_eq_fourierMultiplierCLM T]
  rw [← Complex.coe_smul (-(2 * Real.pi) ^ 2)]
  rw [FourierTransform.fourier_smul]
  rw [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [FourierTransform.fourier_fourierInv_eq]
  rfl

/-- Iterated version of `fourier_laplacian_eq_smulLeftCLM_normSq`. -/
private lemma fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
    (m k : ℕ) (T : 𝓢'(OddSpace m, ℂ)) :
    𝓕 ((Laplacian.laplacian^[k]) T) =
      ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ) ^ k •
        (((fourierNormSqMultiplier m)^[k]) (𝓕 T)) := by
  let a : ℂ := ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)
  let M : 𝓢'(OddSpace m, ℂ) →L[ℂ] 𝓢'(OddSpace m, ℂ) :=
    fourierNormSqMultiplier m
  change 𝓕 ((Laplacian.laplacian^[k]) T) = a ^ k • ((M^[k]) (𝓕 T))
  induction k with
  | zero =>
      simp [M]
  | succ k ih =>
      calc
        𝓕 ((Laplacian.laplacian^[Nat.succ k]) T)
            = 𝓕 (Laplacian.laplacian ((Laplacian.laplacian^[k]) T)) := by
                simp [Function.iterate_succ_apply']
        _ = a • M (𝓕 ((Laplacian.laplacian^[k]) T)) := by
                simpa [a, M] using
                  fourier_laplacian_eq_smulLeftCLM_normSq m
                    ((Laplacian.laplacian^[k]) T)
        _ = a • M (a ^ k • ((M^[k]) (𝓕 T))) := by
                rw [ih]
        _ = a ^ Nat.succ k • ((M^[Nat.succ k]) (𝓕 T)) := by
                simp [Function.iterate_succ_apply', pow_succ, mul_smul, mul_comm]

/-- Collapse the iterated Fourier-side `‖ξ‖²` multipliers into one multiplier. -/
private lemma iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow
    (m k : ℕ) (T : 𝓢'(OddSpace m, ℂ)) :
    ((fourierNormSqMultiplier m)^[k]) T =
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) T := by
  induction k with
  | zero =>
      simp [fourierNormSqMultiplier]
  | succ k ih =>
      calc
        ((fourierNormSqMultiplier m)^[Nat.succ k]) T
            = fourierNormSqMultiplier m (((fourierNormSqMultiplier m)^[k]) T) := by
                simp [Function.iterate_succ_apply']
        _ = fourierNormSqMultiplier m
              (TemperedDistribution.smulLeftCLM ℂ
                (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) T) := by
                rw [ih]
        _ = TemperedDistribution.smulLeftCLM ℂ
              ((fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) *
                fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2)) T := by
                change TemperedDistribution.smulLeftCLM ℂ
                    (fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2))
                    (TemperedDistribution.smulLeftCLM ℂ
                      (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) T) =
                  TemperedDistribution.smulLeftCLM ℂ
                    ((fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) *
                      fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2)) T
                exact TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
                  (F := ℂ)
                  (g₁ := fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k)
                  (g₂ := fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2))
                  (by fun_prop) (by fun_prop) T
        _ = TemperedDistribution.smulLeftCLM ℂ
              (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ Nat.succ k) T := by
                have hfun :
                    ((fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ k) *
                        fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2)) =
                      (fun ξ : OddSpace m =>
                        (Complex.ofReal (‖ξ‖ ^ 2)) ^ Nat.succ k) := by
                  funext ξ
                  simp [Pi.mul_apply, pow_succ]
                rw [hfun]

/--
Multiplier-form Fourier target.  This is often the most Mathlib-compatible
remaining analytic statement: after taking Fourier transforms, it is enough to
show that multiplying `𝓕 ‖x‖` by `‖ξ‖²` exactly `m + 1` times gives a nonzero
constant distribution.
-/
private theorem norm_iterated_laplacian_pairing_at_zero_of_fourier_multiplier_iterate_identity
    (m : ℕ)
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        (((fourierNormSqMultiplier m)^[m + 1])
            (𝓕 (normKernelDistributionAtZero m))) =
          c • ((volume : Measure (OddSpace m)).toTemperedDistribution)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ 0 := by
  rcases h with ⟨c, hc, hmult⟩
  let a : ℂ := ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    norm_num [Complex.ofReal_eq_zero, Real.pi_ne_zero]
  refine norm_iterated_laplacian_pairing_at_zero_of_fourier_laplacian_identity m
    ⟨a ^ (m + 1) * c, mul_ne_zero (pow_ne_zero (m + 1) ha) hc, ?_⟩
  calc
    𝓕 ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m))
        = a ^ (m + 1) •
            (((fourierNormSqMultiplier m)^[m + 1])
                (𝓕 (normKernelDistributionAtZero m))) := by
            simpa [a] using
              fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
                m (m + 1) (normKernelDistributionAtZero m)
    _ = a ^ (m + 1) •
          (c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ))) := by
            rw [hmult]
    _ = (a ^ (m + 1) * c) •
          ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ)) := by
            rw [mul_smul]

/--
Single-multiplier Fourier target.  This is the cleanest remaining Fourier
subgoal: prove that `(‖ξ‖²)^(m+1) • 𝓕(‖x‖)` is a nonzero constant distribution.
-/
private theorem norm_iterated_laplacian_pairing_at_zero_of_fourier_multiplier_power_identity
    (m : ℕ)
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        TemperedDistribution.smulLeftCLM ℂ
          (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
          (𝓕 (normKernelDistributionAtZero m)) =
            c • ((volume : Measure (OddSpace m)).toTemperedDistribution)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ 0 := by
  rcases h with ⟨c, hc, hpow⟩
  refine norm_iterated_laplacian_pairing_at_zero_of_fourier_multiplier_iterate_identity
    m ⟨c, hc, ?_⟩
  rw [iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow m (m + 1)
    (𝓕 (normKernelDistributionAtZero m))]
  exact hpow

/--
Reverse bridge from the classical distributional fundamental-solution identity
to the Fourier multiplier formulation.  This keeps the Green-identity route and
the Fourier/Riesz route interchangeable: proving
`Δ^(m+1) ‖x‖ = c δ₀` is enough to close the multiplier target below.
-/
private theorem normKernel_fourier_multiplier_power_eq_constDistribution_of_distributional_identity
    (m : ℕ)
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m) =
          c • TemperedDistribution.delta (0 : OddSpace m))) :
    ∃ c : ℂ, c ≠ 0 ∧
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 (normKernelDistributionAtZero m)) =
          c • ((volume : Measure (OddSpace m)).toTemperedDistribution) := by
  rcases h with ⟨c, hc, hdist⟩
  let a : ℂ := ((-(2 * Real.pi) ^ 2 : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    norm_num [Complex.ofReal_eq_zero, Real.pi_ne_zero]
  refine ⟨(a ^ (m + 1))⁻¹ * c, mul_ne_zero (inv_ne_zero (pow_ne_zero _ ha)) hc, ?_⟩
  let Mpow : 𝓢'(OddSpace m, ℂ) :=
    TemperedDistribution.smulLeftCLM ℂ
      (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
      (𝓕 (normKernelDistributionAtZero m))
  have hfourier :
      𝓕 ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m)) =
        c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
          𝓢'(OddSpace m, ℂ)) := by
    rw [hdist, FourierTransform.fourier_smul,
      TemperedDistribution.fourier_delta_zero]
  have hmult :
      a ^ (m + 1) • Mpow =
        c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
          𝓢'(OddSpace m, ℂ)) := by
    calc
      a ^ (m + 1) • Mpow
          = a ^ (m + 1) •
              (((fourierNormSqMultiplier m)^[m + 1])
                (𝓕 (normKernelDistributionAtZero m))) := by
              congr 1
              exact (iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow
                m (m + 1) (𝓕 (normKernelDistributionAtZero m))).symm
      _ = 𝓕 ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m)) := by
              exact (fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
                m (m + 1) (normKernelDistributionAtZero m)).symm
      _ = c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ)) := hfourier
  calc
    TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 (normKernelDistributionAtZero m))
        = (a ^ (m + 1))⁻¹ • (a ^ (m + 1) • Mpow) := by
            simp [Mpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ha)]
    _ = (a ^ (m + 1))⁻¹ •
          (c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ))) := by
            rw [hmult]
    _ = ((a ^ (m + 1))⁻¹ * c) •
          ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ)) := by
            rw [mul_smul]

/--
Algebraic composition step for the Green-identity route.  If `k` Laplacians of
`T` give a nonzero multiple of an intermediate Riesz-type distribution `U`, and
one more Laplacian of `U` gives a nonzero multiple of `V`, then `k + 1`
Laplacians of `T` give a nonzero multiple of `V`.
-/
private lemma iterated_laplacian_succ_eq_smul_of_iterated_eq_smul
    (m k : ℕ) (T U V : 𝓢'(OddSpace m, ℂ)) (a b : ℂ)
    (hTU : ((Laplacian.laplacian^[k]) T) = a • U)
    (hUV : Laplacian.laplacian U = b • V) :
    ((Laplacian.laplacian^[k + 1]) T) = (a * b) • V := by
  calc
    ((Laplacian.laplacian^[k + 1]) T)
        = Laplacian.laplacian ((Laplacian.laplacian^[k]) T) := by
            simp [Function.iterate_succ_apply']
    _ = Laplacian.laplacian (a • U) := by
            rw [hTU]
    _ = (LineDeriv.laplacianCLM ℂ (OddSpace m) 𝓢'(OddSpace m, ℂ)) (a • U) := by
            rw [TemperedDistribution.laplacianCLM_apply]
    _ = a • (LineDeriv.laplacianCLM ℂ (OddSpace m) 𝓢'(OddSpace m, ℂ)) U := by
            exact map_smul (LineDeriv.laplacianCLM ℂ (OddSpace m) 𝓢'(OddSpace m, ℂ)) a U
    _ = a • Laplacian.laplacian U := by
            rw [TemperedDistribution.laplacianCLM_apply]
    _ = a • (b • V) := by
            rw [hUV]
    _ = (a * b) • V := by
            rw [mul_smul]

private theorem normKernel_distributional_laplacian_power_eq_delta_of_riesz_step
    (m k : ℕ) (U : 𝓢'(OddSpace m, ℂ)) (a b : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hreduce :
      ((Laplacian.laplacian^[k]) (normKernelDistributionAtZero m)) = a • U)
    (hfund :
      Laplacian.laplacian U = b • TemperedDistribution.delta (0 : OddSpace m)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((Laplacian.laplacian^[k + 1]) (normKernelDistributionAtZero m) =
        c • TemperedDistribution.delta (0 : OddSpace m)) := by
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  exact iterated_laplacian_succ_eq_smul_of_iterated_eq_smul
    m k (normKernelDistributionAtZero m) U
    (TemperedDistribution.delta (0 : OddSpace m)) a b hreduce hfund

/--
Pure Fourier/Riesz-kernel blocker now isolated from the measure-theoretic and
distributional packaging.

Analytically this says that the Fourier transform of `‖x‖`, multiplied by
`(‖ξ‖²)^(m+1)`, is a nonzero constant distribution.  This is equivalent to the
classical odd-dimensional identity `Δ^(m+1) ‖x‖ = c_m δ₀`.
-/
private theorem normKernel_fourier_multiplier_power_eq_constDistribution
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 (normKernelDistributionAtZero m)) =
          c • ((volume : Measure (OddSpace m)).toTemperedDistribution) := by
  sorry

/--
Radial fundamental-solution pairing, now reduced to the pure Fourier/Riesz
multiplier blocker above.  In dimension `2 * m + 1`, pairing `‖x‖` against the
`(m + 1)`-fold Laplacian of a Schwartz test recovers a nonzero multiple of
evaluation at the origin.
-/
private theorem norm_iterated_laplacian_pairing_at_zero
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ 0 := by
  exact norm_iterated_laplacian_pairing_at_zero_of_fourier_multiplier_power_identity
    m (normKernel_fourier_multiplier_power_eq_constDistribution m)

/-- Distributional packaging of the radial pairing identity. -/
private theorem normKernel_distributional_laplacian_power_eq_delta
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m) =
        c • TemperedDistribution.delta (0 : OddSpace m)) := by
  rcases norm_iterated_laplacian_pairing_at_zero m with ⟨c, hc, hpair⟩
  refine ⟨c, hc, ?_⟩
  ext φ
  calc
    ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m)) φ
        = normKernelDistributionAtZero m ((Laplacian.laplacian^[m + 1]) φ) := by
            exact temperedDistribution_iterated_laplacian_apply_apply
              m (m + 1) (normKernelDistributionAtZero m) φ
    _ = ∫ y : OddSpace m,
          (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y := by
            exact normKernelDistributionAtZero_apply m ((Laplacian.laplacian^[m + 1]) φ)
    _ = c * φ 0 := hpair φ
    _ = (c • TemperedDistribution.delta (0 : OddSpace m)) φ := by simp

/--
Direct distributional form of the missing radial fundamental-solution theorem.

The norm-kernel distribution itself is now formalized; only the PDE identity
`Δ^(m+1) ‖x‖ = c_m δ₀` remains.
-/
private theorem normKernel_distributional_fundamental_solution_at_zero
    (m : ℕ) :
    ∃ T : 𝓢'(OddSpace m, ℂ),
      (∀ φ : 𝓢(OddSpace m, ℂ),
        T φ = ∫ y : OddSpace m, (‖y‖ : ℂ) * φ y) ∧
      ∃ c : ℂ, c ≠ 0 ∧
        ((Laplacian.laplacian^[m + 1]) T =
          c • TemperedDistribution.delta (0 : OddSpace m)) := by
  refine ⟨normKernelDistributionAtZero m, ?_, ?_⟩
  · intro φ
    exact normKernelDistributionAtZero_apply m φ
  · exact normKernel_distributional_laplacian_power_eq_delta m

/-- The Schwartz-space Laplacian commutes pointwise with translations. -/
private lemma laplacian_compSubConstCLM_apply
    (m : ℕ) (a y : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    (Laplacian.laplacian (φ.compSubConstCLM ℂ a)) y =
      (Laplacian.laplacian φ) (y - a) := by
  rw [SchwartzMap.laplacian_apply, SchwartzMap.laplacian_apply]
  change (Δ (fun z : OddSpace m => φ (z - a))) y =
    (Δ (fun z : OddSpace m => φ z)) (y - a)
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_sub]

private lemma laplacian_compSubConstCLM
    (m : ℕ) (a : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    Laplacian.laplacian (φ.compSubConstCLM ℂ a) =
      (Laplacian.laplacian φ).compSubConstCLM ℂ a := by
  ext y
  exact laplacian_compSubConstCLM_apply m a y φ

private lemma iterated_laplacian_compSubConstCLM
    (m k : ℕ) (a : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    ((Laplacian.laplacian^[k]) (φ.compSubConstCLM ℂ a)) =
      ((Laplacian.laplacian^[k]) φ).compSubConstCLM ℂ a := by
  induction k generalizing φ with
  | zero =>
      simp
  | succ k ih =>
      calc
        ((Laplacian.laplacian^[Nat.succ k]) (φ.compSubConstCLM ℂ a))
            = Laplacian.laplacian
                ((Laplacian.laplacian^[k]) (φ.compSubConstCLM ℂ a)) := by
                simp [Function.iterate_succ_apply']
        _ = Laplacian.laplacian
              (((Laplacian.laplacian^[k]) φ).compSubConstCLM ℂ a) := by
                rw [ih φ]
        _ = (Laplacian.laplacian ((Laplacian.laplacian^[k]) φ)).compSubConstCLM ℂ a := by
                exact laplacian_compSubConstCLM m a ((Laplacian.laplacian^[k]) φ)
        _ = ((Laplacian.laplacian^[Nat.succ k]) φ).compSubConstCLM ℂ a := by
                simp [Function.iterate_succ_apply']

private lemma iterated_laplacian_compSubConstCLM_apply
    (m k : ℕ) (a y : OddSpace m) (φ : 𝓢(OddSpace m, ℂ)) :
    ((Laplacian.laplacian^[k]) (φ.compSubConstCLM ℂ a)) y =
      ((Laplacian.laplacian^[k]) φ) (y - a) := by
  rw [iterated_laplacian_compSubConstCLM m k a φ]
  rfl

/--
Translation-invariance packaging from the origin radial identity to a pole at
an arbitrary point.
-/
private theorem distance_iterated_laplacian_pairing_of_norm_translation
    (m : ℕ)
    (hnorm :
      ∃ c : ℂ, c ≠ 0 ∧
        ∀ φ : 𝓢(OddSpace m, ℂ),
          ∫ y : OddSpace m,
              (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
            c * φ 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ x := by
  rcases hnorm with ⟨c, hc, hnorm⟩
  refine ⟨c, hc, ?_⟩
  intro x φ
  let ψ : 𝓢(OddSpace m, ℂ) := φ.compSubConstCLM ℂ (-x)
  have hΔ : ∀ y : OddSpace m,
      ((Laplacian.laplacian^[m + 1]) ψ) y =
        ((Laplacian.laplacian^[m + 1]) φ) (y + x) := by
    intro y
    have h := iterated_laplacian_compSubConstCLM_apply m (m + 1) (-x) y φ
    simpa [ψ, sub_neg_eq_add] using h
  calc
    ∫ y : OddSpace m,
        (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y
        = ∫ y : OddSpace m,
            (dist (y + x) x : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) (y + x) := by
              rw [← integral_add_right_eq_self
                (fun y : OddSpace m =>
                  (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) x]
    _ = ∫ y : OddSpace m,
          (‖y‖ : ℂ) * ((Laplacian.laplacian^[m + 1]) ψ) y := by
          refine integral_congr_ae ?_
          filter_upwards with y
          rw [hΔ y]
          congr 1
          simp [dist_eq_norm]
    _ = c * ψ 0 := hnorm ψ
    _ = c * φ x := by
          simp [ψ]

/--
Uncentered fundamental-solution blocker.

In dimension `2 * m + 1`, pairing `y ↦ dist y x` with the `(m + 1)`-fold
Laplacian of a Schwartz test function should recover the test value at `x`, up
to a nonzero dimensional constant.
-/
private theorem distance_iterated_laplacian_pairing
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ x := by
  exact distance_iterated_laplacian_pairing_of_norm_translation m
    (norm_iterated_laplacian_pairing_at_zero m)

private lemma smulLeftCLM_delta_zero_of_apply_zero
    (m : ℕ) (g : OddSpace m → ℂ) (hg : g.HasTemperateGrowth)
    (hg0 : g (0 : OddSpace m) = 0) :
    TemperedDistribution.smulLeftCLM ℂ g
      (TemperedDistribution.delta (0 : OddSpace m)) = 0 := by
  ext φ
  simp [TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, hg0]

private lemma lineDeriv_volume_toTemperedDistribution_eq_zero
    (m : ℕ) (v : OddSpace m) :
    ∂_{v} ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ)) = 0 := by
  rw [← TemperedDistribution.fourier_delta_zero (E := OddSpace m)]
  rw [TemperedDistribution.lineDerivOp_fourier_eq]
  have hmul :
      TemperedDistribution.smulLeftCLM ℂ (fun x : OddSpace m => (inner ℝ x v : ℂ))
        (TemperedDistribution.delta (0 : OddSpace m)) = 0 := by
    exact smulLeftCLM_delta_zero_of_apply_zero m
      (fun x : OddSpace m => (inner ℝ x v : ℂ)) (by fun_prop) (by simp)
  rw [hmul]
  simp

private lemma laplacian_volume_toTemperedDistribution_eq_zero
    (m : ℕ) :
    Δ ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ)) = 0 := by
  rw [TemperedDistribution.laplacian_eq_sum (stdOrthonormalBasis ℝ (OddSpace m))]
  simp [lineDeriv_volume_toTemperedDistribution_eq_zero]

private lemma iterated_laplacian_succ_volume_toTemperedDistribution_eq_zero
    (m k : ℕ) :
    ((Laplacian.laplacian^[k + 1])
      ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ))) = 0 := by
  induction k with
  | zero =>
      simpa using laplacian_volume_toTemperedDistribution_eq_zero m
  | succ k ih =>
      calc
        ((Laplacian.laplacian^[Nat.succ k + 1])
          ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ)))
            = Δ ((Laplacian.laplacian^[k + 1])
                ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ))) := by
                simp [Nat.succ_eq_add_one, Function.iterate_succ_apply']
        _ = 0 := by
              rw [ih]
              rw [← TemperedDistribution.laplacianCLM_apply
                (0 : 𝓢'(OddSpace m, ℂ))]
              exact map_zero (LineDeriv.laplacianCLM ℂ (OddSpace m) 𝓢'(OddSpace m, ℂ))

/--
The constant subtraction in `centeredDistanceKernel` should vanish against an
iterated Laplacian of a Schwartz test function.
-/
private theorem integral_iterated_laplacian_eq_zero
    (m : ℕ) :
    ∀ φ : 𝓢(OddSpace m, ℂ),
      ∫ y : OddSpace m, ((Laplacian.laplacian^[m + 1]) φ) y = 0 := by
  intro φ
  have hzero :=
    congrArg (fun T : 𝓢'(OddSpace m, ℂ) => T φ)
      (iterated_laplacian_succ_volume_toTemperedDistribution_eq_zero m m)
  have hzero' :
      ((Laplacian.laplacian^[m + 1])
        ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ))) φ = 0 := by
    simpa using hzero
  have hmove :=
    temperedDistribution_iterated_laplacian_apply_apply m (m + 1)
      ((volume : Measure (OddSpace m)).toTemperedDistribution : 𝓢'(OddSpace m, ℂ)) φ
  rw [hmove] at hzero'
  simpa [MeasureTheory.Measure.toTemperedDistribution_apply] using hzero'

private theorem constant_iterated_laplacian_integral_eq_zero
    (m : ℕ) :
    ∀ a : ℂ, ∀ φ : 𝓢(OddSpace m, ℂ),
      ∫ y : OddSpace m, a * ((Laplacian.laplacian^[m + 1]) φ) y = 0 := by
  intro a φ
  calc
    ∫ y : OddSpace m, a * ((Laplacian.laplacian^[m + 1]) φ) y
        = a * ∫ y : OddSpace m, ((Laplacian.laplacian^[m + 1]) φ) y := by
          simpa using
            (MeasureTheory.integral_const_mul (μ := volume) a
              (fun y : OddSpace m => ((Laplacian.laplacian^[m + 1]) φ) y))
    _ = 0 := by
          have hzero := integral_iterated_laplacian_eq_zero m φ
          rw [hzero, mul_zero]

/--
Centered kernel pairing reduced to the uncentered distance pairing plus the
vanishing of the constant term.
-/
private theorem centeredDistanceKernel_iterated_laplacian_pairing_of_distance
    (m : ℕ)
    (hdist :
      ∃ c : ℂ, c ≠ 0 ∧
        ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
          ∫ y : OddSpace m,
              (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y =
            c * φ x)
    (hconst :
      ∀ a : ℂ, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m, a * ((Laplacian.laplacian^[m + 1]) φ) y = 0) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (centeredDistanceKernel m x y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ x := by
  rcases hdist with ⟨c, hc, hdist⟩
  refine ⟨c, hc, ?_⟩
  intro x φ
  have hdist_int :
      Integrable (fun y : OddSpace m =>
        (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) :=
    dist_mul_iterated_laplacian_integrable m x φ
  have hconst_int :
      Integrable (fun y : OddSpace m =>
        (dist (0 : OddSpace m) x : ℂ) *
          ((Laplacian.laplacian^[m + 1]) φ) y) := by
    have hφ : Integrable (fun y : OddSpace m =>
        ((Laplacian.laplacian^[m + 1]) φ) y) := by
      simpa using
        (SchwartzMap.integrable (μ := volume) ((Laplacian.laplacian^[m + 1]) φ))
    simpa using hφ.const_mul (dist (0 : OddSpace m) x : ℂ)
  calc
    ∫ y : OddSpace m,
        (centeredDistanceKernel m x y : ℂ) *
          ((Laplacian.laplacian^[m + 1]) φ) y
        = ∫ y : OddSpace m,
            (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y -
              (dist (0 : OddSpace m) x : ℂ) *
                ((Laplacian.laplacian^[m + 1]) φ) y := by
          refine integral_congr_ae ?_
          filter_upwards with y
          simp [centeredDistanceKernel, sub_mul]
    _ = (∫ y : OddSpace m,
            (dist y x : ℂ) * ((Laplacian.laplacian^[m + 1]) φ) y) -
          (∫ y : OddSpace m,
            (dist (0 : OddSpace m) x : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y) := by
          simpa using (integral_sub hdist_int hconst_int)
    _ = c * φ x - 0 := by
          simpa using congrArg₂ (fun u v : ℂ => u - v)
            (hdist x φ) (hconst (dist (0 : OddSpace m) x : ℂ) φ)
    _ = c * φ x := by simp

/--
Hard analytic blocker isolated from the log.

This wrapper keeps the centered statement needed downstream while the proof
queue can first attack the uncentered fundamental-solution and constant-term
subtargets above.
-/
private theorem centeredDistanceKernel_iterated_laplacian_pairing
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (centeredDistanceKernel m x y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ x := by
  exact centeredDistanceKernel_iterated_laplacian_pairing_of_distance m
    (distance_iterated_laplacian_pairing m)
    (constant_iterated_laplacian_integral_eq_zero m)

/--
The remaining Fubini/Tonelli interchange for the average-distance inversion
formula.

The product integrand is controlled by `‖y‖ * ‖Δ^(m+1) φ y‖`, because
`|dist y x - dist 0 x| ≤ ‖y‖`; the latter is integrable for Schwartz `φ`.
This is the only analytic interchange needed after the pointwise kernel
pairing is proved.
-/
private theorem averageDistance_iterated_laplacian_integral_eq_kernel_pairing_integral
    (m : ℕ) (η : Measure (OddSpace m)) [IsProbabilityMeasure η]
    (φ : 𝓢(OddSpace m, ℂ)) :
      ∫ y : OddSpace m,
        (averageDistance η y : ℂ) *
          ((Laplacian.laplacian^[m + 1]) φ) y =
      ∫ x : OddSpace m,
        (∫ y : OddSpace m,
          (centeredDistanceKernel m x y : ℂ) *
            ((Laplacian.laplacian^[m + 1]) φ) y) ∂η := by
  let w : OddSpace m → ℂ := fun y => ((Laplacian.laplacian^[m + 1]) φ) y
  let F : OddSpace m × OddSpace m → ℂ := fun p =>
    (centeredDistanceKernel m p.1 p.2 : ℂ) * w p.2
  have hw_int : Integrable (fun y : OddSpace m => ‖y‖ * ‖w y‖) := by
    dsimp [w]
    have hpow : Integrable
        (fun y : OddSpace m =>
          ‖y‖ ^ (1 : ℕ) * ‖((Laplacian.laplacian^[m + 1]) φ) y‖) := by
      simpa using
        (SchwartzMap.integrable_pow_mul volume ((Laplacian.laplacian^[m + 1]) φ) 1)
    simpa using hpow
  have hdom : Integrable (fun p : OddSpace m × OddSpace m => ‖p.2‖ * ‖w p.2‖)
      (η.prod volume) := by
    exact hw_int.comp_snd η
  have hF_int : Integrable F (η.prod volume) := by
    refine hdom.mono' ?_ ?_
    · have hcont : Continuous F := by
        dsimp [F, w, centeredDistanceKernel]
        fun_prop
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      have hdist : |centeredDistanceKernel m p.1 p.2| ≤ ‖p.2‖ := by
        simpa [centeredDistanceKernel, dist_eq_norm] using
          (abs_dist_sub_le p.2 (0 : OddSpace m) p.1)
      calc
        ‖F p‖ = ‖(centeredDistanceKernel m p.1 p.2 : ℂ)‖ * ‖w p.2‖ := by
          simp [F]
        _ = |centeredDistanceKernel m p.1 p.2| * ‖w p.2‖ := by
          simp [Real.norm_eq_abs]
        _ ≤ ‖p.2‖ * ‖w p.2‖ := by
          exact mul_le_mul_of_nonneg_right hdist (norm_nonneg (w p.2))
  have hpoint : ∀ y : OddSpace m,
      (averageDistance η y : ℂ) * w y = ∫ x : OddSpace m, F (x, y) ∂η := by
    intro y
    calc
      (averageDistance η y : ℂ) * w y
          = (∫ x : OddSpace m, (centeredDistanceKernel m x y : ℂ) ∂η) * w y := by
              rw [averageDistance_eq_integral_centeredDistanceKernel]
              rw [← integral_complex_ofReal (μ := η)
                (f := fun x : OddSpace m => centeredDistanceKernel m x y)]
      _ = ∫ x : OddSpace m, (centeredDistanceKernel m x y : ℂ) * w y ∂η := by
              exact (integral_mul_const (μ := η) (w y)
                (fun x : OddSpace m => (centeredDistanceKernel m x y : ℂ))).symm
      _ = ∫ x : OddSpace m, F (x, y) ∂η := by
              rfl
  calc
    ∫ y : OddSpace m,
        (averageDistance η y : ℂ) *
          ((Laplacian.laplacian^[m + 1]) φ) y
        = ∫ y : OddSpace m, ∫ x : OddSpace m, F (x, y) ∂η := by
            refine integral_congr_ae ?_
            filter_upwards with y
            simpa [w] using hpoint y
    _ = ∫ x : OddSpace m, (∫ y : OddSpace m, F (x, y)) ∂η := by
            exact (MeasureTheory.integral_integral_swap (μ := η) (ν := volume)
              (f := fun x : OddSpace m => fun y : OddSpace m => F (x, y)) hF_int).symm
    _ = ∫ x : OddSpace m,
        (∫ y : OddSpace m,
          (centeredDistanceKernel m x y : ℂ) *
            ((Laplacian.laplacian^[m + 1]) φ) y) ∂η := by
            rfl

/--
Packaged inversion formula needed for the top-level Schwartz-integral theorem.

After `centeredDistanceKernel_iterated_laplacian_pairing`, this should follow
by applying the pairing pointwise in `x`, integrating against `η`, and using the
Fubini/Tonelli step that swaps the `η`-integral with the `y`-integral.
-/
private theorem averageDistance_schwartz_inversion_formula_from_pairing_constant
    (m : ℕ) (η : Measure (OddSpace m)) [IsProbabilityMeasure η]
    (φ : 𝓢(OddSpace m, ℂ)) (c : ℂ) (hc : c ≠ 0)
    (hpair :
      ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ y : OddSpace m,
            (centeredDistanceKernel m x y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y =
          c * φ x) :
    ∫ x, φ x ∂η =
      c⁻¹ * ∫ y : OddSpace m,
        (averageDistance η y : ℂ) *
          ((Laplacian.laplacian^[m + 1]) φ) y := by
  have hkernel :
      ∫ x : OddSpace m,
          (∫ y : OddSpace m,
            (centeredDistanceKernel m x y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y) ∂η =
        c * ∫ x : OddSpace m, φ x ∂η := by
    calc
      ∫ x : OddSpace m,
          (∫ y : OddSpace m,
            (centeredDistanceKernel m x y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y) ∂η
          = ∫ x : OddSpace m, c * φ x ∂η := by
              refine integral_congr_ae (μ := η) ?_
              filter_upwards with x
              exact hpair x φ
      _ = c * ∫ x : OddSpace m, φ x ∂η := by
              simpa using
                (MeasureTheory.integral_const_mul (μ := η) c
                  (fun x : OddSpace m => φ x))
  have havg :
      ∫ y : OddSpace m,
          (averageDistance η y : ℂ) *
            ((Laplacian.laplacian^[m + 1]) φ) y =
        c * ∫ x : OddSpace m, φ x ∂η := by
    calc
      ∫ y : OddSpace m,
          (averageDistance η y : ℂ) *
            ((Laplacian.laplacian^[m + 1]) φ) y
          = ∫ x : OddSpace m,
              (∫ y : OddSpace m,
                (centeredDistanceKernel m x y : ℂ) *
                  ((Laplacian.laplacian^[m + 1]) φ) y) ∂η := by
              exact averageDistance_iterated_laplacian_integral_eq_kernel_pairing_integral
                m η φ
      _ = c * ∫ x : OddSpace m, φ x ∂η := hkernel
  calc
    ∫ x : OddSpace m, φ x ∂η
        = c⁻¹ * (c * ∫ x : OddSpace m, φ x ∂η) := by
            rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = c⁻¹ * ∫ y : OddSpace m,
          (averageDistance η y : ℂ) *
            ((Laplacian.laplacian^[m + 1]) φ) y := by
            rw [havg]

private theorem averageDistance_schwartz_inversion_formula_of_kernel_pairing
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ))
    (hpair :
      ∃ c : ℂ, c ≠ 0 ∧
        ∀ x : OddSpace m, ∀ φ : 𝓢(OddSpace m, ℂ),
          ∫ y : OddSpace m,
              (centeredDistanceKernel m x y : ℂ) *
                ((Laplacian.laplacian^[m + 1]) φ) y =
            c * φ x) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ η : Measure (OddSpace m), IsProbabilityMeasure η →
        ∫ x, φ x ∂η =
          c * ∫ y : OddSpace m,
            (averageDistance η y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y := by
  rcases hpair with ⟨c, hc, hpair⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  intro η hη
  letI : IsProbabilityMeasure η := hη
  exact averageDistance_schwartz_inversion_formula_from_pairing_constant m η φ c hc hpair

/-- Wrapper from the kernel-pairing blocker to the packaged inversion formula. -/
private theorem averageDistance_schwartz_inversion_formula
    (m : ℕ) (φ : 𝓢(OddSpace m, ℂ)) :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ η : Measure (OddSpace m), IsProbabilityMeasure η →
        ∫ x, φ x ∂η =
          c * ∫ y : OddSpace m,
            (averageDistance η y : ℂ) *
              ((Laplacian.laplacian^[m + 1]) φ) y := by
  exact averageDistance_schwartz_inversion_formula_of_kernel_pairing m φ
    (centeredDistanceKernel_iterated_laplacian_pairing m)

/--
First analytic target: equality of average-distance potentials implies equality
of all Schwartz test-function integrals.

Suggested proof route:
1. Regard `averageDistance μ` as the convolution of `μ` with the centered
   distance kernel.
2. Prove the distributional identity
   `Δ ^ (m + 1) (fun y => centeredDistanceKernel m x y) = c_m * delta_x`.
3. Pair both sides with a Schwartz test function and use the hypothesis on
   average-distance functions.
-/
theorem schwartz_integral_eq_of_averageDistance_eq_odd
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y)
    (φ : 𝓢(OddSpace m, ℂ)) :
    ∫ x, φ x ∂μ = ∫ x, φ x ∂ν := by
  rcases averageDistance_schwartz_inversion_formula m φ with ⟨c, _hc, hformula⟩
  let w : OddSpace m → ℂ := fun y => ((Laplacian.laplacian^[m + 1]) φ) y
  have hformula' :
      ∀ η : Measure (OddSpace m),
        IsProbabilityMeasure η →
          ∫ x, φ x ∂η =
            c * ∫ y : OddSpace m, (averageDistance η y : ℂ) * w y := by
    simpa [w] using hformula
  exact schwartz_integral_eq_of_potential_formula m μ ν havg φ w c hformula'

/--
Smooth compactly supported real tests are covered by the Schwartz hypothesis:
coerce the test to a complex-valued smooth compactly supported function, convert
it to a Schwartz map, and then take real parts of the complex integral equality.
-/
private theorem smooth_compactSupport_integral_eq_of_schwartz_integral_eq
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h :
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    {f : OddSpace m → ℝ} (hcs : HasCompactSupport f)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  have hcsC : HasCompactSupport (fun x : OddSpace m => (f x : ℂ)) := by
    simpa [Function.comp_def] using
      hcs.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
  have hsmC :
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : OddSpace m => (f x : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp hsm
  have hφ := h (hcsC.toSchwartzMap hsmC)
  have hC :
      ∫ x : OddSpace m, (f x : ℂ) ∂μ =
        ∫ x : OddSpace m, (f x : ℂ) ∂ν := by
    simpa using hφ
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal (μ := μ) (f := f),
    ← integral_complex_ofReal (μ := ν) (f := f)]
  exact hC

/-- An `L¹(μ + ν)` approximation controls the integral error against `μ`. -/
private lemma integral_norm_sub_le_of_eLpNorm_one_le
    (m : ℕ) (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f g : OddSpace m → ℝ) (hfcs : HasCompactSupport f) (hfc : Continuous f)
    (hgcs : HasCompactSupport g) (hgc : Continuous g) {ε : ℝ} (hε : 0 < ε)
    (happrox : eLpNorm (f - g) 1 (μ + ν) ≤ ENNReal.ofReal ε) :
    ∫ x, ‖f x - g x‖ ∂μ ≤ ε := by
  let lam : Measure (OddSpace m) := μ + ν
  have hf_mem : MemLp f 1 lam := hfc.memLp_of_hasCompactSupport hfcs
  have hg_mem : MemLp g 1 lam := hgc.memLp_of_hasCompactSupport hgcs
  have hfg_mem : MemLp (f - g) 1 lam := hf_mem.sub hg_mem
  have h_int_lam : ∫ x, ‖f x - g x‖ ∂lam ≤ ε := by
    have hLp := hfg_mem.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
    rw [show eLpNorm (f - g) 1 (μ + ν) = eLpNorm (f - g) 1 lam by rfl] at happrox
    rw [hLp] at happrox
    simpa [lam] using (ENNReal.ofReal_le_ofReal_iff hε.le).mp happrox
  have hfi : Integrable (fun x : OddSpace m => ‖f x - g x‖) lam := by
    simpa using hfg_mem.integrable_norm_rpow one_ne_zero ENNReal.one_ne_top
  exact (integral_mono_measure (μ := μ) (ν := lam) (Measure.le_add_right le_rfl)
    (ae_of_all _ fun x => norm_nonneg (f x - g x)) hfi).trans h_int_lam

/--
Second analytic target: extend equality from Schwartz tests to all compactly
supported continuous real tests.

The proof approximates `f : C_c(E, ℝ)` in `L¹(μ + ν)` by smooth compactly
supported functions, uses the previous Schwartz bridge on the approximants, and
lets the approximation error tend to zero.
-/
private theorem compactlySupported_integral_eq_of_schwartz_integral_eq
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h :
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ x, φ x ∂μ = ∫ x, φ x ∂ν)
    (f : CompactlySupportedContinuousMap (OddSpace m) ℝ) :
    ∫ x, f x ∂μ = ∫ x, f x ∂ν := by
  apply eq_of_forall_dist_le
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨g, hgcs, hgsm, happrox⟩ :=
    f.hasCompactSupport.exist_eLpNorm_sub_le_of_continuous
      (μ := μ + ν) ENNReal.one_ne_top hε₂ f.continuous
  have hgcont : Continuous g := hgsm.continuous
  have hdist_mu :
      dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) ≤ ε / 2 := by
    have hf_int : Integrable (fun x : OddSpace m => f x) μ :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hg_int : Integrable g μ := hgcont.integrable_of_hasCompactSupport hgcs
    calc
      dist (∫ x, f x ∂μ) (∫ x, g x ∂μ)
          = ‖∫ x : OddSpace m, f x - g x ∂μ‖ := by
              rw [dist_eq_norm, ← integral_sub hf_int hg_int]
      _ ≤ ∫ x : OddSpace m, ‖f x - g x‖ ∂μ :=
              norm_integral_le_integral_norm (fun x : OddSpace m => f x - g x)
      _ ≤ ε / 2 := by
              exact integral_norm_sub_le_of_eLpNorm_one_le m μ ν (fun x => f x) g
                f.hasCompactSupport f.continuous hgcs hgcont hε₂ happrox
  have hdist_nu :
      dist (∫ x, f x ∂ν) (∫ x, g x ∂ν) ≤ ε / 2 := by
    have hf_int : Integrable (fun x : OddSpace m => f x) ν :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hg_int : Integrable g ν := hgcont.integrable_of_hasCompactSupport hgcs
    calc
      dist (∫ x, f x ∂ν) (∫ x, g x ∂ν)
          = ‖∫ x : OddSpace m, f x - g x ∂ν‖ := by
              rw [dist_eq_norm, ← integral_sub hf_int hg_int]
      _ ≤ ∫ x : OddSpace m, ‖f x - g x‖ ∂ν :=
              norm_integral_le_integral_norm (fun x : OddSpace m => f x - g x)
      _ ≤ ε / 2 := by
              exact integral_norm_sub_le_of_eLpNorm_one_le m ν μ (fun x => f x) g
                f.hasCompactSupport f.continuous hgcs hgcont hε₂
                (by simpa [add_comm] using happrox)
  have hg_eq : ∫ x, g x ∂μ = ∫ x, g x ∂ν :=
    smooth_compactSupport_integral_eq_of_schwartz_integral_eq m μ ν h hgcs hgsm
  have hdist_g : dist (∫ x, g x ∂μ) (∫ x, g x ∂ν) = 0 := by
    rw [hg_eq, dist_self]
  calc
    dist (∫ x, f x ∂μ) (∫ x, f x ∂ν)
        ≤ dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) +
            dist (∫ x, g x ∂μ) (∫ x, f x ∂ν) := dist_triangle _ _ _
    _ ≤ dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) +
          (dist (∫ x, g x ∂μ) (∫ x, g x ∂ν) +
            dist (∫ x, g x ∂ν) (∫ x, f x ∂ν)) := by
            gcongr
            exact dist_triangle _ _ _
    _ = dist (∫ x, f x ∂μ) (∫ x, g x ∂μ) +
          dist (∫ x, g x ∂ν) (∫ x, f x ∂ν) := by
            rw [hdist_g, zero_add]
    _ ≤ ε / 2 + ε / 2 := by
            exact add_le_add hdist_mu (by simpa [dist_comm] using hdist_nu)
    _ = ε := by ring

theorem measure_eq_of_schwartz_integral_eq
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h :
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) :
    μ = ν := by
  exact Measure.ext_of_integral_eq_on_compactlySupported
    (compactlySupported_integral_eq_of_schwartz_integral_eq m μ ν h)

/--
Subproject replacement for the current axiom's measure-level endpoint.
-/
theorem measure_eq_of_averageDistance_eq_odd
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y) :
    μ = ν := by
  exact measure_eq_of_schwartz_integral_eq m μ ν
    (schwartz_integral_eq_of_averageDistance_eq_odd m μ ν havg)

/--
The exact replacement theorem for the axiom in `Inversion.lean`.

Once the two analytic targets above are proved, this theorem can be copied back
to `Inversion.lean` in place of the axiom.
-/
theorem averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y)
    (g : BoundedContinuousFunction (OddSpace m) NNReal) :
    ∫⁻ x, (g x : ENNReal) ∂μ = ∫⁻ x, (g x : ENNReal) ∂ν := by
  rw [measure_eq_of_averageDistance_eq_odd m μ ν havg]

end CramerWoldTheorem.OddInversion
