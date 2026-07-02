/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
import OddInversion.FundamentalSolution
import Physlib.Mathematics.Distribution.Basic

/-!
Proof-focused subproject for replacing
`CramerWoldTheorem.averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal`.

This file is intentionally not imported by `CramerWoldTheorem.Main`.  It gives a
small proof queue for the odd-dimensional inversion fact without adding another
unproved constant to the main development.
-/

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

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
  exact normKernel_fourier_multiplier_power_eq_constDistribution_core m

/--
Radial fundamental-solution pairing, reduced to the Fourier/Riesz multiplier
theorem above.  In dimension `2 * m + 1`, pairing `‖x‖` against the
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

/--
Direct distributional form of the missing radial fundamental-solution theorem.

The norm-kernel distributional PDE identity `Δ^(m+1) ‖x‖ = c_m δ₀`, packaged
with its representing integral.
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

theorem measure_eq_of_schwartz_integral_eq
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h :
      ∀ φ : 𝓢(OddSpace m, ℂ),
        ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) :
    μ = ν := by
  rw [← Physlib.Distribution.ofFiniteMeasure_eq_iff]
  ext φ
  rw [Physlib.Distribution.ofFiniteMeasure_apply,
    Physlib.Distribution.ofFiniteMeasure_apply]
  exact h φ

/-- Measure-level endpoint used by `CramerWoldTheorem/Inversion.lean`. -/
theorem measure_eq_of_averageDistance_eq_odd
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y) :
    μ = ν := by
  exact measure_eq_of_schwartz_integral_eq m μ ν
    (schwartz_integral_eq_of_averageDistance_eq_odd m μ ν havg)

/-- Lintegral endpoint imported by `CramerWoldTheorem/Inversion.lean`. -/
theorem averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal
    (m : ℕ)
    (μ ν : Measure (OddSpace m))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg : ∀ y : OddSpace m, averageDistance μ y = averageDistance ν y)
    (g : BoundedContinuousFunction (OddSpace m) NNReal) :
    ∫⁻ x, (g x : ENNReal) ∂μ = ∫⁻ x, (g x : ENNReal) ∂ν := by
  rw [measure_eq_of_averageDistance_eq_odd m μ ν havg]

end CramerWoldTheorem.OddInversion
