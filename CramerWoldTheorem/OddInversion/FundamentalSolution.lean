import OddInversion.Kernel
import OddInversion.FourierAlgebra
import OddInversion.Transport

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

/--
Classical odd-dimensional Riesz-kernel identity for the norm kernel.

In dimension `2 * m + 1`, the `(m + 1)`-fold distributional Laplacian of
`x ↦ ‖x‖` is a nonzero dimensional constant times `δ₀`.

The proof uses PhysLean's terminal singular step, formalized in
`PhysLeanBridge.Space.distLaplacian_norm_zpow_boundary_eq_delta`, and the local
bridge infrastructure:

1. prove the distributional gradient formula
   `∇(‖x‖^a) = a ‖x‖^(a-2) x` for the admissible singular powers;
2. iterate the off-origin recurrence
   `Δ(r^a) = a (a + d - 2) r^(a - 2)` until the exponent is `2 - d`;
3. use the spherical-coordinate divergence theorem for
   `div (‖x‖^{-d} x) = vol(S^{d-1}) δ₀`;
4. transport the resulting real distribution statement to complex tempered
   distributions.
-/
theorem normKernel_distributional_laplacian_power_eq_delta
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((Laplacian.laplacian^[m + 1]) (normKernelDistributionAtZero m) =
        c • TemperedDistribution.delta (0 : OddSpace m)) := by
  let e : Space (2 * m + 1) ≃L[ℝ] OddSpace m :=
    ((Space.basis (d := 2 * m + 1)).repr.toContinuousLinearEquiv)
  rcases
    PhysLeanBridge.Space.odd_complexified_laplacian_norm_exists m with
    ⟨c, hc, hspace⟩
  refine ⟨c, hc, ?_⟩
  have hpush := congrArg (PhysLeanBridge.pushForwardTempered e) hspace
  rw [PhysLeanBridge.Space.pushForwardTempered_iterated_laplacian_basis_repr
      (d := 2 * m + 1) (k := m + 1)
      (T := PhysLeanBridge.complexifyRealDistribution
        (PhysLeanBridge.Space.oddNormPowerDistribution m 0))] at hpush
  rw [PhysLeanBridge.Space.pushForward_complexified_oddNormPowerDistribution_zero_eq_normKernel
      (m := m)] at hpush
  rw [PhysLeanBridge.pushForwardTempered_smul,
    PhysLeanBridge.pushForwardTempered_delta_zero] at hpush
  exact hpush

/--
Fourier multiplier form of the same Riesz-kernel identity.

This theorem is proved from the distributional Laplacian identity above by
Mathlib's Fourier-transform API; all remaining analytic content is isolated in
`normKernel_distributional_laplacian_power_eq_delta`.
-/
theorem normKernel_fourier_multiplier_power_eq_constDistribution_core
    (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 (normKernelDistributionAtZero m)) =
          c • ((volume : Measure (OddSpace m)).toTemperedDistribution) := by
  exact fourier_multiplier_power_eq_constDistribution_of_distributional_identity
    m (normKernelDistributionAtZero m)
    (normKernel_distributional_laplacian_power_eq_delta m)

end CramerWoldTheorem.OddInversion
