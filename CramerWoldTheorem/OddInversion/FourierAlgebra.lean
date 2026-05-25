import OddInversion.Basic

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

/-- Fourier-side multiplication by `‖ξ‖²` on tempered distributions. -/
noncomputable def fourierNormSqMultiplier
    (m : ℕ) : 𝓢'(OddSpace m, ℂ) →L[ℂ] 𝓢'(OddSpace m, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ
    (fun ξ : OddSpace m => Complex.ofReal (‖ξ‖ ^ 2))

/-- A single distributional Laplacian becomes multiplication by `-(2π)^2 ‖ξ‖²`
after Fourier transform. -/
lemma fourier_laplacian_eq_smulLeftCLM_normSq
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
lemma fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
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
lemma iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow
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
Reverse bridge from the classical distributional fundamental-solution identity
to the Fourier multiplier formulation.  This is independent of the particular
kernel; the hard input is only `Δ^(m+1) T = c δ₀`.
-/
theorem fourier_multiplier_power_eq_constDistribution_of_distributional_identity
    (m : ℕ) (T : 𝓢'(OddSpace m, ℂ))
    (h :
      ∃ c : ℂ, c ≠ 0 ∧
        ((Laplacian.laplacian^[m + 1]) T =
          c • TemperedDistribution.delta (0 : OddSpace m))) :
    ∃ c : ℂ, c ≠ 0 ∧
      TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 T) =
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
      (𝓕 T)
  have hfourier :
      𝓕 ((Laplacian.laplacian^[m + 1]) T) =
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
              (((fourierNormSqMultiplier m)^[m + 1]) (𝓕 T)) := by
              congr 1
              exact (iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow
                m (m + 1) (𝓕 T)).symm
      _ = 𝓕 ((Laplacian.laplacian^[m + 1]) T) := by
              exact (fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
                m (m + 1) T).symm
      _ = c • ((volume : Measure (OddSpace m)).toTemperedDistribution :
            𝓢'(OddSpace m, ℂ)) := hfourier
  calc
    TemperedDistribution.smulLeftCLM ℂ
        (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
        (𝓕 T)
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

end CramerWoldTheorem.OddInversion
