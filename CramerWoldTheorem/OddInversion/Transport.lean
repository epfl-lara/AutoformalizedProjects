import OddInversion.Kernel
import OddInversion.PhysLeanBridge

open Physlib MeasureTheory
open scoped BigOperators ENNReal Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

namespace PhysLeanBridge

/-- Push a tempered distribution forward along a continuous linear equivalence. -/
noncomputable def pushForwardTempered {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (T : 𝓢'(E, ℂ)) : 𝓢'(F, ℂ) :=
  PointwiseConvergenceCLM.precomp _ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) T

@[simp]
lemma pushForwardTempered_apply {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (T : 𝓢'(E, ℂ)) (φ : 𝓢(F, ℂ)) :
    pushForwardTempered e T φ =
      T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ) :=
  rfl

@[simp]
lemma pushForwardTempered_smul {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (c : ℂ) (T : 𝓢'(E, ℂ)) :
    pushForwardTempered e (c • T) = c • pushForwardTempered e T := by
  ext φ
  simp [pushForwardTempered]

lemma pushForwardTempered_delta_zero {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    pushForwardTempered e (TemperedDistribution.delta (0 : E)) =
      TemperedDistribution.delta (0 : F) := by
  ext φ
  rw [pushForwardTempered_apply, TemperedDistribution.delta_apply,
    TemperedDistribution.delta_apply]
  simp

namespace Space

lemma basis_repr_basis (d : ℕ) (i : Fin d) :
    Space.basis.repr (Space.basis i) =
      EuclideanSpace.basisFun (Fin d) ℝ i := by
  ext j
  simp [EuclideanSpace.basisFun_apply]

lemma basis_repr_comp_laplacian (d : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    Laplacian.laplacian
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((Space.basis (d := d)).repr.toContinuousLinearEquiv) φ) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((Space.basis (d := d)).repr.toContinuousLinearEquiv)
        (Laplacian.laplacian φ) := by
  rw [SchwartzMap.laplacian_eq_sum (Space.basis),
    show Laplacian.laplacian φ =
      ∑ i, ∂_{EuclideanSpace.basisFun (Fin d) ℝ i}
        (∂_{EuclideanSpace.basisFun (Fin d) ℝ i} φ) from
      SchwartzMap.laplacian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ) φ]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  have hb :
      ((Space.basis (d := d)).repr.toContinuousLinearEquiv) (Space.basis i) =
        EuclideanSpace.basisFun (Fin d) ℝ i :=
    basis_repr_basis d i
  rw [hb]

lemma basis_repr_comp_iterated_laplacian (d k : ℕ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) :
    ((Laplacian.laplacian^[k])
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          ((Space.basis (d := d)).repr.toContinuousLinearEquiv) φ)) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        ((Space.basis (d := d)).repr.toContinuousLinearEquiv)
        ((Laplacian.laplacian^[k]) φ) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih]
      rw [basis_repr_comp_laplacian d]

lemma pushForwardTempered_laplacian_basis_repr (d : ℕ) (T : 𝓢'(Space d, ℂ)) :
    pushForwardTempered ((Space.basis (d := d)).repr.toContinuousLinearEquiv)
        (Laplacian.laplacian T) =
      Laplacian.laplacian
        (pushForwardTempered ((Space.basis (d := d)).repr.toContinuousLinearEquiv) T) := by
  ext φ
  rw [TemperedDistribution.laplacian_apply_apply]
  rw [pushForwardTempered_apply, pushForwardTempered_apply]
  rw [TemperedDistribution.laplacian_apply_apply]
  rw [basis_repr_comp_laplacian d]

lemma pushForwardTempered_iterated_laplacian_basis_repr
    (d k : ℕ) (T : 𝓢'(Space d, ℂ)) :
    pushForwardTempered ((Space.basis (d := d)).repr.toContinuousLinearEquiv)
        ((Laplacian.laplacian^[k]) T) =
      ((Laplacian.laplacian^[k])
        (pushForwardTempered ((Space.basis (d := d)).repr.toContinuousLinearEquiv) T)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [pushForwardTempered_laplacian_basis_repr d]
      rw [ih]

set_option linter.flexible false in
lemma pushForward_complexified_oddNormPowerDistribution_zero_eq_normKernel
    (m : ℕ) :
    pushForwardTempered
        ((Space.basis (d := 2 * m + 1)).repr.toContinuousLinearEquiv)
        (complexifyRealDistribution (oddNormPowerDistribution m 0)) =
      normKernelDistributionAtZero m := by
  ext φ
  let e : Space (2 * m + 1) ≃L[ℝ] OddSpace m :=
    ((Space.basis (d := 2 * m + 1)).repr.toContinuousLinearEquiv)
  let ψ : 𝓢(Space (2 * m + 1), ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e φ
  have hψ_apply : ∀ x, ψ x = φ (e x) := by
    intro x
    rfl
  have hnorm_e : ∀ x : Space (2 * m + 1), ‖e x‖ = ‖x‖ := by
    intro x
    simp [e]
  have hmp : MeasurePreserving e volume volume := by
    simpa [e] using
      ((Space.basis (d := 2 * m + 1)).measurePreserving_repr)
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  let Fspace : Space (2 * m + 1) → ℂ := fun x => (‖x‖ : ℂ) * ψ x
  let Fodd : OddSpace m → ℂ := fun y => (‖y‖ : ℂ) * φ y
  have hFspace_eq : Fspace = Fodd ∘ e := by
    funext x
    simp [Fspace, Fodd, hψ_apply, hnorm_e x]
  have hFodd_int : Integrable Fodd := by
    simpa [Fodd] using norm_mul_schwartz_integrable m φ
  have hFspace_int : Integrable Fspace := by
    rw [hFspace_eq]
    exact (hmp.integrable_comp_emb hemb).2 hFodd_int
  have h_integral_push :
      ∫ x : Space (2 * m + 1), Fspace x =
        ∫ y : OddSpace m, Fodd y := by
    rw [hFspace_eq]
    exact hmp.integral_comp hemb Fodd
  calc
    pushForwardTempered e (complexifyRealDistribution (oddNormPowerDistribution m 0)) φ
        = complexifyRealDistribution (oddNormPowerDistribution m 0) ψ := by
            rfl
    _ = (∫ x : Space (2 * m + 1), (Fspace x).re) +
          Complex.I * (∫ x : Space (2 * m + 1), (Fspace x).im) := by
            rw [complexifyRealDistribution_apply, oddNormPowerDistribution_zero]
            have hre :
                (∫ x : Space (2 * m + 1), (φ (e x)).re * ‖x‖) =
                  ∫ x : Space (2 * m + 1), ‖x‖ * (φ (e x)).re := by
              apply integral_congr_ae
              filter_upwards with x
              ring
            have him :
                (∫ x : Space (2 * m + 1), (φ (e x)).im * ‖x‖) =
                  ∫ x : Space (2 * m + 1), ‖x‖ * (φ (e x)).im := by
              apply integral_congr_ae
              filter_upwards with x
              ring
            simp [_root_.Space.distOfFunction_apply, Fspace, ψ, Complex.mul_re,
              Complex.mul_im]
            rw [hre, him]
    _ = ∫ x : Space (2 * m + 1), Fspace x := by
            calc
              ((↑(∫ x : Space (2 * m + 1), (Fspace x).re) : ℂ) +
                    Complex.I * ↑(∫ x : Space (2 * m + 1), (Fspace x).im))
                  = (↑(∫ x : Space (2 * m + 1), (Fspace x).re) : ℂ) +
                      ↑(∫ x : Space (2 * m + 1), (Fspace x).im) * Complex.I := by
                    ring
              _ = ∫ x : Space (2 * m + 1), Fspace x := by
                    exact integral_re_add_im hFspace_int
    _ = ∫ y : OddSpace m, Fodd y := h_integral_push
    _ = normKernelDistributionAtZero m φ := by
            rw [normKernelDistributionAtZero_apply]

end Space

end PhysLeanBridge

end CramerWoldTheorem.OddInversion
