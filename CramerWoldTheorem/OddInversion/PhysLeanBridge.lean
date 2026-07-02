import Physlib.SpaceAndTime.Space.Norm.Basic
import Physlib.Mathematics.Distribution.PowMul
import Mathlib.Analysis.Distribution.TemperedDistribution

open Physlib MeasureTheory
open Filter
open scoped BigOperators SchwartzMap Topology Laplacian LineDeriv

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CramerWoldTheorem.OddInversion.PhysLeanBridge

/--
Complexification of a PhysLean real distribution.

For a real distribution `U`, this sends a complex Schwartz test function `φ`
to `U (re φ) + i U (im φ)`.  This is the basic bridge from PhysLean's
real-distribution API to Mathlib's complex tempered-distribution API.
-/
noncomputable def complexifyRealDistribution {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E→d[ℝ] ℝ) : 𝓢'(E, ℂ) :=
  ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ <|
    { toFun φ := (U (φ.postcompCLM Complex.reCLM) : ℂ) +
        Complex.I * (U (φ.postcompCLM Complex.imCLM) : ℂ)
      map_add' φ ψ := by
        simp
        ring
      map_smul' a φ := by
        have hre : ((a • φ).postcompCLM Complex.reCLM) =
            a.re • (φ.postcompCLM Complex.reCLM) -
              a.im • (φ.postcompCLM Complex.imCLM) := by
          ext x
          simp [Complex.mul_re]
        have him : ((a • φ).postcompCLM Complex.imCLM) =
            a.re • (φ.postcompCLM Complex.imCLM) +
              a.im • (φ.postcompCLM Complex.reCLM) := by
          ext x
          simp [Complex.mul_im]
        rw [hre, him]
        simp only [map_sub, map_smul, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul,
          map_add, Complex.ofReal_add, RingHom.id_apply]
        apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
      cont := by
        fun_prop }

@[simp]
lemma complexifyRealDistribution_apply {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E→d[ℝ] ℝ) (φ : 𝓢(E, ℂ)) :
    complexifyRealDistribution U φ =
      (U (φ.postcompCLM Complex.reCLM) : ℂ) +
        Complex.I * (U (φ.postcompCLM Complex.imCLM) : ℂ) :=
  rfl

@[simp]
lemma complexifyRealDistribution_smul {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (U : E→d[ℝ] ℝ) :
    complexifyRealDistribution (c • U) =
      (c : ℂ) • complexifyRealDistribution U := by
  ext φ
  change complexifyRealDistribution (c • U) φ =
    (c : ℂ) * complexifyRealDistribution U φ
  rw [complexifyRealDistribution_apply, complexifyRealDistribution_apply]
  have hRe :
      (c • U) (φ.postcompCLM Complex.reCLM) =
        c * U (φ.postcompCLM Complex.reCLM) := rfl
  have hIm :
      (c • U) (φ.postcompCLM Complex.imCLM) =
        c * U (φ.postcompCLM Complex.imCLM) := rfl
  rw [hRe, hIm]
  rw [Complex.ofReal_mul, Complex.ofReal_mul]
  ring_nf

@[simp]
lemma complexifyRealDistribution_diracDelta {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E) :
    complexifyRealDistribution (Physlib.Distribution.diracDelta ℝ a) =
      TemperedDistribution.delta a := by
  ext φ
  rw [complexifyRealDistribution_apply, TemperedDistribution.delta_apply]
  simp [Complex.ext_iff]

namespace Space

private lemma integrable_isDistBounded_mul_schwartzMap_spherical {dm1 : ℕ}
    {f : Space dm1.succ → ℝ}
    (hf : Space.IsDistBounded f) (η : 𝓢(Space dm1.succ, ℝ)) :
    Integrable ((fun x => η x.1 * f x.1)
      ∘ (homeomorphUnitSphereProd (Space dm1.succ)).symm)
      ((volume (α := Space dm1.succ)).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ (Space dm1.succ) - 1))) := by
  have h1 : Integrable ((fun x => η x.1 * f x.1))
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume) := by
    change Integrable ((fun x => η x * f x) ∘ Subtype.val)
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume)
    rw [← MeasureTheory.integrableOn_iff_comap_subtypeVal]
    · exact (hf.integrable_space_mul η).integrableOn
    · simp
  have he := (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := Space dm1.succ)))
  rw [← he.integrable_comp_emb]
  · convert h1
    simp only [Nat.succ_eq_add_one, Function.comp_apply, Homeomorph.symm_apply_apply]
  · exact Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (Space dm1.succ))

private lemma integrable_real_pow_mul_schwartz
    (ψ : 𝓢(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * ψ x) volume := by
  refine (ψ.integrable_pow_mul volume k).mono' (by fun_prop) ?_
  filter_upwards with x
  simp [norm_mul, norm_pow]

private lemma radial_power_deriv_integral_by_parts
    {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (n : ↑(Metric.sphere (0 : Space d.succ) 1))
    (p : ℕ) (hp : 0 < p) :
    - ∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
        ∂(.comap Subtype.val volume)
      =
      (p : ℝ) * ∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ (p - 1) * η (r.1 • n.1)
        ∂(.comap Subtype.val volume) := by
  let η' : 𝓢(ℝ, ℝ) := SchwartzMap.compCLM (g := fun a => a • n.1) ℝ (by
    apply And.intro
    · fun_prop
    · intro n'
      match n' with
      | 0 =>
        use 1, 1
        simp [norm_smul]
      | 1 =>
        use 0, 1
        intro x
        simp [fderiv_smul_const, iteratedFDeriv_succ_eq_comp_right,
          ContinuousLinearMap.norm_id]
      | n' + 1 + 1 =>
        use 0, 0
        intro x
        simp only [Real.norm_eq_abs, pow_zero, mul_one, norm_le_zero_iff]
        rw [iteratedFDeriv_succ_eq_comp_right]
        conv_lhs =>
          enter [2, 3, y]
          simp [fderiv_smul_const]
        rw [iteratedFDeriv_succ_const]
        rfl) (by use 1, 1; simp [norm_smul]) η
  have hη'_apply (x : ℝ) : η' x = η (x • n.1) := by
    simp [η']
  have hmul_iter_apply :
      ∀ k x, ((Physlib.Distribution.powOneMul ℝ)^[k] η') x = x ^ k * η' x := by
    intro k
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply']
        rw [Physlib.Distribution.powOneMul_apply, ih]
        rw [pow_succ]
        change x * (x ^ k * η' x) = x ^ k * x * η' x
        ring
  have hleft_subtype :
      ∫ (r : Set.Ioi (0 : ℝ)),
          r.1 ^ p * _root_.deriv (fun a => η (a • n.1)) r.1
          ∂(.comap Subtype.val volume)
        =
        ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ p * _root_.deriv (fun a => η (a • n.1)) x := by
    exact MeasureTheory.integral_subtype_comap (μ := volume)
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (fun x : ℝ => x ^ p * _root_.deriv (fun a => η (a • n.1)) x)
  have hright_subtype :
      ∫ (r : Set.Ioi (0 : ℝ)),
          r.1 ^ (p - 1) * η (r.1 • n.1)
          ∂(.comap Subtype.val volume)
        =
        ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ (p - 1) * η (x • n.1) := by
    exact MeasureTheory.integral_subtype_comap (μ := volume)
      (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
      (fun x : ℝ => x ^ (p - 1) * η (x • n.1))
  rw [hleft_subtype, hright_subtype]
  have hIBP :
      ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ p * _root_.deriv (fun a => η (a • n.1)) x
        =
        (0 : ℝ) - (0 : ℝ) -
          ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
            ((p : ℝ) * x ^ (p - 1)) * η (x • n.1) := by
    refine MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ))
      (u := fun x : ℝ => x ^ p)
      (u' := fun x : ℝ => (p : ℝ) * x ^ (p - 1))
      (v := fun x : ℝ => η (x • n.1))
      (v' := fun x : ℝ => _root_.deriv (fun a => η (a • n.1)) x)
      (a' := (0 : ℝ)) (b' := (0 : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simpa using (hasDerivAt_pow p x)
    · intro x hx
      exact DifferentiableAt.hasDerivAt (by fun_prop :
        DifferentiableAt ℝ (fun x : ℝ => η (x • n.1)) x)
    · have hderiv_int :
          Integrable (fun x : ℝ =>
            x ^ p * ((SchwartzMap.derivCLM ℝ ℝ) η') x) volume :=
        integrable_real_pow_mul_schwartz ((SchwartzMap.derivCLM ℝ ℝ) η') p
      exact hderiv_int.integrableOn.congr_fun (by
        intro x hx
        have hderiv_eq :
            _root_.deriv η' x = _root_.deriv (fun a => η (a • n.1)) x := by
          congr 1
        simp [SchwartzMap.derivCLM_apply, hderiv_eq])
        measurableSet_Ioi
    · have hbase :
          Integrable (fun x : ℝ => x ^ (p - 1) * η' x) volume :=
        integrable_real_pow_mul_schwartz η' (p - 1)
      have hconst :
          Integrable (fun x : ℝ => (p : ℝ) * (x ^ (p - 1) * η' x)) volume :=
        hbase.const_mul (p : ℝ)
      exact hconst.integrableOn.congr_fun (by
        intro x hx
        ring_nf
        simp [hη'_apply, mul_assoc])
        measurableSet_Ioi
    · have hcont :
          ContinuousAt (fun x : ℝ => x ^ p * η (x • n.1)) (0 : ℝ) := by
        fun_prop
      have hlim := tendsto_nhdsWithin_of_tendsto_nhds
        (s := Set.Ioi (0 : ℝ)) hcont.tendsto
      change Filter.Tendsto (fun x : ℝ => x ^ p * η (x • n.1))
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ))
      simpa [Pi.mul_apply, hη'_apply, hp.ne'] using hlim
    · have hzero :
          Filter.Tendsto (fun x : ℝ => x ^ p * η' x) atTop (𝓝 (0 : ℝ)) := by
        have hsch :
            Filter.Tendsto (fun x : ℝ => ((Physlib.Distribution.powOneMul ℝ)^[p] η') x)
              atTop (𝓝 (0 : ℝ)) :=
          Filter.Tendsto.mono_left
            (((Physlib.Distribution.powOneMul ℝ)^[p] η').toZeroAtInfty.zero_at_infty')
            atTop_le_cocompact
        exact hsch.congr' (Eventually.of_forall (fun x => by
          rw [hmul_iter_apply p x]))
      change Filter.Tendsto (fun x : ℝ => x ^ p * η (x • n.1)) atTop (𝓝 (0 : ℝ))
      simpa [hη'_apply, Pi.mul_apply] using hzero
  calc
    -∫ (x : ℝ) in Set.Ioi (0 : ℝ),
        x ^ p * _root_.deriv (fun a => η (a • n.1)) x
        = ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
            ((p : ℝ) * x ^ (p - 1)) * η (x • n.1) := by
          rw [hIBP]
          ring
    _ = (p : ℝ) * ∫ (x : ℝ) in Set.Ioi (0 : ℝ),
          x ^ (p - 1) * η (x • n.1) := by
          rw [← integral_const_mul]
          congr
          funext x
          ring

set_option maxHeartbeats 800000 in
-- The spherical-coordinate integration-by-parts calculation is long and otherwise times out.
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
set_option linter.unnecessarySimpa false in
lemma distDiv_norm_zpow_smul_repr_self_eq_smul
    {d : ℕ} (q : ℤ) (hq : 0 < q + (d.succ : ℤ)) :
    Space.distDiv (Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ q • Space.basis.repr x)
      (Space.IsDistBounded.zpow_smul_repr_self q (by omega))) =
      (((q + (d.succ : ℤ) : ℤ) : ℝ) •
        Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ q)
          (Space.IsDistBounded.pow q (by omega))) := by
  ext η
  let p : ℕ := Int.toNat (q + (d.succ : ℤ))
  have hp_int : (p : ℤ) = q + (d.succ : ℤ) := by
    dsimp [p]
    exact Int.toNat_of_nonneg (le_of_lt hq)
  have hp_pos : 0 < p := by
    have : (0 : ℤ) < (p : ℤ) := by
      rw [hp_int]
      exact hq
    exact_mod_cast this
  let F : Space d.succ → ℝ := fun x =>
    inner ℝ (‖x‖ ^ q • Space.basis.repr x) (Space.grad η x)
  calc _
    _ = - ∫ x, F x := by
          rw [Space.distDiv_ofFunction]
    _ = - ∫ r, F (r.2.1 • r.1.1)
        ∂(volume (α := Space d.succ).toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
          rw [Space.integral_volume_eq_spherical]
    _ = - ∫ n, (∫ r, F (r.1 • n.1)
        ∂(Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1)))
        ∂(volume (α := Space d.succ).toSphere) := by
          rw [MeasureTheory.integral_prod]
          convert Space.integrable_isDistBounded_inner_grad_schwartzMap_spherical
            (Space.IsDistBounded.zpow_smul_repr_self q (by omega)) η using 1
          ext r
          simp [F]
    _ = - ∫ n, (∫ (r : Set.Ioi (0 : ℝ)),
        r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
        ∂(.comap Subtype.val volume))
        ∂(volume (α := Space d.succ).toSphere) := by
          congr
          funext n
          simp [F, Measure.volumeIoiPow]
          erw [integral_withDensity_eq_integral_smul (by fun_prop)]
          · congr
            funext r
            have hr : 0 < (r : ℝ) := by exact r.2
            have hnr : ‖(n : Space d.succ)‖ = 1 := by
              simpa [Metric.mem_sphere, dist_eq_norm] using n.2
            have hnorm : ‖((r : ℝ) • (n : Space d.succ))‖ = (r : ℝ) := by
              simp [norm_smul, hnr, abs_of_nonneg (le_of_lt hr)]
            rw [NNReal.smul_def]
            rw [Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) d)]
            · simp only [smul_eq_mul]
              rw [hnorm]
              have hderiv :
                  inner ℝ (Space.basis.repr (n : Space d.succ))
                      (Space.grad (⇑η) ((r : ℝ) • (n : Space d.succ))) =
                    _root_.deriv (fun a => η (a • (n : Space d.succ))) (r : ℝ) := by
                let x : Space d.succ := (r : ℝ) • (n : Space d.succ)
                have hxnorm : ‖x‖ = (r : ℝ) := by
                  dsimp [x]
                  exact hnorm
                have hxinv : ‖x‖⁻¹ • x = (n : Space d.succ) := by
                  dsimp [x]
                  rw [hxnorm, smul_smul]
                  field_simp [ne_of_gt hr]
                  simp
                have hunit :
                    ‖x‖⁻¹ • Space.basis.repr x =
                      Space.basis.repr (n : Space d.succ) := by
                  rw [← map_smul, hxinv]
                have h := Space.grad_inner_space_unit_vector x (⇑η)
                  (SchwartzMap.differentiable η)
                rw [hunit] at h
                rw [hxnorm] at h
                have hfun :
                    (fun r_1 : ℝ => η (r_1 • ((r : ℝ)⁻¹) • x)) =
                      (fun a => η (a • (n : Space d.succ))) := by
                  funext a
                  rw [← hxinv]
                  rw [hxnorm]
                rw [hfun] at h
                simpa [real_inner_comm] using h
              rw [← hderiv]
              simp only [inner_smul_left]
              have hpow :
                  (r : ℝ) ^ d * ((r : ℝ) ^ q * (r : ℝ)) =
                    (r : ℝ) ^ p := by
                have hz : (r : ℝ) ≠ 0 := ne_of_gt hr
                calc
                  (r : ℝ) ^ d * ((r : ℝ) ^ q * (r : ℝ))
                      = (r : ℝ) ^ (d : ℤ) *
                          ((r : ℝ) ^ q * (r : ℝ) ^ (1 : ℤ)) := by
                            rw [zpow_natCast, zpow_one]
                  _ = (r : ℝ) ^ ((d : ℤ) + (q + 1)) := by
                            rw [← zpow_add₀ hz q 1, ← zpow_add₀ hz (d : ℤ) (q + 1)]
                  _ = (r : ℝ) ^ (p : ℤ) := by
                            congr 1
                            omega
                  _ = (r : ℝ) ^ p := by
                            rw [zpow_natCast]
              calc
                (r : ℝ) ^ d * ((r : ℝ) ^ q *
                    ((r : ℝ) *
                      inner ℝ (Space.basis.repr (n : Space d.succ))
                        (Space.grad (⇑η) ((r : ℝ) • (n : Space d.succ)))))
                    = ((r : ℝ) ^ d * ((r : ℝ) ^ q * (r : ℝ))) *
                        inner ℝ (Space.basis.repr (n : Space d.succ))
                          (Space.grad (⇑η) ((r : ℝ) • (n : Space d.succ))) := by
                        ring
                _ = (r : ℝ) ^ p *
                    inner ℝ (Space.basis.repr (n : Space d.succ))
                      (Space.grad (⇑η) ((r : ℝ) • (n : Space d.succ))) := by
                        rw [hpow]
    _ = (((q + (d.succ : ℤ) : ℤ) : ℝ) •
        Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ q)
          (Space.IsDistBounded.pow q (by omega))) η := by
      have hcoef : (((q + (d.succ : ℤ) : ℤ) : ℝ)) = (p : ℝ) := by
        exact_mod_cast hp_int.symm
      have hspherical :
          ∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
              ∫ (r : Set.Ioi (0 : ℝ)),
                r.1 ^ (p - 1) * η (r.1 • n.1)
                ∂(.comap Subtype.val volume)
              ∂(volume (α := Space d.succ).toSphere)
            =
          ∫ x : Space d.succ, η x * ‖x‖ ^ q := by
        symm
        calc
          ∫ x : Space d.succ, η x * ‖x‖ ^ q
              = ∫ r, η (r.2.1 • r.1.1) * ‖r.2.1 • r.1.1‖ ^ q
                  ∂(volume (α := Space d.succ).toSphere.prod
                    (Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))) := by
                rw [Space.integral_volume_eq_spherical]
          _ = ∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
                ∫ r, η (r.1 • n.1) * ‖r.1 • n.1‖ ^ q
                  ∂(Measure.volumeIoiPow (Module.finrank ℝ (Space d.succ) - 1))
                ∂(volume (α := Space d.succ).toSphere) := by
                rw [MeasureTheory.integral_prod]
                convert integrable_isDistBounded_mul_schwartzMap_spherical
                  (Space.IsDistBounded.pow q (by omega)) η using 1
                ext r
                simp
          _ = ∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
                ∫ (r : Set.Ioi (0 : ℝ)),
                  r.1 ^ (p - 1) * η (r.1 • n.1)
                  ∂(.comap Subtype.val volume)
                ∂(volume (α := Space d.succ).toSphere) := by
                congr
                funext n
                simp [Measure.volumeIoiPow]
                erw [integral_withDensity_eq_integral_smul (by fun_prop)]
                congr
                funext r
                have hr : 0 < (r : ℝ) := by exact r.2
                have hnr : ‖(n : Space d.succ)‖ = 1 := by
                  simpa [Metric.mem_sphere, dist_eq_norm] using n.2
                have hnorm : ‖((r : ℝ) • (n : Space d.succ))‖ = (r : ℝ) := by
                  simp [norm_smul, hnr, abs_of_nonneg (le_of_lt hr)]
                have hpow :
                    (r : ℝ) ^ d * (r : ℝ) ^ q = (r : ℝ) ^ (p - 1) := by
                  have hz : (r : ℝ) ≠ 0 := ne_of_gt hr
                  calc
                    (r : ℝ) ^ d * (r : ℝ) ^ q
                        = (r : ℝ) ^ ((d : ℤ) + q) := by
                            rw [← zpow_natCast (r : ℝ) d, ← zpow_add₀ hz (d : ℤ) q]
                    _ = (r : ℝ) ^ ((p - 1 : ℕ) : ℤ) := by
                            congr 1
                            omega
                    _ = (r : ℝ) ^ (p - 1) := by
                            rw [zpow_natCast]
                rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) d)]
                simp only [smul_eq_mul]
                rw [hnorm]
                calc
                  (r : ℝ) ^ d * (η ((r : ℝ) • (n : Space d.succ)) * (r : ℝ) ^ q)
                      = ((r : ℝ) ^ d * (r : ℝ) ^ q) *
                          η ((r : ℝ) • (n : Space d.succ)) := by
                          ring
                  _ = (r : ℝ) ^ (p - 1) *
                      η ((r : ℝ) • (n : Space d.succ)) := by
                          rw [hpow]
      calc
        -∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
            ∫ (r : Set.Ioi (0 : ℝ)),
              r.1 ^ p * (_root_.deriv (fun a => η (a • n.1)) r.1)
              ∂(.comap Subtype.val volume)
            ∂(volume (α := Space d.succ).toSphere)
            = ∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
                (p : ℝ) * ∫ (r : Set.Ioi (0 : ℝ)),
                  r.1 ^ (p - 1) * η (r.1 • n.1)
                  ∂(.comap Subtype.val volume)
                ∂(volume (α := Space d.succ).toSphere) := by
              rw [← integral_neg]
              congr
              funext n
              exact radial_power_deriv_integral_by_parts η n p hp_pos
        _ = (p : ℝ) * ∫ (n : ↑(Metric.sphere (0 : Space d.succ) 1)),
                ∫ (r : Set.Ioi (0 : ℝ)),
                  r.1 ^ (p - 1) * η (r.1 • n.1)
                  ∂(.comap Subtype.val volume)
                ∂(volume (α := Space d.succ).toSphere) := by
              rw [integral_const_mul]
        _ = (p : ℝ) * ∫ x : Space d.succ, η x * ‖x‖ ^ q := by
              rw [hspherical]
        _ = (((q + (d.succ : ℤ) : ℤ) : ℝ) •
            Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ q)
              (Space.IsDistBounded.pow q (by omega))) η := by
              simp [Space.distOfFunction_apply, mul_comm]
              left
              rw [← hcoef]
              norm_num

/-- PhysLean's real distributional Laplacian on `Space d`. -/
noncomputable def distLaplacian {d : ℕ} :
    ((Space d)→d[ℝ] ℝ) →ₗ[ℝ] (Space d)→d[ℝ] ℝ :=
  Space.distDiv.comp Space.distGrad

lemma distLaplacian_apply {d : ℕ}
    (T : (Space d)→d[ℝ] ℝ) (η : 𝓢(Space d, ℝ)) :
    distLaplacian T η = T (Laplacian.laplacian η) := by
  rw [SchwartzMap.laplacian_eq_sum (Space.basis)]
  rw [map_sum]
  unfold distLaplacian
  rw [LinearMap.comp_apply]
  rw [Space.distDiv_apply_eq_sum_fderivD]
  congr
  funext i
  rw [Distribution.fderivD_apply]
  simp only [WithLp.ofLp_neg, Pi.neg_apply]
  rw [Space.distGrad_apply]
  change -((Space.distDeriv i) T
    ((SchwartzMap.evalCLM ℝ (Space d) ℝ (Space.basis i))
      ((SchwartzMap.fderivCLM ℝ (Space d) ℝ) η))) =
    T (∂_{Space.basis i} (∂_{Space.basis i} η))
  rw [Space.distDeriv_apply]
  rw [Distribution.fderivD_apply]
  simp only [neg_neg]
  congr 1

lemma postcomp_re_lineDeriv {d : ℕ} (v : Space d) (φ : 𝓢(Space d, ℂ)) :
    (∂_{v} φ).postcompCLM Complex.reCLM =
      ∂_{v} (φ.postcompCLM Complex.reCLM) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply]
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change Complex.reCLM ((fderiv ℝ (fun y : Space d => φ y) x) v) =
    (fderiv ℝ (fun y : Space d => Complex.reCLM (φ y)) x) v
  rw [fderiv_clm_apply
    (c := fun _ : Space d => Complex.reCLM)
    (u := fun y : Space d => φ y)]
  · rw [fderiv_const_apply]
    simp
  · fun_prop
  · exact SchwartzMap.differentiable φ x

lemma postcomp_im_lineDeriv {d : ℕ} (v : Space d) (φ : 𝓢(Space d, ℂ)) :
    (∂_{v} φ).postcompCLM Complex.imCLM =
      ∂_{v} (φ.postcompCLM Complex.imCLM) := by
  ext x
  simp only [SchwartzMap.postcompCLM_apply]
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change Complex.imCLM ((fderiv ℝ (fun y : Space d => φ y) x) v) =
    (fderiv ℝ (fun y : Space d => Complex.imCLM (φ y)) x) v
  rw [fderiv_clm_apply
    (c := fun _ : Space d => Complex.imCLM)
    (u := fun y : Space d => φ y)]
  · rw [fderiv_const_apply]
    simp
  · fun_prop
  · exact SchwartzMap.differentiable φ x

lemma postcomp_re_laplacian {d : ℕ} (φ : 𝓢(Space d, ℂ)) :
    (Laplacian.laplacian φ).postcompCLM Complex.reCLM =
      Laplacian.laplacian (φ.postcompCLM Complex.reCLM) := by
  rw [SchwartzMap.laplacian_eq_sum (Space.basis),
    SchwartzMap.laplacian_eq_sum (Space.basis)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [postcomp_re_lineDeriv (φ := ∂_{Space.basis i} φ),
    postcomp_re_lineDeriv (φ := φ)]

lemma postcomp_im_laplacian {d : ℕ} (φ : 𝓢(Space d, ℂ)) :
    (Laplacian.laplacian φ).postcompCLM Complex.imCLM =
      Laplacian.laplacian (φ.postcompCLM Complex.imCLM) := by
  rw [SchwartzMap.laplacian_eq_sum (Space.basis),
    SchwartzMap.laplacian_eq_sum (Space.basis)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [postcomp_im_lineDeriv (φ := ∂_{Space.basis i} φ),
    postcomp_im_lineDeriv (φ := φ)]

lemma complexifyRealDistribution_distLaplacian {d : ℕ}
    (T : (Space d)→d[ℝ] ℝ) :
    complexifyRealDistribution (distLaplacian T) =
      (Δ (complexifyRealDistribution T : 𝓢'(Space d, ℂ))) := by
  ext φ
  rw [TemperedDistribution.laplacian_apply_apply]
  simp [complexifyRealDistribution_apply, distLaplacian_apply,
    postcomp_re_laplacian, postcomp_im_laplacian]

lemma complexifyRealDistribution_iterated_distLaplacian {d : ℕ}
    (k : ℕ) (T : (Space d)→d[ℝ] ℝ) :
    complexifyRealDistribution (((distLaplacian (d := d))^[k]) T) =
      ((Laplacian.laplacian^[k])
        (complexifyRealDistribution T : 𝓢'(Space d, ℂ))) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [complexifyRealDistribution_distLaplacian]
      rw [ih]

set_option linter.flexible false in
lemma distLaplacian_norm_zpow_eq_smul {d : ℕ} (a : ℤ)
    (hgrad : -(d.succ - 1 : ℕ) + 1 ≤ a)
    (hdiv : 0 < (a - 2) + (d.succ : ℤ)) :
    distLaplacian
      (Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ a)
        (Space.IsDistBounded.pow a (by omega))) =
      (((a : ℝ) * (((a - 2) + (d.succ : ℤ) : ℤ) : ℝ)) •
        Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ (a - 2))
          (Space.IsDistBounded.pow (a - 2) (by omega))) := by
  unfold distLaplacian
  rw [LinearMap.comp_apply]
  rw [Space.distGrad_distOfFunction_norm_zpow a hgrad]
  have hvec :
      Space.distOfFunction
        (fun x : Space d.succ => ((a : ℝ) * ‖x‖ ^ (a - 2)) • Space.basis.repr x)
        (by
          simp [← smul_smul]
          refine Space.IsDistBounded.const_fun_smul ?_ (a : ℝ)
          exact Space.IsDistBounded.zpow_smul_repr_self (a - 2) (by omega)) =
      (a : ℝ) •
        Space.distOfFunction
          (fun x : Space d.succ => ‖x‖ ^ (a - 2) • Space.basis.repr x)
          (Space.IsDistBounded.zpow_smul_repr_self (a - 2) (by omega)) := by
    rw [← Space.distOfFunction_smul_fun]
    congr 1
    funext x
    simp [smul_smul]
  rw [hvec]
  rw [map_smul]
  rw [distDiv_norm_zpow_smul_repr_self_eq_smul (q := a - 2) hdiv]
  rw [smul_smul]

/--
The gradient half of the boundary Riesz identity in PhysLean's distribution
language.  In dimension `d + 1`, the exponent `1 - d` is exactly `2 - n`.
-/
lemma distLaplacian_norm_zpow_boundary_raw {d : ℕ} :
    distLaplacian
      (Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ (1 - (d : ℤ)))
        (Space.IsDistBounded.pow (1 - (d : ℤ)) (by omega))) =
      Space.distDiv (Space.distOfFunction
        (fun x : Space d.succ =>
          (((1 - (d : ℤ) : ℤ) : ℝ) * ‖x‖ ^ ((1 - (d : ℤ)) - 2)) •
            Space.basis.repr x)
        (by
          convert Space.IsDistBounded.const_fun_smul
            (F := EuclideanSpace ℝ (Fin d.succ))
            (Space.IsDistBounded.zpow_smul_repr_self ((1 - (d : ℤ)) - 2) (by omega))
            (((1 - (d : ℤ) : ℤ) : ℝ)) using 1
          ext x i
          simp [smul_smul, mul_assoc])) := by
  unfold distLaplacian
  rw [LinearMap.comp_apply]
  rw [Space.distGrad_distOfFunction_norm_zpow]
  omega

/--
The boundary Riesz identity supplied by PhysLean, repackaged as a scalar
distributional Laplacian statement.

This is the exact terminal singular step needed after the off-origin recurrence
`Δ(r^a) = a(a+n-2) r^(a-2)` has reduced `r` to `r^(2-n)`.
-/
lemma distLaplacian_norm_zpow_boundary_eq_delta {d : ℕ} :
    distLaplacian
      (Space.distOfFunction (fun x : Space d.succ => ‖x‖ ^ (1 - (d : ℤ)))
        (Space.IsDistBounded.pow (1 - (d : ℤ)) (by omega))) =
      ((1 - (d : ℤ) : ℤ) : ℝ) •
        ((d.succ * (volume (α := Space d.succ)).real (Metric.ball 0 1)) •
          Physlib.Distribution.diracDelta ℝ (0 : Space d.succ)) := by
  rw [distLaplacian_norm_zpow_boundary_raw]
  let c : ℝ := ((1 - (d : ℤ) : ℤ) : ℝ)
  have hexp : (1 - (d : ℤ)) - 2 = -(d.succ : ℤ) := by omega
  have hdist :
      Space.distOfFunction
        (fun x : Space d.succ =>
          (((1 - (d : ℤ) : ℤ) : ℝ) * ‖x‖ ^ ((1 - (d : ℤ)) - 2)) •
            Space.basis.repr x)
        (by
          convert Space.IsDistBounded.const_fun_smul
            (F := EuclideanSpace ℝ (Fin d.succ))
            (Space.IsDistBounded.zpow_smul_repr_self ((1 - (d : ℤ)) - 2) (by omega))
            (((1 - (d : ℤ) : ℤ) : ℝ)) using 1
          ext x i
          simp [smul_smul, mul_assoc]) =
        c • Space.distOfFunction (fun x : Space d.succ =>
            ‖x‖ ^ (-(d.succ : ℤ)) • Space.basis.repr x)
          (Space.IsDistBounded.zpow_smul_repr_self (-(d.succ : ℤ)) (by omega)) := by
    dsimp [c]
    rw [← Space.distOfFunction_smul_fun]
    congr 1
    funext x
    rw [hexp]
    simp [smul_smul]
  rw [hdist]
  rw [map_smul]
  rw [Space.distDiv_inv_pow_eq_dim]

/-- The unit ball in PhysLean's odd-dimensional `Space` has positive real volume. -/
lemma odd_volume_ball_real_pos (m : ℕ) :
    0 < (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1) := by
  rw [MeasureTheory.Measure.real]
  apply ENNReal.toReal_pos
  · exact ne_of_gt (Metric.measure_ball_pos
      (μ := (volume : Measure (Space (2 * m + 1))))
      (0 : Space (2 * m + 1)) (by norm_num))
  · exact MeasureTheory.measure_ball_ne_top

/-- The scalar in the odd-dimensional boundary Riesz identity is nonzero. -/
lemma odd_boundary_rieszConstant_ne_zero (m : ℕ) :
    ((1 - ((2 * m) : ℤ) : ℤ) : ℝ) *
      (((2 * m + 1) : ℕ) *
        (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1)) ≠ 0 := by
  have hv : 0 < (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1) :=
    odd_volume_ball_real_pos m
  have hnat : (((2 * m + 1) : ℕ) : ℝ) ≠ 0 := by
    positivity
  have hcoef_int : (1 - ((2 * m) : ℤ) : ℤ) ≠ 0 := by
    omega
  have hcoef : ((1 - ((2 * m) : ℤ) : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast hcoef_int
  exact mul_ne_zero hcoef (mul_ne_zero hnat hv.ne.symm)

/--
Odd-dimensional terminal Riesz step in PhysLean's real distribution language.
This is the exact statement needed once the recurrence has reduced `‖x‖` to
`‖x‖^(1 - 2m)`.
-/
lemma odd_distLaplacian_norm_zpow_boundary_exists (m : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧
      distLaplacian
        (Space.distOfFunction
          (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * m) : ℤ)))
          (Space.IsDistBounded.pow (1 - ((2 * m) : ℤ)) (by omega))) =
        c • Physlib.Distribution.diracDelta ℝ (0 : Space (2 * m + 1)) := by
  refine ⟨((1 - ((2 * m) : ℤ) : ℤ) : ℝ) *
      (((2 * m + 1) : ℕ) *
        (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1)),
      odd_boundary_rieszConstant_ne_zero m, ?_⟩
  simpa [mul_smul] using (distLaplacian_norm_zpow_boundary_eq_delta (d := 2 * m))

/--
Complexified form of the odd-dimensional terminal Riesz step on PhysLean's
`Space`.  This is one transport step closer to the Mathlib target: the codomain
is now Mathlib's complex `TemperedDistribution`.
-/
lemma odd_complexified_distLaplacian_norm_zpow_boundary_exists (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      complexifyRealDistribution
        (distLaplacian
          (Space.distOfFunction
            (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * m) : ℤ)))
            (Space.IsDistBounded.pow (1 - ((2 * m) : ℤ)) (by omega)))) =
        c • TemperedDistribution.delta (0 : Space (2 * m + 1)) := by
  rcases odd_distLaplacian_norm_zpow_boundary_exists m with ⟨c, hc, h⟩
  refine ⟨(c : ℂ), by exact_mod_cast hc, ?_⟩
  rw [h]
  rw [complexifyRealDistribution_smul, complexifyRealDistribution_diracDelta]

/-- The real radial power distribution `‖x‖^(1 - 2j)` in dimension `2m + 1`. -/
noncomputable def oddNormPowerDistribution (m j : ℕ) :
    (Space (2 * m + 1)) →d[ℝ] ℝ :=
  if hj : j ≤ m then
    Space.distOfFunction
      (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * j) : ℤ)))
      (Space.IsDistBounded.pow (1 - ((2 * j) : ℤ)) (by omega))
  else 0

lemma oddNormPowerDistribution_zero (m : ℕ) :
    oddNormPowerDistribution m 0 =
      Space.distOfFunction (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 : ℤ))
        (Space.IsDistBounded.pow 1 (by omega)) := by
  simp [oddNormPowerDistribution]

lemma oddNormPowerDistribution_boundary (m : ℕ) :
    oddNormPowerDistribution m m =
      Space.distOfFunction
        (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * m) : ℤ)))
        (Space.IsDistBounded.pow (1 - ((2 * m) : ℤ)) (by omega)) := by
  simp [oddNormPowerDistribution]

lemma odd_rieszStepCoeff_ne_zero (m j : ℕ) (hj : j < m) :
    (((1 - ((2 * j) : ℤ) : ℤ) : ℝ) *
      ((((1 - ((2 * j) : ℤ)) - 2) + ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℝ)) ≠ 0 := by
  apply mul_ne_zero
  · have h : (1 - ((2 * j) : ℤ) : ℤ) ≠ 0 := by omega
    exact_mod_cast h
  · have h : ((((1 - ((2 * j) : ℤ)) - 2) +
        ((2 * m + 1 : ℕ) : ℤ) : ℤ)) ≠ 0 := by
      omega
    exact_mod_cast h

lemma odd_distLaplacian_normPowerDistribution_eq_smul (m j : ℕ) (hj : j < m) :
    distLaplacian (d := 2 * m + 1) (oddNormPowerDistribution m j) =
      (((1 - ((2 * j) : ℤ) : ℤ) : ℝ) *
        ((((1 - ((2 * j) : ℤ)) - 2) + ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℝ)) •
          oddNormPowerDistribution m (j + 1) := by
  have h := distLaplacian_norm_zpow_eq_smul (d := 2 * m)
    (a := (1 - ((2 * j) : ℤ)))
    (hgrad := by omega)
    (hdiv := by omega)
  have hj_le : j ≤ m := Nat.le_of_lt hj
  have hsucc_le : j + 1 ≤ m := Nat.succ_le_of_lt hj
  have hexp : (1 - ((2 * j) : ℤ)) - 2 = 1 - ((2 * (j + 1)) : ℤ) := by
    omega
  have hleft :
      oddNormPowerDistribution m j =
        Space.distOfFunction
          (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * j) : ℤ)))
          (Space.IsDistBounded.pow (1 - ((2 * j) : ℤ)) (by omega)) := by
    simp [oddNormPowerDistribution, hj_le]
  have hright :
      oddNormPowerDistribution m (j + 1) =
        Space.distOfFunction
          (fun x : Space (2 * m + 1) => ‖x‖ ^ ((1 - ((2 * j) : ℤ)) - 2))
          (Space.IsDistBounded.pow ((1 - ((2 * j) : ℤ)) - 2) (by omega)) := by
    simp [oddNormPowerDistribution, hsucc_le, hexp]
  calc
    distLaplacian (d := 2 * m + 1) (oddNormPowerDistribution m j)
        = distLaplacian (d := 2 * m + 1)
            (Space.distOfFunction
              (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 - ((2 * j) : ℤ)))
              (Space.IsDistBounded.pow (1 - ((2 * j) : ℤ)) (by omega))) := by
            rw [hleft]
    _ = (((1 - ((2 * j) : ℤ) : ℤ) : ℝ) *
        ((((1 - ((2 * j) : ℤ)) - 2) + ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℝ)) •
          Space.distOfFunction
            (fun x : Space (2 * m + 1) => ‖x‖ ^ ((1 - ((2 * j) : ℤ)) - 2))
            (Space.IsDistBounded.pow ((1 - ((2 * j) : ℤ)) - 2) (by omega)) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
    _ = (((1 - ((2 * j) : ℤ) : ℤ) : ℝ) *
        ((((1 - ((2 * j) : ℤ)) - 2) + ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℝ)) •
          oddNormPowerDistribution m (j + 1) := by
            rw [hright]

lemma odd_iterated_distLaplacian_normPowerDistribution_eq_smul (m k : ℕ)
    (hk : k ≤ m) :
    ∃ a : ℝ, a ≠ 0 ∧
      (((distLaplacian (d := 2 * m + 1))^[k]) (oddNormPowerDistribution m 0) =
        a • oddNormPowerDistribution m k) := by
  induction k with
  | zero =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp
  | succ k ih =>
      have hk_lt : k < m := Nat.lt_of_succ_le hk
      rcases ih (Nat.le_of_lt hk_lt) with ⟨a, ha, hiter⟩
      let b : ℝ :=
        (((1 - ((2 * k) : ℤ) : ℤ) : ℝ) *
          ((((1 - ((2 * k) : ℤ)) - 2) + ((2 * m + 1 : ℕ) : ℤ) : ℤ) : ℝ))
      have hb : b ≠ 0 := by
        dsimp [b]
        exact odd_rieszStepCoeff_ne_zero m k hk_lt
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      calc
        (((distLaplacian (d := 2 * m + 1))^[Nat.succ k])
            (oddNormPowerDistribution m 0))
            = distLaplacian (d := 2 * m + 1)
                ((((distLaplacian (d := 2 * m + 1))^[k])
                  (oddNormPowerDistribution m 0))) := by
                simp [Function.iterate_succ_apply']
        _ = distLaplacian (d := 2 * m + 1) (a • oddNormPowerDistribution m k) := by
                rw [hiter]
        _ = a • distLaplacian (d := 2 * m + 1) (oddNormPowerDistribution m k) := by
                exact map_smul (distLaplacian (d := 2 * m + 1)) a
                  (oddNormPowerDistribution m k)
        _ = a • (b • oddNormPowerDistribution m (k + 1)) := by
                rw [odd_distLaplacian_normPowerDistribution_eq_smul m k hk_lt]
        _ = (a * b) • oddNormPowerDistribution m (Nat.succ k) := by
                simp [b, smul_smul]

lemma odd_distLaplacian_norm_exists (m : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧
      (((distLaplacian (d := 2 * m + 1))^[m + 1])
          (oddNormPowerDistribution m 0) =
        c • Physlib.Distribution.diracDelta ℝ (0 : Space (2 * m + 1))) := by
  rcases odd_iterated_distLaplacian_normPowerDistribution_eq_smul m m le_rfl with
    ⟨a, ha, hiter⟩
  rcases odd_distLaplacian_norm_zpow_boundary_exists m with ⟨b, hb, hboundary⟩
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  calc
    (((distLaplacian (d := 2 * m + 1))^[m + 1])
        (oddNormPowerDistribution m 0))
        = distLaplacian (d := 2 * m + 1)
            ((((distLaplacian (d := 2 * m + 1))^[m])
              (oddNormPowerDistribution m 0))) := by
            simp [Function.iterate_succ_apply']
    _ = distLaplacian (d := 2 * m + 1) (a • oddNormPowerDistribution m m) := by
            rw [hiter]
    _ = a • distLaplacian (d := 2 * m + 1) (oddNormPowerDistribution m m) := by
            exact map_smul (distLaplacian (d := 2 * m + 1)) a
              (oddNormPowerDistribution m m)
    _ = a • (b • Physlib.Distribution.diracDelta ℝ (0 : Space (2 * m + 1))) := by
            rw [oddNormPowerDistribution_boundary, hboundary]
    _ = (a * b) • Physlib.Distribution.diracDelta ℝ (0 : Space (2 * m + 1)) := by
            rw [mul_smul]

lemma odd_complexified_distLaplacian_norm_exists (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      complexifyRealDistribution
        ((((distLaplacian (d := 2 * m + 1))^[m + 1])
          (oddNormPowerDistribution m 0))) =
        c • TemperedDistribution.delta (0 : Space (2 * m + 1)) := by
  rcases odd_distLaplacian_norm_exists m with ⟨c, hc, h⟩
  refine ⟨(c : ℂ), by exact_mod_cast hc, ?_⟩
  rw [h]
  rw [complexifyRealDistribution_smul, complexifyRealDistribution_diracDelta]

lemma odd_complexified_laplacian_norm_exists (m : ℕ) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((Laplacian.laplacian^[m + 1])
        (complexifyRealDistribution (oddNormPowerDistribution m 0) :
          𝓢'(Space (2 * m + 1), ℂ))) =
        c • TemperedDistribution.delta (0 : Space (2 * m + 1)) := by
  rcases odd_complexified_distLaplacian_norm_exists m with ⟨c, hc, h⟩
  refine ⟨c, hc, ?_⟩
  rw [← complexifyRealDistribution_iterated_distLaplacian (d := 2 * m + 1)
    (k := m + 1) (T := oddNormPowerDistribution m 0)]
  exact h

end Space

end CramerWoldTheorem.OddInversion.PhysLeanBridge
