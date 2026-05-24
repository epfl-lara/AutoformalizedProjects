# Roadmap

## Current Axiom To Replace

In `CramerWoldTheorem/Inversion.lean`:

```lean
averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal
```

Informal content:

If `μ` and `ν` are probability measures on `R^(2m+1)` and
`averageDistance μ y = averageDistance ν y` for all `y`, then every bounded
continuous nonnegative test has the same `lintegral` against `μ` and `ν`.

## Reindexing Warning

The paper writes odd dimensions as `d = 2q - 1` and proves
`Δ^q f_μ = c_q μ`.

The Lean theorem writes odd dimensions as `d = 2m + 1`, so `q = m + 1`.  Any
formal Laplacian recovery lemma should therefore use `Δ^(m + 1)`, not `Δ^m`.

## Proposed Lean Decomposition

1. Pure Fourier/Riesz multiplier blocker:

   ```lean
   normKernel_fourier_multiplier_power_eq_constDistribution
   ```

   This is now the only `sorry` in `Target.lean`.  It states that
   `(‖ξ‖²)^(m+1) • 𝓕(‖x‖)` is a nonzero constant distribution.

2. Origin radial fundamental-solution wrapper:

   ```lean
   norm_iterated_laplacian_pairing_at_zero
   ```

   This is now a proved wrapper from the Fourier/Riesz multiplier identity:
   pairing `y ↦ ‖y‖` with `Δ^(m+1) φ` recovers a nonzero constant multiple of
   `φ 0`.

3. Translation packaging:

   ```lean
   distance_iterated_laplacian_pairing_of_norm_translation
   distance_iterated_laplacian_pairing
   ```

   The `_of_norm_translation` theorem should use translation invariance of
   volume, distance, Schwartz maps, and the Laplacian to move the origin result
   to an arbitrary pole `x`.  `distance_iterated_laplacian_pairing` is now only
   a wrapper.

4. Constant-term vanishing:

   ```lean
   integral_iterated_laplacian_eq_zero
   constant_iterated_laplacian_integral_eq_zero
   ```

   The first theorem is the real target: an iterated Laplacian of a Schwartz
   function has integral zero.  The constant-multiple theorem is now a proved
   wrapper using `MeasureTheory.integral_const_mul`.

5. Centered kernel pairing:

   ```lean
   centeredDistanceKernel_iterated_laplacian_pairing_of_distance
   centeredDistanceKernel_iterated_laplacian_pairing
   ```

   These are now proved algebraic wrappers combining the distance pairing,
   constant-term vanishing, and the distance integrability helpers added by the
   prover.

6. Packaged inversion formula:

   ```lean
   averageDistance_schwartz_inversion_formula_from_pairing_constant
   averageDistance_schwartz_inversion_formula_of_kernel_pairing
   averageDistance_schwartz_inversion_formula
   ```

   The `_from_pairing_constant` theorem is the real Fubini/Tonelli target.  It
   should swap the `x`-integral against a probability measure with the
   `y`-integral against the Schwartz/Laplacian weight and account for the
   inverse nonzero constant.  The later two theorems are wrappers.

7. Schwartz separation target:

   ```lean
   schwartz_integral_eq_of_averageDistance_eq_odd
   ```

   This is now only an algebraic wrapper around
   `averageDistance_schwartz_inversion_formula` and
   `schwartz_integral_eq_of_potential_formula`.  Do not attack it directly.

8. Measure separation target:

   ```lean
   smooth_compactSupport_integral_eq_of_schwartz_integral_eq
   compactlySupported_integral_eq_of_schwartz_integral_eq
   measure_eq_of_schwartz_integral_eq
   ```

   This is proved.  The endpoint now avoids characteristic functions: smooth
   compactly supported real tests are coerced to complex Schwartz maps using
   `HasCompactSupport.toSchwartzMap`; arbitrary `C_c` tests are reached by
   smooth compact-support approximation in `L¹(μ + ν)`; measure equality then
   follows from `Measure.ext_of_integral_eq_on_compactlySupported`.

9. Axiom replacement:

   ```lean
   averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal
   ```

   This follows immediately from measure equality.

## Agent Guidance From The Prover Logs

`prove-20260524T102801Z-pid8721.log` showed the prover repeatedly failed on
`schwartz_integral_eq_of_averageDistance_eq_odd` because the theorem was too
coarse.

`prove-20260524T112151Z-pid75546.log` then showed the prover still struggled on
`distance_iterated_laplacian_pairing`.  It added useful integrability helpers,
but search found no Mathlib/project theorem for the Fourier transform of
`‖x‖`, Riesz kernels, or the distributional identity `Δ^(m+1) ‖x‖ = c δ₀`.
The next run should therefore start at the origin radial statement
`norm_iterated_laplacian_pairing_at_zero`, not at the translated distance
statement.

`prove-20260524T121155Z-pid38698.log` confirmed the same blocker at
`norm_iterated_laplacian_pairing_at_zero`.  It added a few useful verified
helpers, but the advisor again found no current Mathlib route to the radial
Riesz/fundamental-solution identity.  Re-running broad search on this target is
unlikely to help until the norm distribution and its Laplacian identity are
formalized.

`prove-20260524T153407Z` timed out on the isolated Fourier/Riesz target after
searching Mathlib and the local project.  It did not find a packaged Fourier
transform of `‖x‖`, a Riesz kernel theorem, or a direct fundamental-solution
identity.

Do not use or import `CramerWoldTheorem.Inversion` in this subproject: that file
contains the axiom this directory is meant to replace.

Current queue order:

1. Prove `normKernel_fourier_multiplier_power_eq_constDistribution`.
2. Everything downstream in `Target.lean`, including
   `norm_iterated_laplacian_pairing_at_zero`, is now a proved wrapper.

Useful helpers already proved in `Target.lean`:

```lean
schwartz_integral_mul_iterated_laplacian_comm
dist_mul_schwartz_integrable
dist_mul_iterated_laplacian_integrable
norm_mul_schwartz_integrable
norm_mul_iterated_laplacian_integrable
temperedDistribution_iterated_laplacian_apply_apply
normKernelDistributionAtZero_apply
fourier_laplacian_eq_smulLeftCLM_normSq
fourier_iterated_laplacian_eq_iterated_smulLeftCLM_normSq
iterated_fourierNormSqMultiplier_eq_smulLeftCLM_pow
normKernel_fourier_multiplier_power_eq_constDistribution_of_distributional_identity
iterated_laplacian_succ_eq_smul_of_iterated_eq_smul
normKernel_distributional_laplacian_power_eq_delta_of_riesz_step
smooth_compactSupport_integral_eq_of_schwartz_integral_eq
integral_norm_sub_le_of_eLpNorm_one_le
compactlySupported_integral_eq_of_schwartz_integral_eq
```

These handle basic integrability and moving iterated distributional Laplacians
onto Schwartz test functions, plus the full Schwartz-to-measure separation
endpoint.  They are infrastructure only; they do not prove the missing radial
fundamental-solution identity.

Smallest missing analytic lemma:

```lean
∃ c : ℂ, c ≠ 0 ∧
  TemperedDistribution.smulLeftCLM ℂ
    (fun ξ : OddSpace m => (Complex.ofReal (‖ξ‖ ^ 2)) ^ (m + 1))
    (𝓕 (normKernelDistributionAtZero m)) =
      c • ((volume : Measure (OddSpace m)).toTemperedDistribution)
```

The norm-kernel tempered distribution `T_norm φ = ∫ y, (‖y‖ : ℂ) * φ y` is now
constructed in Lean as `normKernelDistributionAtZero`.  The distributional
identity `(Δ^[m+1]) T_norm = c • δ₀` is also now a proved wrapper around the
Fourier multiplier statement above.  Conversely,
`normKernel_fourier_multiplier_power_eq_constDistribution_of_distributional_identity`
proves that the Fourier multiplier statement follows from
`(Δ^[m+1]) T_norm = c • δ₀`; therefore the Green-identity route and the Fourier
route now have the same formal endpoint.

## External Formalization Lead

PhysLean has a closely related formal theorem:

```lean
Space.distDiv_inv_pow_eq_dim
```

Source in the probed repository:

```text
Physlib/SpaceAndTime/Space/Norm.lean
```

It proves, in PhysLean's distribution API, that
`div (x ↦ ‖x‖^{-d} x)` is a nonzero multiple of `δ₀`.  This is exactly the
last Green-identity ingredient for the Laplacian fundamental solution
`Δ r^(2-n) = c δ₀`.  It is not directly imported here because the probed
PhysLean checkout uses Lean `v4.29.1`, while this project uses
`v4.30.0-rc2`; also PhysLean's `Distribution` is a continuous linear map on
Schwartz functions, while this file uses Mathlib's `TemperedDistribution`
pointwise-convergence API.  The theorem is still a useful formal source for a
port or bridge.

## Analytic Lemmas Needed For Step 1

- Show `y ↦ dist y x` has the right distributional Laplacian singularity at `x`.
- Show the constant term `dist 0 x` vanishes after applying the Laplacian in the
  `y` variable.
- Establish the fundamental-solution identity in dimension `2m+1`:

  ```text
  Δ^(m+1) (fun y => ‖y - x‖) = c_m * δ_x
  ```

  with a nonzero constant `c_m`.

- Justify Fubini / distribution pairing:

  ```text
  Δ^(m+1) (fun y => ∫ K x y dμ x)
    = ∫ Δ^(m+1) (fun y => K x y) dμ x
  ```

- Pair with Schwartz test functions and use the hypothesis
  `averageDistance μ = averageDistance ν`.

## Mathlib API Targets

Start with these declarations:

- `MeasureTheory.Measure.toTemperedDistribution`
- `MeasureTheory.Measure.toTemperedDistribution_apply`
- `TemperedDistribution.laplacian_apply_apply`
- `TemperedDistribution.laplacian_eq_fourierMultiplierCLM`
- `SchwartzMap.laplacian_eq_fourierMultiplierCLM`
- `HasCompactSupport.toSchwartzMap`
- `HasCompactSupport.exist_eLpNorm_sub_le_of_continuous`
- `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`

Useful modules:

- `Mathlib.Analysis.Distribution.TemperedDistribution`
- `Mathlib.Analysis.Distribution.FourierMultiplier`
- `Mathlib.Analysis.Distribution.TemperateGrowth`
- `Mathlib.Analysis.Normed.Lp.SmoothApprox`
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real`

## Recommended First Milestones

1. Prove the `m = 0`, dimension-one case:

   ```text
   d^2/dy^2 |y - x| = 2 δ_x
   ```

   This validates the indexing and distribution-pairing route.

2. `measure_eq_of_schwartz_integral_eq` is already proved in `Target.lean`.

3. Formalize the radial-kernel identity by Fourier multipliers if possible,
   because Mathlib already has Laplacian/Fourier multiplier support for
   tempered distributions.
