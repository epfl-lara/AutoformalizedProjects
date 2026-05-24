# Resources

## Source Paper

- Lyons and Zumbrun, "A Calculus Proof of the Cramer-Wold Theorem":
  https://arxiv.org/abs/1607.03206

Relevant local files:

- `docs/source/cramerwold-arxiv.tex`
- `docs/lyons_zumbrun2016_cramer_wold.pdf`
- `CramerWoldTheorem/Blueprint.md`

Key source region:

- TeX lines around the paragraph beginning "The idea is that if `n = 2m - 1`
  is odd..." through the proof of `Δ^m f_μ = c_m μ`.

## Mathlib References

- Tempered distributions:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/TemperedDistribution.html

- Fourier multipliers and Laplacian:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/FourierMultiplier.html

- Distribution derivative notation and Laplacian:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Distribution/DerivNotation.html

- Characteristic functions of measures:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/CharacteristicFunction/Basic.html

- Bounded continuous functions and lintegrals:
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/BoundedContinuousFunction.html

- PhysLean formal distributional divergence theorem:
  https://github.com/HEPLean/PhysLean/blob/master/Physlib/SpaceAndTime/Space/Norm.lean

  Relevant declaration: `Space.distDiv_inv_pow_eq_dim`.  It proves the formal
  identity `div (x ↦ ‖x‖^{-d} x) = c δ₀` in PhysLean's distribution API.
  This is the formal Green-identity ingredient closest to the remaining
  `OddInversion/Target.lean` blocker, but it is not currently a project
  dependency and the probed checkout uses Lean `v4.29.1`.

## Analytic Background

Local downloads are in `docs/`; see `docs/README.md` for source URLs,
checksums, and copyright/license notes.

- Fundamental solution of the Laplace equation, overview:
  https://en.wikipedia.org/wiki/Fundamental_solution#Laplace_equation

- Green's identities:
  https://en.wikipedia.org/wiki/Green%27s_identities

- Stanford Math 220B lecture notes:
  - Laplace's Equation:
    `docs/stanford_math220b_laplace.pdf`
  - Green's Functions:
    `docs/stanford_math220b_greens_functions.pdf`

- MIT OCW lecture notes:
  - 18.156, Lecture 0, fundamental solutions:
    `docs/mit_18_156_lec0_fundamental_solutions.pdf`
  - 18.303, Green's function notes:
    `docs/mit_18_303_greens_function.pdf`

- ProofWiki, one-dimensional Laplace fundamental solution:
  `docs/proofwiki_1d_laplace_fundamental_solution.html`

- Evans, "Partial Differential Equations", standard reference for fundamental
  solutions of the Laplacian and distributional identities.

- Folland, "Introduction to Partial Differential Equations", standard reference
  for Fourier-transform derivations of fundamental solutions.

Evans and Folland were not downloaded because they are copyrighted books.

## Proof Strategy Notes

The source paper uses a Green identity argument.  For Lean, a Fourier multiplier
route may be more compatible with existing Mathlib:

1. Use Mathlib's tempered distribution API.
2. Express repeated Laplacians as Fourier multipliers by powers of `‖ξ‖^2`.
3. Prove the Fourier transform of the odd-dimensional distance kernel is a
   nonzero constant times `‖ξ‖^(-2m-2)` in the distributional sense.
4. Multiplication by `‖ξ‖^(2m+2)` then gives a nonzero constant times `1`,
   i.e. the Fourier transform of a Dirac delta.

The Green identity path may be closer to the paper, but it requires more
classical analysis infrastructure around compactly supported smooth functions,
boundary terms, and singularity excision.
