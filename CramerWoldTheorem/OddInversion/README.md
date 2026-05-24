# Odd-Dimensional Inversion Subproject

Goal: replace the axiom
`CramerWoldTheorem.averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal`
with a theorem.

This directory is deliberately not imported by `CramerWoldTheorem.Main`.  It is
a proof workspace for the analytic endpoint behind `Inversion.lean`.

## Files

- `Target.lean`: Lean proof queue.  It restates the axiom as a theorem.  All
  measure-separation, Fubini, translation, and algebraic wrapper steps are now
  proved; the remaining blocker is the pure Fourier/Riesz multiplier identity
  `normKernel_fourier_multiplier_power_eq_constDistribution`.
- `Roadmap.md`: proof decomposition, constants, and Lean-facing tasks.
- `Resources.md`: internet, Mathlib, and PhysLean references to use while
  proving.

## Check Command

From the project root:

```bash
lake env lean OddInversion/Target.lean
```

The file currently contains one `sorry` placeholder and no custom axioms.  The main
project remains unchanged until this subproject is imported or its completed
theorems are moved into `Inversion.lean`.
