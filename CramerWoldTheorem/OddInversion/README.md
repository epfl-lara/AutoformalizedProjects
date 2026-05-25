# Odd-Dimensional Inversion Subproject

Goal: replace the axiom
`CramerWoldTheorem.averageDistance_eq_odd_lintegral_of_boundedContinuous_nnreal`
with a theorem.

This directory is deliberately not imported by `CramerWoldTheorem.Main`.  It is
a proof workspace for the analytic endpoint behind `Inversion.lean`.

## Files

- `Target.lean`: Lean proof queue.  It restates the axiom as a theorem.  The
  measure-separation, Fubini, translation, algebraic wrapper, and
  Fourier/Riesz multiplier steps are now proved.
- `FundamentalSolution.lean`: completed odd-dimensional fundamental-solution
  identity for the norm kernel.
- `PhysLeanBridge.lean` and `Transport.lean`: bridge the PhysLean real
  distributional Laplacian result to Mathlib complex tempered distributions on
  `OddSpace`.
- `Roadmap.md`: proof decomposition, constants, and Lean-facing tasks.
- `Resources.md`: internet, Mathlib, and PhysLean references to use while
  proving.

## Check Command

From the project root:

```bash
lake env lean OddInversion/Target.lean
```

The target file contains no `sorry` placeholders and no custom axioms.  The main
project can import the completed theorem directly.
