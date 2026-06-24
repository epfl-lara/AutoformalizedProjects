# Odd-Dimensional Inversion Subproject

This directory contains the completed proof workspace for the analytic endpoint
behind `CramerWoldTheorem/Inversion.lean`.

## Files

- `Target.lean`: Lean proof queue for the measure-level endpoint. The
  measure-separation, Fubini, translation, algebraic wrapper, and
  Fourier/Riesz multiplier steps are proved here.
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

The target file contains no `sorry` placeholders and no custom axioms. The main
project imports the completed theorem through `CramerWoldTheorem/Inversion.lean`.
