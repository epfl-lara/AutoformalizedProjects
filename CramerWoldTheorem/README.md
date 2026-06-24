# A Calculus Proof of the Cramer-Wold Theorem

Lean 4 source-backed formalization of Russell Lyons and Kevin Zumbrun,
*A Calculus Proof of the Cramer-Wold Theorem*.

The active formalization is in:

- `CramerWoldTheorem/`
- `CramerWoldTheorem.lean`

The Lean declarations are split by proof role:

- `Basic.lean`: Euclidean-space model, closed half-spaces, half-space values, and average-distance function.
- `Halfspaces.lean`: measurability and recovery of average-distance functions from half-space values.
- `Inversion.lean`: odd-dimensional inversion and even-to-odd reduction.
- `MainTheorem.lean`: the Cramer-Wold theorem and normal/threshold companion statement.

## Status

- `lake build CramerWoldTheorem` succeeds.
- The active Lean development has no project-local `sorry`, `admit`, custom
  `axiom`, or `unsafe`.
- The formalization records closed half-spaces, half-space values,
  average-distance functions, the odd-dimensional inversion step, the
  even-to-odd reduction, and the final Cramer-Wold statement.
- The analytic endpoint is implemented in `OddInversion/` and imported by
  `CramerWoldTheorem/Inversion.lean`.

## File Layout

- `CramerWoldTheorem/Basic.lean`: Euclidean-space model, closed half-spaces,
  half-space values, and average-distance function.
- `CramerWoldTheorem/Halfspaces.lean`: measurability and recovery of
  average-distance functions from half-space values.
- `CramerWoldTheorem/Inversion.lean`: odd-dimensional average-distance
  inversion and even-to-odd reduction.
- `CramerWoldTheorem/MainTheorem.lean`: the Cramer-Wold theorem and the
  normal/threshold parameterized companion statement.
- `OddInversion/`: proof workspace for the odd-dimensional analytic endpoint.

See:

- `CramerWoldTheorem/Blueprint.md`
- `docs/source/cramerwold-arxiv.tex`
- `docs/lyons_zumbrun2016_cramer_wold.pdf`
