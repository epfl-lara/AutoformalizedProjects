# A Calculus Proof of the Cramer-Wold Theorem

Lean 4 source-backed formalization setup for Russell Lyons and Kevin Zumbrun,
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
- Current version has no custom axioms, `admit`, or `unsafe`; it has two
  source-backed analytic `sorry` proof obligations.
- The formalization records closed half-spaces, half-space values, average-distance
  functions, the odd-dimensional inversion step, the even-to-odd reduction, and the
  final Cramer-Wold statement.

The remaining analytic proof targets are:

- `averageDistance_eq_of_halfspaceValues_eq`: packages the Crofton/Fubini argument
  showing that closed-halfspace values determine the average-distance function.
- `measure_eq_of_averageDistance_eq_odd_aux`: packages the odd-dimensional Green's
  identity/Laplacian inversion step showing that the average-distance function
  determines the measure.

These correspond to the two hard analytic proof blocks in the source paper. The
even-dimensional embedding step and the final parity split are proved in Lean from
these proof targets.

This is a substantially harder proof-completion target than the finite combinatorics
paper because the source proof uses signed measures, Crofton measure, Green's identity,
and distributional Laplacian inversion.

See:

- `CramerWoldTheorem/Blueprint.md`
- `docs/source/cramerwold-arxiv.tex`
- `docs/lyons_zumbrun2016_cramer_wold.pdf`
