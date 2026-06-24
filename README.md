# Paper-Level Autoformalizations

Lean 4 formalization projects produced with the EPFLemma workflow. The `main`
branch is reserved for projects that are ready to present publicly: each listed
project builds and has no project-local `sorry`, `admit`, custom `axiom`, or
`unsafe` in its Lean files.

Work-in-progress formalizations are kept on separate draft pull requests instead
of living on `main`.

## Completed Projects

| Project | Lake target | Source paper | Public status |
| --- | --- | --- | --- |
| `PythagoreanPolynomialParametrization` | `Pyth` | Sophie Frisch and Leonid Vaserstein, *Parametrization of Pythagorean triples by a single triple of polynomials* | Proof-complete source-backed formalization of the obstruction theorem, the integer-valued parametrization, and the positive/16-parameter variants. |
| `CramerWoldTheorem` | `CramerWoldTheorem` | Russell Lyons and Kevin Zumbrun, *A Calculus Proof of the Cramer-Wold Theorem* | Proof-complete source-backed formalization of the half-space theorem, average-distance reconstruction, odd-dimensional inversion, and even-to-odd reduction. |

## Work in Progress

The unfinished formalizations are maintained as draft PR branches:

| Project | Status on WIP branch |
| --- | --- |
| `AShortProofOfTheHiltonMilnerTheorem` | Source-backed Hilton-Milner theorem skeleton with remaining proof obligations. |
| `QuantizingPythagoreanTriples` | Source-backed q-Pythagorean skeleton with remaining proof obligations and the source-stated open unimodality conjecture. |

## Checks

Run all completed project builds:

```bash
./scripts/check-projects.sh
```

Or build an individual project from its directory:

```bash
cd PythagoreanPolynomialParametrization
lake build Pyth

cd ../CramerWoldTheorem
lake build CramerWoldTheorem
```
