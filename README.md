# Paper Level Autoformalizations

Lean 4 projects for the autoformalization with EPFLemma framework. 

## Projects

| Project | Lean target | Paper | Status |
| --- | --- | --- | --- |
| `PythagoreanPolynomialParametrization` | `Pyth` | Frisch--Vaserstein, *Parametrization of Pythagorean triples by a single triple of polynomials* | Source-backed statement skeleton in `Pyth/`; legacy proof-complete function-model version hidden under `.version/`. |
| `QuantizingPythagoreanTriples` | `Pythagore2` | Mathevet--Morier-Genoud--Ovsienko, *Quantizing Pythagorean triples* | Source-backed statement skeleton in `Pythagore2/`; q-rationals defined from continued fractions and q-matrix words; only the open unimodality conjecture remains an axiom. |
| `AShortProofOfTheHiltonMilnerTheorem` | `AShortProofOfTheHiltonMilnerTheorem` | Bulavka--Woodroofe, *A short proof of the Hilton-Milner Theorem* | Source-backed statement skeleton for finite set families, shadows, shifting, the Hilton--Milner bound, and uniqueness bridge lemmas. |
| `CramerWoldTheorem` | `CramerWoldTheorem` | Lyons--Zumbrun, *A Calculus Proof of the Cramer-Wold Theorem* | Builds with two source-backed analytic `sorry` targets for Crofton reconstruction and odd-dimensional Laplacian inversion; no custom axioms. |

## Checks

```bash
./scripts/check-projects.sh
```
