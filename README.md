# Paper Level Autoformalizations

Lean 4 projects for the autoformalization with EPFLemma framework. 

## Projects

| Project | Lean target | Paper | Status |
| --- | --- | --- | --- |
| `PythagoreanPolynomialParametrization` | `Pyth` | Frisch--Vaserstein, *Parametrization of Pythagorean triples by a single triple of polynomials* | Source-backed statement skeleton in `Pyth/`; legacy proof-complete function-model version hidden under `.version/`. |
| `QuantizingPythagoreanTriples` | `Pythagore2` | Mathevet--Morier-Genoud--Ovsienko, *Quantizing Pythagorean triples* | Source-backed statement skeleton in `Pythagore2/`; q-rationals defined from continued fractions and q-matrix words; only the open unimodality conjecture remains an axiom. |

## Checks

```bash
./scripts/check-projects.sh
```
