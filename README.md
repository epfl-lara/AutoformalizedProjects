# Paper-Level Autoformalizations

Lean 4 formalization projects produced with the EPFLemma workflow. The `main`
branch is reserved for projects that are ready to present publicly: each listed
project builds and has no project-local `sorry`, `admit`, custom `axiom`, or
`unsafe` in its Lean files.

Work-in-progress formalizations are kept on separate draft pull requests instead
of living on `main`.

## Repository Metadata

- License: [Apache License 2.0](LICENSE)
- Contribution guide: [CONTRIBUTING.md](CONTRIBUTING.md)
- Publication notes and limitations:
  [PUBLICATION_LIMITATIONS.md](PUBLICATION_LIMITATIONS.md)
- Citation metadata: [CITATION.cff](CITATION.cff)

## Completed Projects

### `PythagoreanPolynomialParametrization`

- Lake target: `Pyth`
- Source: Sophie Frisch and Leonid Vaserstein,
  [*Parametrization of Pythagorean triples by a single triple of
  polynomials*](https://arxiv.org/abs/0706.0290)
- Status: proof-complete source-backed formalization of the obstruction theorem,
  the integer-valued parametrization, and the positive/16-parameter variants.

### `CramerWoldTheorem`

- Lake target: `CramerWoldTheorem`
- Source: Russell Lyons and Kevin Zumbrun,
  [*A Calculus Proof of the Cramer-Wold
  Theorem*](https://arxiv.org/abs/1607.03206)
- Status: proof-complete source-backed formalization of the half-space theorem,
  average-distance reconstruction, odd-dimensional inversion, and even-to-odd
  reduction.

## Work in Progress

The unfinished formalizations are maintained as draft PR branches:

- `AShortProofOfTheHiltonMilnerTheorem`:
  [*A short proof of the Hilton-Milner
  Theorem*](https://arxiv.org/abs/2411.02513), with remaining proof
  obligations.
- `QuantizingPythagoreanTriples`:
  [*Quantizing Pythagorean triples*](https://arxiv.org/abs/2602.20536), with
  remaining proof obligations and the source-stated open unimodality conjecture.

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
