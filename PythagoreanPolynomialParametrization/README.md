# Parametrization of Pythagorean Triples by Polynomials

Lean 4 source-backed formalization setup for Sophie Frisch and Leonid Vaserstein,
*Parametrization of Pythagorean triples by a single triple of polynomials*.

The active formalization is the more faithful statement skeleton in:

- `Pyth/`
- `Pyth.lean`

The older proof-complete function-model version is preserved unchanged under
the hidden archive path:

- `.version/proof_complete_function_model_20260428/`

For new proof attempts, start from `Pyth/`; do not revive
the weaker top-level function-model skeleton unless explicitly comparing
against the archive.

## Status

- `lake build Pyth` succeeds.
- Current active version has source-backed theorem skeletons with `sorry` proof obligations.
- It models the paper's rational polynomials as `MvPolynomial (Fin n) ℚ` where appropriate, rather than only as rational-valued functions.

See:

- `Pyth/Blueprint.md`
- `TODO.md`
- `EPFLemma.md`
