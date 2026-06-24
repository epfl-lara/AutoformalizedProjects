# Parametrization of Pythagorean Triples by Polynomials

Lean 4 source-backed formalization of Sophie Frisch and Leonid Vaserstein,
*Parametrization of Pythagorean triples by a single triple of polynomials*.

The active formalization is in:

- `Pyth/`
- `Pyth.lean`

## Status

- `lake build Pyth` succeeds.
- The active Lean development has no project-local `sorry`, `admit`, custom
  `axiom`, or `unsafe`.
- It models the paper's rational polynomials as `MvPolynomial (Fin n) ℚ` where
  appropriate, rather than only as rational-valued functions.
- Externally cited and explanatory source claims are isolated in
  `Pyth/Explanatory.lean`.

## File Layout

- `Pyth/Basic.lean`: Pythagorean triples, integer-valued polynomials, and
  parametrization predicates.
- `Pyth/SourceLemmas.lean`: source-level lemmas for the `T(a,b,c)` map,
  parity conditions, positive parameters, and four-square substitutions.
- `Pyth/Obstructions.lean`: no single integer-coefficient polynomial triple
  parametrizes all Pythagorean triples.
- `Pyth/IntegerValued.lean`: the explicit four-variable integer-valued
  parametrization.
- `Pyth/Positive.lean`: the positive-triple parametrization and the
  16-parameter unrestricted variant.
- `Pyth/Explanatory.lean`: reusable finite-family parametrization statements,
  the cited finite-cover theorem, and integer-valued factorization notes.

See:

- `Pyth/Blueprint.md`
- `docs/pyth.tex`
