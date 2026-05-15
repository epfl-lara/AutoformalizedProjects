import Pyth.Basic
import Pyth.SourceLemmas
import Pyth.Obstructions
import Pyth.IntegerValued
import Pyth.Positive

/-! # Parametrization of Pythagorean Triples by Polynomials

This directory sets up source-backed Lean statements for results from Frisch and
Vaserstein's paper "Parametrization of Pythagorean triples by a single triple of
polynomials". The main mathematical proofs are intentionally left as `sorry` proof
obligations.

## File layout

- `Basic`: shared definitions of Pythagorean triples, integer-valued polynomials,
  and parametrization predicates.
- `SourceLemmas`: source-level proof handoff lemmas for the `T(a,b,c)` map, parity
  conditions, positive parameters, and four-square substitutions.
- `Obstructions`: no single integer-coefficient polynomial triple parametrizes all
  Pythagorean triples.
- `IntegerValued`: the explicit four-variable integer-valued parametrization of all
  Pythagorean triples.
- `Positive`: the positive-triple parametrization and the 16-parameter unrestricted
  variant.
-/
