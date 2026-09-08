# Quantizing Pythagorean Triples

Lean 4 source-backed formalization setup for Mathevet--Morier-Genoud--Ovsienko,
*Quantizing Pythagorean triples*.

The active formalization is in:

- `Pythagore2/`
- `Pythagore2.lean`

## Status

- `lake build Pythagore2` succeeds.
- q-rationals are defined from odd continued fractions and q-deformed matrix words.
- q-rational construction facts are theorem skeletons, not axioms.
- The only axiom is `unimodality_conjecture`, matching the source's open conjecture.

See:

- `Pythagore2/Blueprint.md`
- `TODO.md`
- `EPFLemma.md`
