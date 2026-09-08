import Pythagore2.Basic
import Pythagore2.Classical
import Pythagore2.QRationals
import Pythagore2.QPythagorean
import Pythagore2.Conjecture

/-! # Quantizing Pythagorean Triples

This directory sets up source-backed Lean statements for Mathevet--Morier-Genoud--
Ovsienko, "Quantizing Pythagorean triples".

Unlike the earlier draft, q-rationals are not modeled as axioms. They are defined from
chosen odd continued fraction expansions and the q-deformed matrix word in `R_q` and
`L_q`. The difficult construction properties are theorem skeletons with proof placeholders, so the
only remaining axiom is the paper's open unimodality conjecture.

## File layout

- `Basic`: standard triples, q-integers, reciprocal polynomials, q-Pythagoras equation,
  and conditions Con1--Con3.
- `Classical`: Euclid formula and classical Pythagorean facts.
- `QRationals`: continued fractions, q-deformed matrix action, q-rational numerator and
  denominator, and source properties as theorem skeletons.
- `QPythagorean`: q-Pythagorean matrix, trace formula, explicit A/B/C polynomials, and
  main theorem skeletons.
- `Conjecture`: unimodality definitions and the source conjecture as an axiom.
-/
