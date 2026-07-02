/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
import CramerWoldTheorem.Basic
import CramerWoldTheorem.Halfspaces
import CramerWoldTheorem.Inversion
import CramerWoldTheorem.MainTheorem

/-! # A Calculus Proof of the Cramer--Wold Theorem

Source-backed Lean statements for Lyons and Zumbrun's calculus proof of the
Cramer--Wold theorem.

## File layout

- `Basic`: Euclidean-space model, closed half-spaces, half-space values, and
  average-distance function.
- `Halfspaces`: measurability and recovery of average-distance functions from
  half-space values.
- `Inversion`: odd-dimensional average-distance inversion and even-to-odd
  reduction.
- `MainTheorem`: the Cramer--Wold theorem and the normal/threshold parameterized
  companion statement.
-/
