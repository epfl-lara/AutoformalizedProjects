# Formalization Blueprint: docs/QuantizingPythagoreanTriples/Pythagore2.tex

- Source: `docs/QuantizingPythagoreanTriples/Pythagore2.tex`
- Target Lean entry file: `Pythagore2/Main.lean`
- Status: reorganized source-backed statement skeleton; q-rational axioms removed; only the paper's open unimodality conjecture remains an axiom

## Current Rating

- Statement/source coverage: 8/10. The standard triples, q-deformed equation, conditions Con1--Con3, continued-fraction/q-matrix construction of q-rationals, q-Pythagorean matrix, trace formula, explicit A/B/C formulas, main existence theorem, and unimodality conjecture are represented.
- Proof completeness: 0/10. This is still a proof skeleton: 22 theorem declarations use `sorry`.
- Axiom discipline: 9/10. The previous q-rational interface axioms were replaced by definitions and theorem skeletons. The only remaining axiom is `unimodality_conjecture`, matching the source's open conjecture.
- Model-readiness: 7/10. The file split gives smaller proof targets, but proving the continued-fraction construction, q-rational positivity, and q-Pythagorean properties remains substantial.

## Planner Checklist

- [x] Identify definitions and notation that must exist before theorem statements.
- [x] Split large source theorems into Lean-sized lemmas.
- [x] Record source labels/pages/equations for generated declarations.
- [x] Replace inappropriate axioms with source-backed definitions plus `theorem ... := by sorry`.
- [x] Keep the open unimodality conjecture as an axiom.
- [x] Reorganize Lean files into smaller model-facing proof targets.
- [x] Verify the reorganized aggregator builds.
- [x] Run independent statement/source verification review after the split.
- [x] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow.
- [x] Complete proofs and remove `sorry`.

## Import Plan

Direct external import:
- `Pythagore2/Basic.lean` imports `Mathlib`.

Local import chain:
- `Pythagore2/Classical.lean` imports `Pythagore2.Basic`.
- `Pythagore2/QRationals.lean` imports `Pythagore2.Basic`.
- `Pythagore2/QPythagorean.lean` imports `Pythagore2.Classical` and `Pythagore2.QRationals`.
- `Pythagore2/Conjecture.lean` imports `Pythagore2.QPythagorean`.
- `Pythagore2/Main.lean` imports all Pythagore2 modules as an aggregator.

## Suggested Search Modules

Non-gating modules or namespaces to search while proving:
- `Mathlib.NumberTheory.PythagoreanTriples`
- `Mathlib.Data.Polynomial.Basic`
- `Mathlib.LinearAlgebra.Matrix`
- `Mathlib.Data.Int.GCD`
- `Mathlib.Data.Rat.Defs`
- `Mathlib.Data.Matrix.Notation`

## Generated File Layout

- Aggregator entry file: `Pythagore2/Main.lean`
- Shared definitions and source conditions: `Pythagore2/Basic.lean`
- Classical Euclid formula inputs: `Pythagore2/Classical.lean`
- q-rationals from odd continued fractions and q-matrix words: `Pythagore2/QRationals.lean`
- q-Pythagorean matrix, trace formula, explicit A/B/C, and main theorem: `Pythagore2/QPythagorean.lean`
- Unimodality conjecture: `Pythagore2/Conjecture.lean`
- Current proof obligations: 22 `sorry` declarations.
- Current axioms: 1, `unimodality_conjecture`.

## Definitions and Construction Objects

| Lean name | File | Source concept | Description |
|-----------|------|----------------|-------------|
| `StandardPythagoreanTriple` | `Basic.lean` | standard Pythagorean triple | positive `a,b,c`, Pythagoras equation, gcd in `{1,2}`, parity convention |
| `qInteger` | `Basic.lean` | `[n]_q` | finite sum `1 + q + ... + q^(n-1)` |
| `reciprocalPolynomial` | `Basic.lean` | `C*(q)` | `q^(deg C) C(q^-1)` as coefficient reversal |
| `reciprocalPolynomialWithDegree` | `Basic.lean` | `q^d P(q^-1)` | explicit-degree reciprocal used for q-rational inverse formulas |
| `IsSelfReciprocal` | `Basic.lean` | palindromic polynomial | equality with reciprocal |
| `HasNonNegativeCoefficients` | `Basic.lean` | nonnegative coefficients | all integer coefficients are nonnegative |
| `HasPositiveCoefficients` | `Basic.lean` | positive integer coefficients | nonzero and nonnegative coefficients |
| `IsQDeformedPythagoreanTriple` | `Basic.lean` | q-Pythagoras equation | `A^2 + q B^2 = C C*` |
| `CorrespondsToPythagoreanTriple` | `Basic.lean` | q-analogue correspondence | evaluation at `q=1` gives `(a,b,c)` |
| `IsFullyMonic` | `Basic.lean` | Con3 monic | leading and constant coefficients equal `1` |
| `QDeformedSolutionConditions` | `Basic.lean` | Con1--Con3 | positivity, self-reciprocity, and monicity package |
| `finiteContinuedFractionValue` | `QRationals.lean` | finite continued fraction | value of `[a_1,...,a_k]` |
| `OddContinuedFractionExpansion` | `QRationals.lean` | odd continued fraction data | chosen odd-length expansion for `m/n` |
| `Rq`, `Lq` | `QRationals.lean` | q-deformed generators | matrices from source equation `Gens` |
| `qMatrixWord` | `QRationals.lean` | `A_q` | product `R_q^a1 L_q^a2 ...` |
| `qTransposeMatrixWord` | `QRationals.lean` | `A_q^T` | source q-transposed word |
| `qRationalMatrix` | `QRationals.lean` | matrix for `[m/n]_q` | `A_q` for chosen continued fraction |
| `qRationalNum`, `qRationalDen` | `QRationals.lean` | numerator/denominator | second column of `A_q` |
| `qRationalDegreeBound` | `QRationals.lean` | `d=max(deg N,deg D)` | degree bound in inverse formula |
| `X0q` | `QPythagorean.lean` | degenerate matrix `X_0` | source starting matrix |
| `qPythagoreanMatrix` | `QPythagorean.lean` | `X_{m/n}(q)` | `A_q X_0 A_q^T` |
| `qMatrixTrace` | `QPythagorean.lean` | trace | trace of a 2-by-2 polynomial matrix |
| `qPythagoreanA`, `qPythagoreanB`, `qPythagoreanC` | `QPythagorean.lean` | explicit formulas | formulas `qEucl1`--`qEucl3` |
| `IsUnimodal`, `IsUnimodalPolynomial` | `Conjecture.lean` | unimodality | coefficient-sequence unimodality |

## Source Statement Inventory

### Standard Triples

- Kind: definition
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:189-217`
- Lean declarations: `StandardPythagoreanTriple`
- File: `Pythagore2/Basic.lean`
- Lean coverage: exact definition skeleton
- Scope changes: none
- Proof status: definition, no proof obligation

### Euclid Formula

- Kind: theorem
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:219-238`
- Lean declarations: `euclid_formula_standard`, `euclid_formula_is_pythagorean`
- File: `Pythagore2/Classical.lean`
- Lean coverage: exact for the standard-triple classification target; supporting forward formula added for proof ergonomics
- Scope changes: Lean uses `m > n` for standard triples because positive `b = m^2 - n^2` excludes `m = n`
- Proof notes: use Mathlib Pythagorean triple classification or prove primitive and gcd-2 cases directly

### q-Integers and q-Pythagoras Equation

- Kind: definitions
- Source locators:
  - q-integer: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:298-301`
  - reciprocal: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:270-274`
  - conditions Con1--Con3: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:337-350`
  - correspondence: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:353-360`
- Lean declarations: `qInteger`, `reciprocalPolynomial`, `IsQDeformedPythagoreanTriple`, `CorrespondsToPythagoreanTriple`, `IsFullyMonic`, `QDeformedSolutionConditions`
- File: `Pythagore2/Basic.lean`
- Lean coverage: exact definitions, with `IsFullyMonic` explicitly capturing the source's leading-and-lower-coefficient monic condition
- Scope changes: `HasPositiveCoefficients` is encoded as nonzero plus nonnegative coefficients, matching the previous formalization's support-aware reading of "positive coefficients"

### q-Rational Construction

- Kind: definitions and theorem skeletons
- Source locators:
  - odd continued fractions: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:645-659`
  - intrinsic q-rational recurrences: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:691-712`
  - q-generators: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:722-735`
  - explicit matrix formula: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:747-755`
  - total positivity: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:780-794`
  - inverse numerator/denominator formula: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:800-820`
- Lean declarations: `OddContinuedFractionExpansion`, `exists_oddContinuedFractionExpansion`, `Rq`, `Lq`, `qMatrixWord`, `qTransposeMatrixWord`, `qRationalNum`, `qRationalDen`, `qRationalEvalOne`, `qRationalMonicNonnegative`, `qRationalNumDenReciprocal`, `qRationalTotalPositivity`
- File: `Pythagore2/QRationals.lean`
- Lean coverage: proper construction skeleton; q-rational numerator and denominator are definitions, not axioms
- Scope changes: the chosen continued fraction expansion is selected noncomputably from an existence theorem; independence of this choice remains part of the proof burden
- Proof notes: prove finite continued fraction existence, show matrix construction agrees with the q-rational recurrences, prove positivity/degree/inverse properties from q-rational theory

### q-Pythagorean Matrix and Trace

- Kind: definition/proposition
- Source locators:
  - matrix `X_0`: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:562-570`
  - q-matrix `X_{m/n}(q)`: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:855-869`
  - trace formula: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:893-904`
- Lean declarations: `X0q`, `qPythagoreanMatrix`, `qMatrixTrace`, `qPythagoreanMatrix_trace`
- File: `Pythagore2/QPythagorean.lean`
- Lean coverage: exact construction skeleton
- Proof notes: expand the second column of `A_q` and second row of `A_q^T`, multiply through `X_0`, then compute the trace

### Main Explicit Formulas

- Kind: theorem
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:966-1022`
- Lean declarations: `qPythagoreanA`, `qPythagoreanB`, `qPythagoreanC`, `qPythagoreanC_reciprocal`, `qPythagoreanTriple_satisfies_equation`
- File: `Pythagore2/QPythagorean.lean`
- Lean coverage: exact statement skeleton for formulas `qEucl1`--`qEucl3` and the q-Pythagoras equation
- Scope changes: none
- Proof notes: compute `C*` via the inverse q-rational formula, then apply the Brahmagupta-Fibonacci identity in the polynomial ring

### n/1 Family

- Kind: displayed family
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:383-392`
- Lean declarations: `qPythagorean_n_over_one_formulas`
- File: `Pythagore2/QPythagorean.lean`
- Lean coverage: exact statement skeleton for the source's displayed special family
- Scope changes: Lean assumes `1 < n`, the nondegenerate case used in the family

### Properties Con1--Con3

- Kind: proposition
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:1039-1095`
- Lean declarations: `qPythagoreanTriple_selfReciprocal`, `qPythagoreanTriple_monic_positive`, `qPythagoreanC_reciprocal_monic`, `qPythagoreanTriple_conditions`
- File: `Pythagore2/QPythagorean.lean`
- Lean coverage: exact for the nondegenerate standard-triple range `m > n`
- Scope changes: source states `m/n >= 1`; Lean uses `m > n` because `m = n` makes `B = 0` and does not produce a positive classical triple
- Proof notes: use inverse q-rational formulas for self-reciprocity; use monicity, constant-term, degree, and total positivity properties of q-rationals for Con1 and Con3

### Main Existence Theorem

- Kind: theorem
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:373-379`
- Lean declarations: `exists_qPythagoreanTriple`
- File: `Pythagore2/QPythagorean.lean`
- Lean coverage: exact statement skeleton
- Scope changes: none beyond the `m > n` Euclid parameter generated from standard positive triples
- Proof notes: use `euclid_formula_standard` to obtain `m,n`, instantiate `qPythagoreanA/B/C`, then combine `qPythagoreanTriple_satisfies_equation`, `qPythagoreanTriple_conditions`, and `qPythagoreanTriple_corresponds`

### Unimodality Conjecture

- Kind: conjecture
- Source locator: `docs/QuantizingPythagoreanTriples/Pythagore2.tex:409-429`
- Lean declarations: `IsUnimodal`, `IsUnimodalPolynomial`, `unimodality_conjecture`
- File: `Pythagore2/Conjecture.lean`
- Lean coverage: exact
- Scope changes: declared as an `axiom` because the paper states it as an open conjecture
- Proof status: intentionally not in the proof queue

## Known Scope Notes

- q-rational recurrence formulas are represented through the continued-fraction/matrix construction and source properties; a future refinement could add explicit rational-function recurrence lemmas for `[m/n + 1]_q` and `[-n/m]_q`.
- The full `SL(2,Z)`/`PSL(2,Z)` group action is not formalized as a group action object. The construction uses the source's matrix generators and words, which is sufficient for the q-rational and q-Pythagorean statements currently targeted.
- The q-transpose is encoded for the source words rather than as a general operation on all q-polynomial matrices, avoiding rational functions with `q^{-1}` in the polynomial ring.
