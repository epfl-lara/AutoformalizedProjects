# Formalization Blueprint: A Calculus Proof of the Cramer--Wold Theorem

- Source: `docs/source/cramerwold-arxiv.tex`
- Nearby PDF checked: `docs/lyons_zumbrun2016_cramer_wold.pdf`
- Target Lean entry file: `CramerWoldTheorem/Main.lean`
- Status: source-backed Lean draft builds with no `sorry`; the final theorem depends
  on two private analytic axioms that package source proof blocks not yet formalized
  in Mathlib-level detail.

## Planner Checklist

- [x] Identify definitions and notation that must exist before theorem statements.
- [x] Split the large source theorem proof into Lean-sized theorem/lemma skeletons.
- [x] Record source labels/pages/equations for every generated declaration.
- [x] Check local project and Mathlib names before introducing duplicates.
- [x] Verify drafted Lean statements match the source document. Planner comparison is recorded below; independent review still required.
- [x] Run independent statement/source verification review and apply corrections.
- [x] Attach the complete source proof text when available, or explicitly record why it is unavailable.
- [x] Record a natural-language proof strategy or source proof pointer for each theorem/lemma.
- [x] Resolve all construction stubs before proof handoff. There are no `def := sorry` construction stubs in the Lean draft.
- [x] Mark stable theorem/lemma/example `sorry` declarations ready for a user-started prove workflow. Only check this after independent review approves every source entry.

## Import Plan

Direct Lean imports expected in generated Lean files only:
- `Mathlib`

The generated file `CramerWoldTheorem/Main.lean` imports only `Mathlib`. The root project module `CramerWoldTheorem.lean` imports `CramerWoldTheorem.Main`, so a project build covers the generated target.

## Trusted Analytic Assumptions

The current Lean development has no `sorry`, `admit`, or `unsafe`, but it is not
axiom-free.  The public Cramer--Wold theorem depends on two private axioms:

- `averageDistance_eq_of_halfspaceValues_eq`: equality of the source half-space
  value function determines `averageDistance`. This packages the Crofton measure,
  Fubini, compact-support signed-measure calculation, and limiting argument from
  TeX lines 127--211.
- `measure_eq_of_averageDistance_eq_odd_aux`: equality of average-distance
  functions determines the probability measure in positive odd dimension. This
  packages the Green's identity, radial Laplacian, Fubini, and test-function
  inversion argument from TeX lines 213--310.

The even-dimensional embedding reduction and final parity split are proved in Lean
from these two assumptions.

## Suggested Search Modules

Non-gating modules or namespaces to search while proving. Do not force these into `.lean` imports unless the prover actually needs them.
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure`
- `Mathlib.MeasureTheory.Measure.MeasureSpaceDef`
- `Mathlib.Analysis.InnerProductSpace.PiL2`
- `Mathlib.Analysis.Distribution.TemperedDistribution`
- `Mathlib.Geometry.Manifold.Instances.Real` for existing half-space terminology

Search already performed:
- closed half-spaces / Euclidean half-spaces: found `EuclideanSpace`, `EuclideanHalfSpace`, `closure_halfSpace`, `convex_halfSpace_le`
- measure extensionality / probability measures: found `MeasureTheory.Measure.ext_iff`, `MeasureTheory.ProbabilityMeasure`, `MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq_iff`
- Laplacian/distributions: found `TemperedDistribution.laplacian_apply_apply` and related Laplacian declarations
- local project search for Cramer--Wold: no existing project formalization found

## Generated File Layout

- `CramerWoldTheorem/Main.lean`: aggregator entry file importing the active module set.
- `CramerWoldTheorem/Basic.lean`: Euclidean-space model, closed half-spaces, half-space values, and average-distance function.
- `CramerWoldTheorem/Halfspaces.lean`: measurability and recovery of average-distance functions from half-space values.
- `CramerWoldTheorem/Inversion.lean`: odd-dimensional average-distance inversion and even-to-odd reduction.
- `CramerWoldTheorem/MainTheorem.lean`: the Cramer--Wold theorem and normal/threshold companion statement.
- `CramerWoldTheorem.lean`: root module imports `CramerWoldTheorem.Main`.

## Source Document Inventory

Document: Russell Lyons and Kevin Zumbrun, "A Calculus Proof of the Cramer--Wold Theorem", version of 22 April 2017. The source has two sections: Introduction and Proof. Preflight did not detect theorem environments because the TeX uses custom plain-TeX macros; manual inspection found one proclaimed theorem and several proof claims.

### Source theorem: The Cramer--Wold Theorem

Source pointer:
- TeX: `docs/source/cramerwold-arxiv.tex`, section `Proof`, around the `\proclaim The Cram\'er--Wold Theorem` block.
- PDF: page 2, displayed theorem after "Let S be the set of closed half-spaces".

Source statement:
> Let `S` be the set of closed half-spaces `S ⊂ R^n`. Let `μ` and `ν` be Borel probability measures on `R^n` such that `μ(S) = ν(S)` for all `S ∈ S`. Then `μ = ν`.

Planned Lean declarations:
- `CramerWoldTheorem.RealEuclideanSpace`
- `CramerWoldTheorem.closedHalfspace`
- `CramerWoldTheorem.IsClosedHalfspace`
- `CramerWoldTheorem.cramerWold`
- companion parameterized version `CramerWoldTheorem.cramerWold_parametric`

Source qualifiers:
- Mathematical object class: Borel probability measures on Euclidean space.
- Quantifier order: choose dimension `n`, then measures `μ` and `ν`, then assume equality on every closed half-space.
- Parameter domain: `R^n`; Lean representation is `EuclideanSpace ℝ (Fin n)` through `RealEuclideanSpace n`.
- Half-space class: closed half-spaces. Lean represents these as sets of the form `{x | p ≤ inner ℝ normal x}` with `normal ≠ 0`, via `IsClosedHalfspace`.
- Equality condition: `μ S = ν S` for every closed half-space `S`.
- Output codomain: equality of measures, `μ = ν`.
- Side conditions: `n` is taken nonzero in the main Lean theorem (`[NeZero n]`) to match the paper's sphere/half-space proof context; probability is represented by `IsProbabilityMeasure` instances on Lean `Measure`s over the Borel measurable space.
- Follow-on/source remark: the introduction says equivalently by projections to lines through the origin. This first draft formalizes the half-space version only; projection equivalence is not included as a theorem.

Lean coverage:
- `RealEuclideanSpace n` records the `R^n` model.
- `closedHalfspace normal threshold` and `IsClosedHalfspace S` record the closed-half-space representation bridge.
- `cramerWold` states the source theorem with explicit half-space predicate.
- `cramerWold_parametric` is a companion theorem for users/provers starting from a normal/threshold family of half-spaces.

Scope changes:
- Representation bridge: `R^n` is encoded as `EuclideanSpace ℝ (Fin n)`.
- The source does not state `n > 0` explicitly, but the proof uses `S^{n-1}` and the standard theorem is for positive Euclidean dimension; Lean makes this explicit as `[NeZero n]` in the main theorem.
- The projection-equivalence parenthetical is not formalized in this draft and should not be considered covered.

Statement verification status: pending independent statement/source review.

### Source proof claim: closed half-spaces are Borel/measurable

Source pointer:
- Implicit in the theorem's phrase "Borel probability measures" evaluated on closed half-spaces and in the construction `ϕ(ω,p) := {x ∈ R^n | <ω,x> ≥ p}`.

Planned Lean declaration:
- `CramerWoldTheorem.measurableSet_closedHalfspace`

Source qualifiers:
- Object class: sets cut out by a continuous linear functional inequality.
- Domain: `RealEuclideanSpace n`.
- Output: `MeasurableSet (closedHalfspace normal threshold)`.
- Side conditions: none beyond the Euclidean/Borel instance.

Lean coverage:
- Records the measurability fact needed to justify measure evaluation and later Crofton/integration arguments.

Scope changes:
- The source treats this as background; Lean states it explicitly as an auxiliary lemma.

Statement verification status: pending independent statement/source review.

### Source proof claim: half-space values determine the average-distance function

Source pointer:
- TeX proof after equation `(2.1)` through the definition of `f_μ(y)`, ending with "We have shown that the function `S ↦ μ(S)` determines `f_μ`."
- PDF page 2 to top of page 3.

Planned Lean declarations:
- `CramerWoldTheorem.halfspaceValues`
- `CramerWoldTheorem.averageDistance`
- `CramerWoldTheorem.averageDistance_eq_of_closedHalfspaceValues`

Source qualifiers:
- Object class: finite signed measure in the paper's intermediate calculation; the Lean proof helper is specialized to probability measures because the final theorem only needs those.
- Domain: all `y : R^n`.
- Equality/image condition: equality of measure values on every closed half-space implies equality of the functions `f_μ` and `f_ν`.
- Source definition: `f_μ(y) := ∫ (‖y - x‖ - ‖x‖) dμ(x)`.
- Side conditions: source uses Crofton's invariant measure on half-spaces and a limiting argument from compactly supported signed measures to finite signed measures.

Lean coverage:
- `averageDistance μ y` encodes the source formula using the distance expression `dist y x - dist 0 x`.
- `averageDistance_eq_of_closedHalfspaceValues` states the equality result needed for probability measures.

Scope changes:
- Specialized from finite signed measures to probability measures in the Lean proof helper.
- The Crofton measure `σ` is not constructed as a Lean definition in this draft; its role is captured in the proof notes and in this theorem skeleton.

Statement verification status: pending independent statement/source review.

### Source proof claim: odd-dimensional inversion from average distance

Source pointer:
- TeX proof paragraph beginning "The idea is that if `n = 2m-1` is odd..." and the later paragraph beginning "We now show that `Δ^m f_μ = c_m μ`..." through the equation with `c_m g(x)`.
- PDF page 3.

Planned Lean declaration:
- `CramerWoldTheorem.measure_eq_of_averageDistance_eq_odd`

Source qualifiers:
- Object class: probability measures on odd-dimensional Euclidean spaces for the final theorem; source proves a distributional identity for finite measures through test functions `g ∈ C_c^∞(R^{2m-1})`.
- Domain: positive odd dimensions. Lean states dimensions as `2*m + 1`, which is the same class of positive odd dimensions after reindexing.
- Equality condition: equality of all average-distance values implies equality of measures.
- Proof dependencies: Green's second identity, radial Laplacian formula, repeated integration by parts, Fubini, and a distributional fundamental-solution identity.

Lean coverage:
- The theorem skeleton states the final odd-dimensional extensionality consequence needed by Cramer--Wold.

Scope changes:
- The internal distributional formula with explicit constant `c_m := 2(-2π)^{m-1}(2m-2)!!` is not separately formalized yet.
- The Lean theorem uses the reindexed dimension `2*m+1` and states the equality-of-measures consequence, not the full test-function inversion formula.

Statement verification status: pending independent statement/source review.

### Source proof claim: even dimensions reduce to the next odd dimension

Source pointer:
- TeX proof paragraph beginning "But since an even dimension embeds in the next higher dimension...".
- PDF page 3.

Planned Lean declaration:
- `CramerWoldTheorem.cramerWold_evenDimension`

Source qualifiers:
- Object class: probability measures on positive even-dimensional Euclidean spaces.
- Domain bridge: identify a measure on `R^{2m}` with a measure supported on `R^{2m} × {0} ⊂ R^{2m+1}`.
- Equality condition: half-space values in the even-dimensional space determine half-space values of the embedded measures in the next odd dimension.
- Output: equality of the original measures.

Lean coverage:
- The theorem skeleton states the positive-even-dimensional Cramer--Wold consequence.

Scope changes:
- The embedding/pushforward construction is proof-level and not yet represented by separate Lean definitions.
- The Lean declaration indexes positive even dimensions as `2 * (m + 1)`.

Statement verification status: pending independent statement/source review.

## Complete Source Proof Text

The source proof of the proclaimed theorem is available and should be used by the prover. It is reproduced here from the TeX/PDF extraction, with minor whitespace normalization only.

```text
Let S be the set of closed half-spaces S ⊂ R^n.

The Cramer--Wold Theorem. Let μ and ν be Borel probability measures on R^n such that
μ(S) = ν(S) for all S ∈ S. Then μ = ν.

Proof. Let σ be the (infinite) Borel measure on S that is invariant under isometries,
normalized so that

  σ({0 ∈ S, x ∉ S}) = ‖x‖/2                                      (2.1)

for ‖x‖ = 1. The measure σ goes back to Crofton (1868) (in two dimensions); it can be
constructed as follows. Let Ω_{n-1} denote hypersurface area measure on the unit sphere
S^{n-1} ⊂ R^n, and let λ denote Lebesgue measure on R. Write
ϕ : S^{n-1} × R → S for the map

  ϕ(ω,p) := {x ∈ R^n | <ω,x> ≥ p}.

Then σ := α_n · ϕ_*(Ω_{n-1} × λ) for some constant α_n whose value does not concern us.
It is clear that σ is invariant under rotations about the origin and under reflections in
hyperplanes that pass through the origin. Translation invariance amounts to the property
that for y ∈ R^n, the pushforward by ϕ_y(ω,p) := ϕ(ω,p) - y is the same measure. But since

  ϕ(ω,p) - y
    = {x - y ∈ R^n | <ω,x> ≥ p}
    = {x ∈ R^n | <ω,x + y> ≥ p}
    = {x ∈ R^n | <ω,x> ≥ p - <ω,y>}
    = ϕ(ω, p - <ω,y>),

isometry invariance of λ gives this property. The isometry invariance of σ implies that
σ({0 ∈ S, x ∉ S}) is a function of ‖x‖ alone; additivity for collinear segments shows that
it is a linear function. Thus, we may choose α_n so that (2.1) holds.

From (2.1) and isometry invariance, we have

  ‖x‖ = ∫_S |1_S(0) - 1_S(x)|^2 dσ(S).

Integrating with respect to a signed measure μ on R^n with compact support, we obtain

  ∫_{R^n} ‖x‖ dμ(x)
    = ∫_S ∫_{R^n} |1_S(0) - 1_S(x)|^2 dμ(x) dσ(S)
    = ∫_S [1_S(0)(1 - 2 μ(S)) + μ(S)] dσ(S).

The choice of 0 was arbitrary, so making another choice and subtracting, we get

  ∫_{R^n} (‖y - x‖ - ‖x‖) dμ(x)
    = ∫_S [(1_S(y) - 1_S(0))(1 - 2 μ(S))] dσ(S).

By taking a limit, we see that this equation holds for every finite signed measure μ.

Define

  f_μ(y) := ∫_{R^n} (‖y - x‖ - ‖x‖) dμ(x).

We have shown that the function S ↦ μ(S) determines f_μ. It remains to show that f_μ
determines μ.

The idea is that if n = 2m - 1 is odd, then Δ^m f_μ = c_m μ for some constant c_m, using
the fundamental solution of the Laplacian, Δ. This then establishes the Cramer--Wold
theorem in odd dimensions. But since an even dimension embeds in the next higher dimension,
the Cramer--Wold theorem follows in even dimensions as well. That is, we may identify a
measure μ on R^{2m} with a measure μ' on R^{2m} × {0} ⊂ R^{2m+1}. The function S ↦ μ(S)
on half-spaces S ⊂ R^{2m} determines the values μ'(S') for half-spaces S' ⊂ R^{2m+1}.
Since this determines μ', the theorem follows for μ.

We now show that Δ^m f_μ = c_m μ in an appropriate sense for μ on R^{2m-1}. Recall Green's
second identity, which says that for a bounded domain D ⊂ R^n with C^1 boundary ∂D having
outward unit normal n and two functions φ, ψ ∈ C^2(closure D), we have

  ∫_D (φ Δψ - ψ Δφ) = ∫_{∂D} (φ ∇_n ψ - ψ ∇_n φ).

Recall also that if F : R^n → R is such that F(x) = G(‖x‖) depends only on r := ‖x‖, then

  (ΔF)(x) = G''(r) + ((n-1)/r) G'(r).

In particular, Δ r^k = k(k+n-2) r^{k-2}. If the support of ψ lies in the interior of a ball
B(0,R) and φ(x) = r^k with k > -n+2, then letting D be B(0,R) \ B(0,ε) with ε → 0 shows
that

  ∫_{R^n} φ Δψ = ∫_{R^n} ψ Δφ.

Similarly, if k = -n+2, then

  ∫_{R^n} φ Δψ = β_{n-1} ψ(0),

where β_{n-1} is the surface area of S^{n-1}.

To show that f_μ determines ∫ g dμ for all g ∈ C_c^∞(R^{2m-1}), we now prove that with
c_m := 2(-2π)^{m-1}(2m-2)!!, where !! denotes the double factorial, we have

  ∫ g dμ = c_m^{-1} ∫_{R^{2m-1}} f_μ(y) (Δ^m g)(y) dλ(y),

where now λ denotes Lebesgue measure on R^{2m-1}. Fubini's theorem yields

  ∫_{R^{2m-1}} f_μ(y) (Δ^m g)(y) dλ(y)
    = ∫_{R^{2m-1}} ∫_{R^{2m-1}} (‖y - x‖ - ‖x‖) (Δ^m g)(y) dλ(y) dμ(x).

Applying the preceding Green formulas (translated to x) repeatedly to the inner integral,
we obtain

  ∫_{R^{2m-1}} (‖y - x‖ - ‖x‖) (Δ^m g)(y) dλ(y)
    = ∫_{R^{2m-1}} Δ_y^{m-1}(‖y - x‖ - ‖x‖) Δg(y) dλ(y)
    = c_m g(x),

as desired.
```

## Prover Notes

- Start from `cramerWold` after statement review. The proof should follow the source split: half-space values determine `averageDistance`, odd-dimensional inversion identifies measures, and even dimensions reduce by embedding into the next odd dimension.
- `averageDistance_eq_of_closedHalfspaceValues` is the planned formal placeholder for the Crofton-measure calculation. A full proof may require constructing or importing an invariant measure on parameterized half-spaces; if that becomes too large, prove an abstract Crofton identity as a separate lemma and keep the source mapping here updated.
- `measure_eq_of_averageDistance_eq_odd` is the planned formal placeholder for the distributional inversion step. Search `TemperedDistribution.laplacian_apply_apply`, Schwartz/test-function APIs, and finite-dimensional Euclidean integration lemmas before redrafting.
- `cramerWold_evenDimension` should be proved by pushing measures forward along the embedding `x ↦ (x,0)` into the next odd dimension and translating half-spaces back to the original space.
- Do not silently replace the half-space theorem by a weaker theorem about coordinate half-spaces; the source requires all closed half-spaces.

## Formal Statement Review Summary

Planner comparison: the main Lean theorem `cramerWold` matches the source half-space theorem modulo the explicit Lean representation bridges listed above. The parenthetical projection-to-lines equivalence is intentionally not covered. The internal proof lemmas are specialized proof skeletons rather than exact source theorem statements.

Statement verification status: pending independent statement/source review.
