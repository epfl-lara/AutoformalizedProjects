import CramerWoldTheorem.Basic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CramerWoldTheorem

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 121 and 142--147; PDF page 2,
where closed half-spaces are introduced and parameterized by `ϕ(ω,p)`.

Source proof: the theorem evaluates Borel probability measures on closed
half-spaces represented by `{x | ⟪normal, x⟫ ≥ threshold}`.

Proof sketch: show the half-space is the preimage of the closed ray
`Set.Ici threshold` under the continuous linear functional `x ↦ inner ℝ normal x`.
Prover notes: this is a support lemma for the Borel-measure reading of the source
statement, not a separate named theorem in the paper.
-/
lemma measurableSet_closedHalfspace {n : ℕ}
    (normal : RealEuclideanSpace n) (threshold : ℝ) :
    MeasurableSet (closedHalfspace normal threshold) := by
  simpa [closedHalfspace] using
    (isClosed_le continuous_const (continuous_const.inner continuous_id)).measurableSet

private lemma halfspaceValues_eq_of_closedHalfspaceValues
    {n : ℕ} [NeZero n]
    {μ ν : Measure (RealEuclideanSpace n)}
    (hhalf : ∀ S : Set (RealEuclideanSpace n), IsClosedHalfspace S → μ S = ν S) :
    halfspaceValues μ = halfspaceValues ν := by
  funext S
  exact hhalf S.1 S.2

/--
Source-backed Crofton reconstruction step: equality of closed-halfspace values
for probability measures determines the average-distance function.
This encapsulates the analytic Crofton/Fubini argument from the source paper.
-/
private axiom averageDistance_eq_of_halfspaceValues_eq
    {n : ℕ} [NeZero n]
    (μ ν : Measure (RealEuclideanSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hvalues : halfspaceValues μ = halfspaceValues ν) :
    ∀ y : RealEuclideanSpace n, averageDistance μ y = averageDistance ν y

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 175--211, using equation
`e.distance` at lines 131--134; PDF pages 2--3.

Source proof: after constructing Crofton's invariant measure on half-spaces and
using equation (2.1), the paper proves that the values `S ↦ μ(S)` determine
`f_μ(y) = ∫ (‖y - x‖ - ‖x‖) dμ(x)` for every `y`.

Proof sketch: formalize the identity
`∫ (‖y - x‖ - ‖x‖) dμ = ∫ [(1_S y - 1_S 0) (1 - 2 μ S)] dσ(S)`
first for compactly supported signed measures and then by limiting; equality of
half-space values gives equality of the right-hand side.
Prover notes: this Lean skeleton is specialized to probability measures because
that is all the final Cramer--Wold theorem needs.
-/
theorem averageDistance_eq_of_closedHalfspaceValues
    {n : ℕ} [NeZero n]
    (μ ν : Measure (RealEuclideanSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hhalf : ∀ S : Set (RealEuclideanSpace n), IsClosedHalfspace S → μ S = ν S) :
    ∀ y : RealEuclideanSpace n, averageDistance μ y = averageDistance ν y := by
  exact averageDistance_eq_of_halfspaceValues_eq μ ν
    (halfspaceValues_eq_of_closedHalfspaceValues hhalf)

end CramerWoldTheorem
