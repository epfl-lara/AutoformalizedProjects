import CramerWoldTheorem.Halfspaces
import CramerWoldTheorem.Inversion

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CramerWoldTheorem

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 121--125 for the statement and
127--311 for the proof; PDF pages 2--3.

Source proof: this is the proclaimed Cramer--Wold theorem. The paper first uses
Crofton's measure on half-spaces to recover the average-distance function from
half-space values, then uses odd-dimensional Laplacian inversion and an
even-to-odd embedding reduction to recover the measure.

Proof sketch: combine `averageDistance_eq_of_closedHalfspaceValues`,
`measure_eq_of_averageDistance_eq_odd`, and `cramerWold_evenDimension`, splitting
on the parity of the positive dimension.
Prover notes: the source's `ℝ^n` is represented by `RealEuclideanSpace n`, and
closed half-spaces are represented by `IsClosedHalfspace`.
-/
theorem cramerWold
    {n : ℕ} [NeZero n]
    (μ ν : Measure (RealEuclideanSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hhalf : ∀ S : Set (RealEuclideanSpace n), IsClosedHalfspace S → μ S = ν S) :
    μ = ν := by
  rcases Nat.even_or_odd' n with ⟨k, hk | hk⟩
  · cases k with
    | zero =>
        exfalso
        exact (NeZero.ne n) (by simpa using hk)
    | succ m =>
        subst n
        simpa [Nat.succ_eq_add_one] using cramerWold_evenDimension m μ ν hhalf
  · subst n
    exact measure_eq_of_averageDistance_eq_odd k μ ν
      (averageDistance_eq_of_closedHalfspaceValues μ ν hhalf)

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 142--147 for the parameterized
half-space map `ϕ(ω,p)`, together with theorem lines 123--125; PDF page 2.

Source proof / representation bridge: a common way to provide the source's
half-space data is by giving values for every normal vector and threshold.

Proof sketch: convert the parameterized hypothesis into the `IsClosedHalfspace`
form used by `cramerWold`.
Prover notes: this companion statement is not a separate theorem in the paper;
it records the bridge from `{x | ⟪normal, x⟫ ≥ threshold}` to the source set `𝒮`.
-/
theorem cramerWold_parametric
    {n : ℕ} [NeZero n]
    (μ ν : Measure (RealEuclideanSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hhalf :
      ∀ (normal : RealEuclideanSpace n) (threshold : ℝ),
        normal ≠ 0 → μ (closedHalfspace normal threshold) =
          ν (closedHalfspace normal threshold)) :
    μ = ν := by
  exact cramerWold μ ν (by
    intro S hS
    rcases hS with ⟨normal, threshold, hnormal, rfl⟩
    exact hhalf normal threshold hnormal)

end CramerWoldTheorem
