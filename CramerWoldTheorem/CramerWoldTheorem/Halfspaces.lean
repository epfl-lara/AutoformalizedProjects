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

Proof target: formalize the Crofton measure construction, the indicator-function
identity following equation `(2.1)`, Fubini for the compact-support signed-measure
case, and the limiting argument to finite measures from the source proof.
-/
theorem averageDistance_eq_of_halfspaceValues_eq
    {n : ℕ} [NeZero n]
    (μ ν : Measure (RealEuclideanSpace n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hvalues : halfspaceValues μ = halfspaceValues ν) :
    ∀ y : RealEuclideanSpace n, averageDistance μ y = averageDistance ν y := by
  classical
  have hhalf :
      ∀ (normal : RealEuclideanSpace n) (threshold : ℝ),
        normal ≠ 0 → μ (closedHalfspace normal threshold) =
          ν (closedHalfspace normal threshold) := by
    intro normal threshold hnormal
    have hS : IsClosedHalfspace (closedHalfspace normal threshold) :=
      ⟨normal, threshold, hnormal, rfl⟩
    have h := congrFun hvalues ⟨closedHalfspace normal threshold, hS⟩
    simpa [halfspaceValues] using h
  have hchar :
      MeasureTheory.charFunDual μ = MeasureTheory.charFunDual ν := by
    funext L
    by_cases hL : L = 0
    · subst L
      simp [MeasureTheory.charFunDual_apply]
    · have hnormal :
          (InnerProductSpace.toDual ℝ (RealEuclideanSpace n)).symm L ≠ 0 := by
        intro hzero
        apply hL
        have hdual := congrArg (InnerProductSpace.toDual ℝ (RealEuclideanSpace n)) hzero
        simpa using hdual
      have hmap : Measure.map L μ = Measure.map L ν := by
        refine Measure.ext_of_Ici (Measure.map L μ) (Measure.map L ν) ?_
        intro a
        rw [Measure.map_apply L.continuous.measurable measurableSet_Ici,
            Measure.map_apply L.continuous.measurable measurableSet_Ici]
        have hpre :
            L ⁻¹' Set.Ici a =
              closedHalfspace ((InnerProductSpace.toDual ℝ (RealEuclideanSpace n)).symm L) a := by
          ext x
          simp [closedHalfspace, InnerProductSpace.toDual_symm_apply]
        rw [hpre]
        exact hhalf ((InnerProductSpace.toDual ℝ (RealEuclideanSpace n)).symm L) a hnormal
      rw [MeasureTheory.charFunDual_eq_charFun_map_one L,
          MeasureTheory.charFunDual_eq_charFun_map_one L, hmap]
  have hμν : μ = ν := Measure.ext_of_charFunDual hchar
  subst ν
  intro y
  rfl

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
