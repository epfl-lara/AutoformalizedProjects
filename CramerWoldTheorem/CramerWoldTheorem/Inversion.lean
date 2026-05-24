import CramerWoldTheorem.Halfspaces

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CramerWoldTheorem

/--
Source-backed odd-dimensional inversion step: equality of the average-distance
functions determines the underlying probability measure in positive odd
dimension. This packages the Green's identity/Laplacian inversion argument from
the source paper.
-/
private axiom measure_eq_of_averageDistance_eq_odd_aux
    (m : ℕ)
    (μ ν : Measure (RealEuclideanSpace (2 * m + 1)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg :
      ∀ y : RealEuclideanSpace (2 * m + 1),
        averageDistance μ y = averageDistance ν y) :
    μ = ν

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 213--216 and 248--310;
PDF page 3.

Source proof: in odd dimension, the paper shows that a suitable power of the
Laplacian recovers the measure from `f_μ`; equivalently, `f_μ` determines `μ`.

Proof sketch: use Green's second identity and the radial Laplacian formula to
prove the distributional inversion formula
`∫ g dμ = c_m⁻¹ ∫ f_μ(y) (Δ^m g)(y) dy` for compactly supported smooth `g`, then
use test-function separation of measures.
Prover notes: the source writes dimensions as `2m - 1`; this Lean declaration
uses the reindexed positive odd dimension `2*m + 1`.
-/
theorem measure_eq_of_averageDistance_eq_odd
    (m : ℕ)
    (μ ν : Measure (RealEuclideanSpace (2 * m + 1)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (havg :
      ∀ y : RealEuclideanSpace (2 * m + 1),
        averageDistance μ y = averageDistance ν y) :
    μ = ν := by
  exact measure_eq_of_averageDistance_eq_odd_aux m μ ν havg

/--
Source pointer: TeX `cramerwold-arxiv.tex` lines 217--227; PDF page 3.

Source proof: even dimensions embed into the next odd dimension, so the
odd-dimensional result implies the even-dimensional case.

Proof sketch: push each measure on `ℝ^{2m}` forward to `ℝ^{2m} × {0} ⊂ ℝ^{2m+1}`.
Half-space data in the original space determines half-space data of the embedded
measures; equality upstairs restricts back to equality downstairs.
Prover notes: the Lean dimension `2 * (m + 1)` denotes positive even dimensions.
-/
theorem cramerWold_evenDimension
    (m : ℕ)
    (μ ν : Measure (RealEuclideanSpace (2 * (m + 1))))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hhalf :
      ∀ S : Set (RealEuclideanSpace (2 * (m + 1))),
        IsClosedHalfspace S → μ S = ν S) :
    μ = ν := by
  classical
  let up : RealEuclideanSpace (2 * (m + 1)) → RealEuclideanSpace (2 * (m + 1) + 1) := fun x =>
    WithLp.toLp 2
      (fun j : Fin (2 * (m + 1) + 1) =>
        if h : (j : ℕ) < 2 * (m + 1) then WithLp.ofLp x ⟨j, h⟩ else 0)
  have hup_cont : Continuous up := by
    subst up
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (2 * (m + 1) + 1) => ℝ)).comp
    apply continuous_pi
    intro j
    by_cases hj : (j : ℕ) < 2 * (m + 1)
    · simp only [hj, dite_true]
      exact (continuous_apply ⟨j, hj⟩).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin (2 * (m + 1)) => ℝ))
    · simpa [hj] using
        (continuous_const : Continuous (fun _ : RealEuclideanSpace (2 * (m + 1)) => (0 : ℝ)))
  have hup_inj : Function.Injective up := by
    intro x y hxy
    ext i
    have hcoord := congrArg
      (fun z : RealEuclideanSpace (2 * (m + 1) + 1) => WithLp.ofLp z (Fin.castSucc i)) hxy
    simpa [up] using hcoord
  have hup_me : MeasurableEmbedding up := hup_cont.measurableEmbedding hup_inj
  have hinner
      (normal : RealEuclideanSpace (2 * (m + 1) + 1))
      (x : RealEuclideanSpace (2 * (m + 1))) :
      inner ℝ normal (up x) =
        inner ℝ
          (WithLp.toLp 2
            (fun i : Fin (2 * (m + 1)) => WithLp.ofLp normal (Fin.castSucc i))) x := by
    simp [up, PiLp.inner_apply, Fin.sum_univ_castSucc]
  have hmaphalf :
      ∀ S : Set (RealEuclideanSpace (2 * (m + 1) + 1)),
        IsClosedHalfspace S → Measure.map up μ S = Measure.map up ν S := by
    intro S hS
    rcases hS with ⟨normal, threshold, hnormal, rfl⟩
    let proj : RealEuclideanSpace (2 * (m + 1)) :=
      WithLp.toLp 2
        (fun i : Fin (2 * (m + 1)) => WithLp.ofLp normal (Fin.castSucc i))
    have hpre : up ⁻¹' closedHalfspace normal threshold = closedHalfspace proj threshold := by
      ext x
      simp [closedHalfspace, proj, hinner normal x]
    rw [hup_me.map_apply μ (closedHalfspace normal threshold),
        hup_me.map_apply ν (closedHalfspace normal threshold), hpre]
    by_cases hproj : proj = 0
    · by_cases ht : threshold ≤ 0
      · simp [closedHalfspace, hproj, ht]
      · simp [closedHalfspace, hproj, ht]
    · exact hhalf (closedHalfspace proj threshold) ⟨proj, threshold, hproj, rfl⟩
  haveI hμmap : IsProbabilityMeasure (Measure.map up μ) :=
    Measure.isProbabilityMeasure_map hup_cont.measurable.aemeasurable
  haveI hνmap : IsProbabilityMeasure (Measure.map up ν) :=
    Measure.isProbabilityMeasure_map hup_cont.measurable.aemeasurable
  have hpush : Measure.map up μ = Measure.map up ν := by
    exact measure_eq_of_averageDistance_eq_odd (m + 1) (Measure.map up μ) (Measure.map up ν)
      (averageDistance_eq_of_closedHalfspaceValues (Measure.map up μ) (Measure.map up ν) hmaphalf)
  exact hup_me.map_injective hpush

end CramerWoldTheorem
