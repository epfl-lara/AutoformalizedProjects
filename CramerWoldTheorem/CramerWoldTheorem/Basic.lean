import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CramerWoldTheorem

/-- The Lean model of the source document's `ℝ^n`. -/
abbrev RealEuclideanSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed half-space `{x | ⟪normal, x⟫ ≥ threshold}` used to model the
source's closed half-spaces in Euclidean space. -/
def closedHalfspace {n : ℕ} (normal : RealEuclideanSpace n) (threshold : ℝ) :
    Set (RealEuclideanSpace n) :=
  {x | threshold ≤ inner ℝ normal x}

/-- Predicate for the source set `𝒮` of closed half-spaces. A set is represented
by a nonzero normal vector and a threshold. -/
def IsClosedHalfspace {n : ℕ} (S : Set (RealEuclideanSpace n)) : Prop :=
  ∃ normal : RealEuclideanSpace n, ∃ threshold : ℝ,
    normal ≠ 0 ∧ S = closedHalfspace normal threshold

/-- The source's half-space data function `S ↦ μ(S)`, with domain restricted to
closed half-spaces. -/
def halfspaceValues {n : ℕ} (μ : Measure (RealEuclideanSpace n)) :
    {S : Set (RealEuclideanSpace n) // IsClosedHalfspace S} → ENNReal :=
  fun S => μ S.1

/-- The average-distance function `f_μ(y) = ∫ (‖y - x‖ - ‖x‖) dμ(x)` from the
source proof. -/
noncomputable def averageDistance {n : ℕ} (μ : Measure (RealEuclideanSpace n))
    (y : RealEuclideanSpace n) : ℝ :=
  ∫ x, (dist y x - dist (0 : RealEuclideanSpace n) x) ∂μ

end CramerWoldTheorem
