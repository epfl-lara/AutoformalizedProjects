import CramerWoldTheorem.Basic

open MeasureTheory
open scoped BigOperators ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

noncomputable section

namespace CramerWoldTheorem.OddInversion

/-- The positive odd Euclidean space used by the inversion endpoint. -/
abbrev OddSpace (m : ℕ) := RealEuclideanSpace (2 * m + 1)

/--
The centered distance kernel whose `μ`-integral is `averageDistance μ y`.

For source dimension `d = 2 * q - 1`, the paper applies `Δ ^ q`.  In this
Lean reindexing `d = 2 * m + 1`, so the expected recovery power is `m + 1`.
-/
def centeredDistanceKernel (m : ℕ) (x y : OddSpace m) : ℝ :=
  dist y x - dist (0 : OddSpace m) x

end CramerWoldTheorem.OddInversion
