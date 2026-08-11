import Mathlib

namespace IMO2026P3

lemma reciprocal_le_of_sum_eq_one_of_le {N : ℕ} (f : Fin (N + 1) → ℝ)
    (hmax : ∀ i, f i ≤ f 0)
    (htotal : (∑ i : Fin (N + 1), f i) = 1) :
    1 / ((N : ℝ) + 1) ≤ f 0 := by
  have hs : (1 : ℝ) ≤ ((N : ℝ) + 1) * f 0 := by
    calc
      (1 : ℝ) = ∑ i : Fin (N + 1), f i := htotal.symm
      _ ≤ ∑ i : Fin (N + 1), f 0 := by
        exact Finset.sum_le_sum (fun i hi => hmax i)
      _ = ((N : ℝ) + 1) * f 0 := by simp
  have hden : 0 < (N : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

end IMO2026P3
