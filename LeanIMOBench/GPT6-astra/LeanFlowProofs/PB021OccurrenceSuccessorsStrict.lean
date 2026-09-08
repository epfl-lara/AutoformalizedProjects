import Mathlib

theorem LeanFlow.pb021_occurrence_successors_strict {c : ℕ → ℕ} {N : ℕ} (hN : 0 < N) (hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card) {u v : ℕ} (hu : N ≤ u) (huv : u < v) (hcv : c u = c v) : c (u + 1) < c (v + 1) := by 
  rw [hrule u hu, hrule v (by omega)]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    exact ⟨⟨hi.1.1, le_trans hi.1.2 (Nat.le_of_lt huv)⟩, hi.2.trans hcv⟩
  · intro heq
    have hv : v ∈ (Finset.Icc 1 v).filter (fun i => c i = c v) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, le_rfl⟩, True.intro⟩
    rw [← heq] at hv
    simp only [Finset.mem_filter, Finset.mem_Icc] at hv
    omega
