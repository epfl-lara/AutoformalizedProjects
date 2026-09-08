import LeanFlowProofs.PB021NoLargeLarge
import LeanFlowProofs.PB021OccurrenceSuccessorsStrict
import Mathlib

theorem LeanFlow.pb021_eventual_small_large_alternation {c : ℕ → ℕ} {N B : ℕ} (hN : 0 < N) (hpos : ∀ i : ℕ, 0 < i → 0 < c i) (hNB : N ≤ B) (hinit : ∀ i : ℕ, 1 ≤ i → i ≤ N → c i ≤ B) (hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card) : ∃ t0 : ℕ, N ≤ t0 ∧ ∀ n : ℕ, c (t0 + 2 * n) ≤ B ∧ B < c (t0 + 2 * n + 1) := by 
  classical
  let S : Set ℕ := {t | N ≤ t ∧ c t ≤ B ∧ c (t + 1) ≤ B}
  have hinj : Set.InjOn (fun t => (c t, c (t + 1))) S := by
    intro u hu v hv he
    have he₁ : c u = c v := congrArg Prod.fst he
    have he₂ : c (u + 1) = c (v + 1) := congrArg Prod.snd he
    rcases lt_trichotomy u v with h | h | h
    · have := pb021_occurrence_successors_strict hN hrule hu.1 h he₁
      omega
    · exact h
    · have := pb021_occurrence_successors_strict hN hrule hv.1 h he₁.symm
      omega
  have hfin : S.Finite := Set.Finite.of_injOn
    (t := (Set.Iic B) ×ˢ (Set.Iic B))
    (by intro t ht; exact ⟨ht.2.1, ht.2.2⟩) hinj
    ((Set.finite_Iic B).prod (Set.finite_Iic B))
  obtain ⟨K, hK⟩ := hfin.toFinset.exists_nat_subset_range
  have hnext : ∀ t, max N K ≤ t → c t ≤ B → B < c (t + 1) := by
    intro t ht hc
    by_contra hh
    have hm : t ∈ S := ⟨le_trans (le_max_left N K) ht, hc, by omega⟩
    have := Finset.mem_range.mp (hK (hfin.mem_toFinset.mpr hm))
    have := le_trans (le_max_right N K) ht
    omega
  have hll := pb021_no_large_large hN hpos hNB hinit hrule
  have hstart : ∃ t0, max N K ≤ t0 ∧ c t0 ≤ B := by
    rcases hll (max N K) (le_max_left N K) with h | h
    · exact ⟨max N K, le_rfl, h⟩
    · exact ⟨max N K + 1, by omega, h⟩
  obtain ⟨t0, ht0, hc0⟩ := hstart
  refine ⟨t0, le_trans (le_max_left N K) ht0, ?_⟩
  intro n
  induction n with
  | zero =>
    simpa using And.intro hc0 (hnext t0 ht0 hc0)
  | succ n ih =>
    have ht : N ≤ t0 + 2 * n + 1 := by omega
    have hs : c (t0 + 2 * n + 2) ≤ B := by
      rcases hll (t0 + 2 * n + 1) ht with h | h
      · omega
      · simpa [Nat.add_assoc] using h
    have hs' : c (t0 + 2 * (n + 1)) ≤ B := by
      convert hs using 1 <;> congr 1 <;> omega
    exact ⟨hs', hnext _ (by omega) hs'⟩
