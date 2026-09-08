import LeanFlowProofs.PB021OccurrenceSuccessorsStrict
import Mathlib

theorem LeanFlow.pb021_no_large_large {c : ℕ → ℕ} {N B : ℕ} (hN : 0 < N) (hpos : ∀ i : ℕ, 0 < i → 0 < c i) (hNB : N ≤ B) (hinit : ∀ i : ℕ, 1 ≤ i → i ≤ N → c i ≤ B) (hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card) : ∀ t : ℕ, N ≤ t → c t ≤ B ∨ c (t + 1) ≤ B := by classical
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    by_cases hsmall : c t ≤ B
    · exact Or.inl hsmall
    right
    let S := (Finset.Icc 1 t).filter (fun i => c i = c t)
    have hmem : ∀ i ∈ S, N < i ∧ i ≤ t ∧ c i = c t := by
      intro i hi
      obtain ⟨hi, heq⟩ := Finset.mem_filter.mp hi
      obtain ⟨hi1, hit⟩ := Finset.mem_Icc.mp hi
      have : N < i := by
        by_contra hn
        have := hinit i hi1 (by omega)
        rw [heq] at this
        exact hsmall this
      exact ⟨this, hit, heq⟩
    have hmap : ∀ i ∈ S, c (i - 1) ∈ Finset.Icc 1 B := by
      intro i hi
      obtain ⟨hNi, hit, heq⟩ := hmem i hi
      have hip : i - 1 + 1 = i := by omega
      have hprev := ih (i - 1) (by omega) (by omega)
      rw [hip, heq] at hprev
      have hb : c (i - 1) ≤ B := hprev.resolve_right hsmall
      exact Finset.mem_Icc.mpr ⟨hpos (i - 1) (by omega), hb⟩
    have hinj : Set.InjOn (fun i => c (i - 1)) (↑S : Set ℕ) := by
      intro i hi j hj heq
      obtain ⟨hNi, hit, hei⟩ := hmem i hi
      obtain ⟨hNj, hjt, hej⟩ := hmem j hj
      have hip : i - 1 + 1 = i := by omega
      have hjp : j - 1 + 1 = j := by omega
      rcases lt_trichotomy i j with hij | hij | hij
      · have hs := LeanFlow.pb021_occurrence_successors_strict hN hrule
          (u := i - 1) (v := j - 1) (by omega) (by omega) heq
        rw [hip, hjp, hei, hej] at hs
        omega
      · exact hij
      · have hs := LeanFlow.pb021_occurrence_successors_strict hN hrule
          (u := j - 1) (v := i - 1) (by omega) (by omega) heq.symm
        rw [hip, hjp, hei, hej] at hs
        omega
    have hcard : S.card ≤ (Finset.Icc 1 B).card :=
      Finset.card_le_card_of_injOn (fun i => c (i - 1)) hmap hinj
    rw [hrule t ht]
    simpa [S] using hcard
