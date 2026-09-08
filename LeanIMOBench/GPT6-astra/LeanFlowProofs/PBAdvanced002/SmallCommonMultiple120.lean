import Mathlib

theorem LeanFlowPB002.small_common_multiple_120 (m : ℕ) (c : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < c i)
    (hsum : Finset.sum Finset.univ c ≤ 120) :
    ∃ P : ℕ, 0 < P ∧ (∀ i : Fin m, c i ∣ P) ∧ P ≤ 3 * 2^60 := by classical
  have hlarge : ∀ n : ℕ, 4 ≤ n → n^2 ≤ 2^n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [pow_succ (2 : ℕ) n]
      nlinarith
  have hsmall : ∀ n : ℕ, n ≠ 3 → n^2 ≤ 2^n := by
    intro n hn
    by_cases h : 4 ≤ n
    · exact hlarge n h
    · interval_cases n <;> norm_num at *
  let D := Finset.univ.image c
  let E := D.erase 3
  have himage : ∀ s : Finset (Fin m), (s.image c).sum id ≤ s.sum c := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.image_insert, Finset.sum_insert ha]
      by_cases h : c a ∈ s.image c
      · rw [Finset.insert_eq_of_mem h]
        exact ih.trans (Nat.le_add_left _ _)
      · rw [Finset.sum_insert h]
        exact Nat.add_le_add_left ih (c a)
  have hsumD : D.sum id ≤ 120 := (himage Finset.univ).trans hsum
  have hsumE : E.sum id ≤ 120 := by
    exact (Finset.sum_le_sum_of_subset (Finset.erase_subset 3 D)).trans hsumD
  have hprod : ∀ s : Finset ℕ, (∀ n ∈ s, n ≠ 3) → (s.prod id)^2 ≤ 2^(s.sum id) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      intro h
      rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_pow, pow_add]
      exact Nat.mul_le_mul (hsmall a (h a (by simp))) (ih (by intro n hn; exact h n (by simp [hn])))
  have hQ : E.prod id ≤ 2^60 := by
    have h := hprod E (by intro n hn; exact (Finset.mem_erase.mp hn).1)
    have hpow : (2:ℕ)^(E.sum id) ≤ 2^120 := Nat.pow_le_pow_right (by decide) hsumE
    have : (E.prod id)^2 ≤ 2^120 := h.trans hpow
    norm_num at this ⊢
    nlinarith
  refine ⟨D.prod id, ?_, ?_, ?_⟩
  · apply Finset.prod_pos
    intro n hn
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
    exact hpos i
  · intro i
    exact Finset.dvd_prod_of_mem id (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · by_cases h3 : 3 ∈ D
    · have heq : D.prod id = 3 * E.prod id := by
        simpa [E] using (Finset.mul_prod_erase D id h3).symm
      rw [heq]
      omega
    · have heq : E = D := by simp [E, h3]
      rw [heq] at hQ
      omega
