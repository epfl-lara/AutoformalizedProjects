import Mathlib

theorem LeanFlowProofs.PB018.pack124 (A : Type*) [Fintype A] [DecidableEq A] (k : ℕ) (hk : 1 ≤ k) (w : A → ℕ) (c : Fin k → ℕ) (hw : ∀ a, w a = 1 ∨ w a = 2 ∨ w a = 4) (htotal : Finset.sum Finset.univ w = Finset.sum Finset.univ c) (hsingle : (Finset.univ.filter (fun i : Fin k => c i % 2 = 1)).card ≤ (Finset.univ.filter (fun a : A => w a = 1)).card) (hfour : (Finset.univ.filter (fun a : A => w a = 4)).card ≤ Finset.sum Finset.univ (fun i : Fin k => c i / 4)) : ∃ f : A → Fin k, ∀ i : Fin k, Finset.sum (Finset.univ.filter (fun a : A => f a = i)) w = c i := by classical
  have pack : ∀ s : Finset A, ∀ c : Fin k → ℕ,
      (∑ a ∈ s, w a) = ∑ i, c i →
      (∑ i, if c i % 2 = 1 then 1 else 0) ≤ (∑ a ∈ s, if w a = 1 then 1 else 0) →
      (∑ a ∈ s, if w a = 4 then 1 else 0) ≤ (∑ i, c i / 4) →
      ∃ f : A → Fin k, ∀ i, (∑ a ∈ s, if f a = i then w a else 0) = c i := by
    intro s
    induction s using Finset.strongInductionOn
    rename_i s ih
    · intro c ht hs hf
      by_cases he : s.Nonempty
      · obtain ⟨a, ha, hmax⟩ := s.exists_max_image w he
        have hwa := hw a
        have hpos : 0 < w a := by omega
        have hc : ∃ i, w a ≤ c i := by
          by_contra hn
          push_neg at hn
          rcases hwa with h1 | h2 | h4
          · have hz : ∑ i, c i = 0 := Finset.sum_eq_zero (by intro i hi; have := hn i; omega)
            have hp := Finset.single_le_sum (fun b hb => Nat.zero_le (w b)) ha
            omega
          · have hn4 : ∀ b ∈ s, w b = 1 ∨ w b = 2 := by
              intro b hb
              have := hmax b hb
              have := hw b
              omega
            have heq : (∑ i, c i) = ∑ i, if c i % 2 = 1 then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              have := hn i
              split_ifs <;> omega
            have hlt : (∑ b ∈ s, if w b = 1 then 1 else 0) < ∑ b ∈ s, w b := by
              apply Finset.sum_lt_sum
              · intro b hb
                split_ifs <;> omega
              · exact ⟨a, ha, by simp [h2]⟩
            omega
          · have hz : (∑ i, c i / 4) = 0 := Finset.sum_eq_zero (by intro i hi; have := hn i; omega)
            have hp := Finset.single_le_sum (f := fun b => if w b = 4 then 1 else 0) (fun b hb => Nat.zero_le _) ha
            simp only [h4, if_true] at hp
            omega
        obtain ⟨j, hj⟩ := hc
        let d : Fin k → ℕ := Function.update c j (c j - w a)
        have hdj : d j = c j - w a := by simp [d]
        have hdi : ∀ i, i ≠ j → d i = c i := by intro i hi; simp [d, hi]
        have sumchange (g : ℕ → ℕ) : (∑ i, g (d i)) + g (c j) = (∑ i, g (c i)) + g (d j) := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), ← Finset.sum_erase_add _ (fun i => g (c i)) (Finset.mem_univ j)]
          have hh : (∑ i ∈ Finset.univ.erase j, g (d i)) = ∑ i ∈ Finset.univ.erase j, g (c i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hdi i (Finset.mem_erase.mp hi).1]
          rw [hh]
          omega
        have hsum := Finset.sum_erase_add s w ha
        have hdsum := sumchange id
        dsimp only [id_eq] at hdsum
        have ht' : (∑ b ∈ s.erase a, w b) = ∑ i, d i := by omega
        have hs' : (∑ i, if d i % 2 = 1 then 1 else 0) ≤ (∑ b ∈ s.erase a, if w b = 1 then 1 else 0) := by
          rcases hwa with h1 | h2 | h4
          · have hone : ∀ b ∈ s.erase a, w b = 1 := by
              intro b hb
              have := hmax b (Finset.mem_of_mem_erase hb)
              have := hw b
              omega
            have htone : (∑ b ∈ s.erase a, if w b = 1 then 1 else 0) = ∑ b ∈ s.erase a, w b := by
              apply Finset.sum_congr rfl
              intro b hb
              simp [hone b hb]
            rw [htone, ht']
            apply Finset.sum_le_sum
            intro i hi
            split_ifs <;> omega
          all_goals
            have hp : d j % 2 = c j % 2 := by omega
            have hsc := sumchange (fun x => if x % 2 = 1 then 1 else 0)
            have hsa := Finset.sum_erase_add s (fun b => if w b = 1 then 1 else 0) ha
            simp only [hp] at hsc
            have hne : w a ≠ 1 := by omega
            rw [if_neg hne, add_zero] at hsa
            omega
        have hf' : (∑ b ∈ s.erase a, if w b = 4 then 1 else 0) ≤ ∑ i, d i / 4 := by
          rcases hwa with h1 | h2 | h4
          · have hz : (∑ b ∈ s.erase a, if w b = 4 then 1 else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro b hb
              have := hmax b (Finset.mem_of_mem_erase hb)
              simp [show w b ≠ 4 by omega]
            omega
          · have hz : (∑ b ∈ s.erase a, if w b = 4 then 1 else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro b hb
              have := hmax b (Finset.mem_of_mem_erase hb)
              simp [show w b ≠ 4 by omega]
            omega
          · have hdc := sumchange (fun x => x / 4)
            have hfa := Finset.sum_erase_add s (fun b => if w b = 4 then 1 else 0) ha
            simp only [h4, if_true] at hfa
            have hddiv : d j / 4 + 1 = c j / 4 := by omega
            omega
        obtain ⟨f, hfi⟩ := ih (s.erase a) (Finset.erase_ssubset ha) d ht' hs' hf'
        refine ⟨Function.update f a j, ?_⟩
        intro i
        have heq : (∑ b ∈ s.erase a, if Function.update f a j b = i then w b else 0) = ∑ b ∈ s.erase a, if f b = i then w b else 0 := by
          apply Finset.sum_congr rfl
          intro b hb
          simp [Function.update_of_ne (Finset.mem_erase.mp hb).1]
        have hrec := hfi i
        have hadd := Finset.sum_erase_add s (fun b => if Function.update f a j b = i then w b else 0) ha
        rw [heq] at hadd
        simp only [Function.update_self] at hadd
        by_cases hij : i = j
        · subst i
          simp only [if_true] at hadd
          omega
        · rw [if_neg (Ne.symm hij)] at hadd
          rw [hdi i hij] at hrec
          omega
      · have hz : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
        subst s
        refine ⟨fun _ => ⟨0, hk⟩, ?_⟩
        intro i
        have hi := Finset.single_le_sum (f := c) (fun b hb => Nat.zero_le _) (Finset.mem_univ i)
        simp only [Finset.sum_empty] at ht ⊢
        omega
  obtain ⟨f, hf⟩ := pack Finset.univ c htotal (by simpa using hsingle) (by simpa using hfour)
  exact ⟨f, by intro i; simpa [Finset.sum_filter] using hf i⟩
