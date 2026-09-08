import Mathlib

theorem LeanFlowProofs.PBAdvanced027Aux.potential_connectivity
    {α : Type*} (V : Set α) (w : α → α → ℝ) (E : α → α → Prop)
    (hsep : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → (1 : ℝ) < w a b)
    (hsplit : ∀ a ∈ V, ∀ b ∈ V, a ≠ b → ¬ E a b →
      ∃ c ∈ V, c ≠ a ∧ c ≠ b ∧ w a c + w c b ≤ w a b) :
    ∀ a ∈ V, ∀ b ∈ V, Relation.ReflTransGen E a b := by 
  classical
  have bounded : ∀ n : ℕ, ∀ a ∈ V, ∀ b ∈ V,
      w a b ≤ (n : ℝ) → Relation.ReflTransGen E a b := by
    intro n
    induction n with
    | zero =>
      intro a ha b hb hw
      by_cases hab : a = b
      · subst b
        exact Relation.ReflTransGen.refl
      · have hs := hsep a ha b hb hab
        norm_num at hw
        linarith
    | succ n ih =>
      intro a ha b hb hw
      by_cases hab : a = b
      · subst b
        exact Relation.ReflTransGen.refl
      · by_cases he : E a b
        · exact Relation.ReflTransGen.single he
        · obtain ⟨c, hc, hca, hcb, hsum⟩ := hsplit a ha b hb hab he
          have hac := hsep a ha c hc (Ne.symm hca)
          have hbc := hsep c hc b hb hcb
          have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          rw [hcast] at hw
          exact (ih a ha c hc (by linarith)).trans (ih c hc b hb (by linarith))
  intro a ha b hb
  obtain ⟨n, hn⟩ := exists_nat_gt (w a b)
  exact bounded n a ha b hb (le_of_lt hn)
