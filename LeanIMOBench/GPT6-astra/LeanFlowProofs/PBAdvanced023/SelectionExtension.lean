import Mathlib

theorem LeanFlow.PB023.selectionExtension (C : ℕ) (hC : 3 ≤ C) :
    let legal : Set (ℕ × ℕ) → Prop := fun S =>
      (∀ r c : ℕ, (r, c) ∈ S →
        (2 ≤ r ∧ r ≤ C) ∧ (1 ≤ c ∧ c ≤ C)) ∧
      (∀ r : ℕ, (2 ≤ r ∧ r ≤ C) → ∃! c : ℕ, (r, c) ∈ S) ∧
      (∀ r₁ c₁ r₂ c₂ : ℕ,
        (r₁, c₁) ∈ S → (r₂, c₂) ∈ S → c₁ = c₂ → r₁ = r₂);
    ∀ c d : ℕ,
      1 ≤ c → c ≤ C → 1 ≤ d → d ≤ C → c ≠ d →
      ∃ S : Set (ℕ × ℕ), legal S ∧ (2, c) ∈ S ∧ (3, d) ∈ S := by 
  classical
  dsimp only
  intro c d hc hcC hd hdC hcd
  have bound : ∀ a b x : ℕ, (1 ≤ a ∧ a ≤ C) → (1 ≤ b ∧ b ≤ C) →
      (1 ≤ x ∧ x ≤ C) → (1 ≤ Equiv.swap a b x ∧ Equiv.swap a b x ≤ C) := by
    intro a b x ha hb hx
    simp only [Equiv.swap_apply_def]
    split_ifs <;> assumption
  let σ : Equiv.Perm ℕ := Equiv.swap 1 c
  have hs1 : σ 1 = c := by simp [σ]
  have hs2 : σ 2 ≠ c := by
    intro he
    have := σ.injective (he.trans hs1.symm)
    norm_num at this
  let π : Equiv.Perm ℕ := σ.trans (Equiv.swap (σ 2) d)
  have hp1 : π 1 = c := by
    change Equiv.swap (σ 2) d (σ 1) = c
    rw [hs1, Equiv.swap_apply_def]
    simp [Ne.symm hs2, hcd]
  have hp2 : π 2 = d := by
    change Equiv.swap (σ 2) d (σ 2) = d
    simp
  have hpbound : ∀ x : ℕ, (1 ≤ x ∧ x ≤ C) → (1 ≤ π x ∧ π x ≤ C) := by
    intro x hx
    apply bound (σ 2) d (σ x)
    · exact bound 1 c 2 ⟨by omega, by omega⟩ ⟨hc, hcC⟩ ⟨by omega, by omega⟩
    · exact ⟨hd, hdC⟩
    · exact bound 1 c x ⟨by omega, by omega⟩ ⟨hc, hcC⟩ hx
  let S : Set (ℕ × ℕ) := {p | (2 ≤ p.1 ∧ p.1 ≤ C) ∧ p.2 = π (p.1 - 1)}
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r k hk
    change (2 ≤ r ∧ r ≤ C) ∧ k = π (r - 1) at hk
    refine ⟨hk.1, ?_⟩
    rw [hk.2]
    exact hpbound (r - 1) ⟨by omega, by omega⟩
  · intro r hr
    refine ⟨π (r - 1), ⟨hr, rfl⟩, ?_⟩
    intro y hy
    exact hy.2
  · intro r₁ c₁ r₂ c₂ h1 h2 he
    change (2 ≤ r₁ ∧ r₁ ≤ C) ∧ c₁ = π (r₁ - 1) at h1
    change (2 ≤ r₂ ∧ r₂ ≤ C) ∧ c₂ = π (r₂ - 1) at h2
    have hh := π.injective (h1.2.symm.trans (he.trans h2.2))
    omega
  · change (2 ≤ 2 ∧ 2 ≤ C) ∧ c = π (2 - 1)
    exact ⟨⟨by omega, by omega⟩, hp1.symm⟩
  · change (2 ≤ 3 ∧ 3 ≤ C) ∧ d = π (3 - 1)
    exact ⟨⟨by omega, hC⟩, hp2.symm⟩
