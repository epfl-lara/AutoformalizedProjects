import Mathlib

theorem LeanFlow.PB023.rowTwoSweep (C : ℕ) (hC : 3 ≤ C) :
    let onBoard : ℕ × ℕ → Prop := fun x =>
      0 < x.1 ∧ x.1 ≤ C + 1 ∧ 0 < x.2 ∧ x.2 ≤ C;
    let valid : List (ℕ × ℕ) → Prop := fun P =>
      P.head? = some (1, 1) ∧
      (∃ x : ℕ × ℕ, (x.1 = C + 1 ∧ onBoard x) ∧ P.getLast? = some x) ∧
      (∀ x : ℕ × ℕ, x ∈ P → onBoard x) ∧
      P.Chain' (fun a b => onBoard b ∧
        abs ((a.1 : ℤ) - (b.1 : ℤ)) + abs ((a.2 : ℤ) - (b.2 : ℤ)) = 1);
    let legal : Set (ℕ × ℕ) → Prop := fun S =>
      (∀ r c : ℕ, (r, c) ∈ S →
        (2 ≤ r ∧ r ≤ C) ∧ (1 ≤ c ∧ c ≤ C)) ∧
      (∀ r : ℕ, (2 ≤ r ∧ r ≤ C) → ∃! c : ℕ, (r, c) ∈ S) ∧
      (∀ r₁ c₁ r₂ c₂ : ℕ,
        (r₁, c₁) ∈ S → (r₂, c₂) ∈ S → c₁ = c₂ → r₁ = r₂);
    let first : (P : List (ℕ × ℕ)) → Set (ℕ × ℕ) → Fin P.length → Prop :=
      fun P S i => P.get i ∈ S ∧
        ∀ j : Fin P.length, j.val < i.val → P.get j ∉ S;
    ∃ P : List (ℕ × ℕ),
      valid P ∧
      ∀ S : Set (ℕ × ℕ), legal S →
        ∃ i : Fin P.length, first P S i ∧ (P.get i).1 = 2 := by classical
  intro onBoard valid legal first
  let f : ℕ → ℕ × ℕ := fun k => if k = 0 then (1,1) else if k ≤ C then (2,k) else (k-C+2,C)
  let P := List.ofFn (fun k : Fin (2*C) => f k)
  have hb (k : ℕ) (hk : k < 2*C) : onBoard (f k) := by
    dsimp [f, onBoard]
    split_ifs <;> simp only [Prod.fst, Prod.snd] <;> omega
  have hg (i : Fin P.length) : P.get i = f i.val := by simp [P, List.get_eq_getElem]
  have hl : P.length = 2*C := by simp [P]
  refine ⟨P, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [List.head?_eq_getElem?]
      simp [P, List.getElem?_eq_getElem, f, show 0 < 2*C by omega]
    · refine ⟨(C+1,C), ⟨rfl, by dsimp [onBoard]; omega⟩, ?_⟩
      rw [List.getLast?_eq_getElem?]
      have ht : 2*C-1 < 2*C := by omega
      have hn : 2*C-1 ≠ 0 := by omega
      have hnC : ¬ 2*C-1 ≤ C := by omega
      simp [P, List.getElem?_eq_getElem, ht, f, hn, hnC]
      omega
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
      rw [hg]
      exact hb i.val (by omega)
    · change P.IsChain _
      apply List.isChain_ofFn.mpr
      intro k hk
      refine ⟨hb (k+1) hk, ?_⟩
      dsimp [f]
      split_ifs <;> simp_all <;> try omega
      all_goals rw [abs_of_nonpos (by omega)] <;> omega
  · intro S hS
    obtain ⟨c, hc, hu⟩ := hS.2.1 2 (by omega)
    have hcB := hS.1 2 c hc
    let i : Fin P.length := ⟨c, by omega⟩
    have hi : P.get i = (2,c) := by rw [hg]; simp [i, f, show c ≠ 0 by omega, show c ≤ C by omega]
    refine ⟨i, ⟨hi ▸ hc, ?_⟩, by rw [hi]⟩
    intro j hj hm
    rw [hg] at hm
    by_cases hz : j.val = 0
    · have hm' : (1,1) ∈ S := by simpa [f, hz] using hm
      have := hS.1 1 1 hm'
      omega
    · have hjC : j.val ≤ C := by dsimp [i] at hj; omega
      have hm' : (2,j.val) ∈ S := by simpa [f, hz, hjC] using hm
      have := hu j.val hm'
      dsimp [i] at hj
      omega
