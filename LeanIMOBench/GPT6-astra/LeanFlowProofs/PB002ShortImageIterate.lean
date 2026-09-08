import Mathlib

theorem LeanFlowPB002.short_image_iterate {V : Type*} [Fintype V] (R : V → V → Prop) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  ∀ (k : ℕ) (x y : V), y ∈ F^[k] ({x} : Set V) →
    ∃ h : ℕ, h < Fintype.card V ∧ y ∈ F^[h] ({x} : Set V) := by 
  classical
  intro F k x y hy
  let P : ℕ → V → Prop := fun n z => z ∈ F^[n] ({x} : Set V)
  have step (n : ℕ) (z : V) : P (n+1) z ↔ ∃ w, P n w ∧ R w z := by
    change z ∈ F^[n+1] ({x} : Set V) ↔ _
    rw [Function.iterate_succ_apply']
    rfl
  have levels : ∀ n z, P n z → (∀ j < n, ¬ P j z) →
      ∀ i ≤ n, ∃ w, P i w ∧ ∀ j < i, ¬ P j w := by
    intro n
    induction n with
    | zero =>
      intro z hz hmin i hi
      have : i = 0 := by omega
      subst i
      exact ⟨z, hz, hmin⟩
    | succ n ih =>
      intro z hz hmin i hi
      by_cases heq : i = n+1
      · subst i
        exact ⟨z, hz, hmin⟩
      · obtain ⟨w, hw, hwz⟩ := (step n z).mp hz
        have hwmin : ∀ j < n, ¬ P j w := by
          intro j hj hp
          exact hmin (j+1) (by omega) ((step j z).mpr ⟨w, hp, hwz⟩)
        exact ih w hw hwmin i (by omega)
  have hex : ∃ n, P n y := ⟨k, hy⟩
  let h := Nat.find hex
  have hh : P h y := Nat.find_spec hex
  have hmin : ∀ j < h, ¬ P j y := by
    intro j hj
    exact Nat.find_min hex hj
  have hl (i : Fin (h+1)) : ∃ w, P i.val w ∧ ∀ j < i.val, ¬ P j w :=
    levels h y hh hmin i.val (by omega)
  choose f hf using hl
  have hinj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hf b).2 a.val hlt (hab ▸ (hf a).1)
    · exact (hf a).2 b.val hgt (hab.symm ▸ (hf b).1)
  have hc := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hc
  exact ⟨h, by omega, hh⟩

