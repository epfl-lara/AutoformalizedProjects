import Mathlib

theorem LeanFlowProofs.PB018.grid_cover (n : ℕ) (hn : 2 ≤ n) {β : Type*} [DecidableEq β] (p : Fin n × Fin n → β) (hsquare : ∀ y₀ y₁ x₀ x₁ : Fin n, y₁.val = y₀.val + 1 → x₁.val = x₀.val + 1 → ({p (y₀, x₀), p (y₀, x₁), p (y₁, x₀), p (y₁, x₁)} : Finset β).card ≤ 2) : (∃ a b : Fin n × Fin n, p a = p b ∧ a.1.val = 0 ∧ b.1.val + 1 = n) ∨ (∃ a b : Fin n × Fin n, p a = p b ∧ a.2.val = 0 ∧ b.2.val + 1 = n) := by set_option maxHeartbeats 2000000 in
  { classical
  by_contra h
  push_neg at h
  obtain ⟨hvert, hhor⟩ := h
  let B : β → Prop := fun b => ∃ a, p a = b ∧ a.1.val = 0
  let L : β → Prop := fun b => ∃ a, p a = b ∧ a.2.val = 0
  let R : β → Prop := fun b => ∃ a, p a = b ∧ a.2.val + 1 = n
  let c : β → ℕ := fun b => if B b then (if L b then 0 else 1) else (if R b then 2 else 0)
  have noLR : ∀ b, L b → R b → False := by
    rintro b ⟨a, ha, hal⟩ ⟨d, hd, hdr⟩
    exact hhor a d (ha.trans hd.symm) hal hdr
  have noBT : ∀ a, a.1.val + 1 = n → ¬ B (p a) := by
    rintro a hat ⟨d, hd, hdb⟩
    exact hvert d a hd hdb hat
  have cb : ∀ a, a.1.val = 0 → c (p a) = 0 ∨ c (p a) = 1 := by
    intro a ha
    have hb : B (p a) := ⟨a, rfl, ha⟩
    simp only [c, if_pos hb]
    split_ifs <;> simp
  have cl : ∀ a, a.2.val = 0 → c (p a) = 0 := by
    intro a ha
    have hl : L (p a) := ⟨a, rfl, ha⟩
    have hr : ¬ R (p a) := noLR _ hl
    simp [c, hl, hr]
  have cr : ∀ a, a.2.val + 1 = n → c (p a) ≠ 0 := by
    intro a ha
    have hr : R (p a) := ⟨a, rfl, ha⟩
    have hl : ¬ L (p a) := fun hl => noLR _ hl hr
    simp only [c, if_neg hl, if_pos hr]
    split_ifs <;> simp
  have ct : ∀ a, a.1.val + 1 = n → c (p a) ≠ 1 := by
    intro a ha
    simp only [c, if_neg (noBT a ha)]
    split_ifs <;> simp
  let U : β → ℤ := fun b => if c b = 0 then 1 else 0
  let V : β → ℤ := fun b => if c b = 1 then 1 else 0
  let E : β → β → ℤ := fun a b => U a * V b - V a * U b
  have triple : ∀ (s : Finset β), s.card ≤ 2 → ∀ a ∈ s, ∀ b ∈ s, ∀ d ∈ s,
      E a b + E b d = E a d := by
    intro s hs a ha b hb d hd
    have heq : a = b ∨ b = d ∨ a = d := by
      by_contra hh
      push_neg at hh
      have hsub : ({a,b,d} : Finset β) ⊆ s := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      have hc := Finset.card_le_card hsub
      have hhcard : ({a,b,d} : Finset β).card = 3 := by simp [hh.1, hh.2.1, hh.2.2]
      omega
    rcases heq with rfl | rfl | rfl <;> dsimp [E] <;> ring
  let ix : ℕ → Fin n := fun i => ⟨min i (n-1), by omega⟩
  have ixval : ∀ i, i < n → (ix i).val = i := by
    intro i hi
    dsimp [ix]
    omega
  let q : ℕ → ℕ → β := fun y x => p (ix y, ix x)
  have curl : ∀ y x, y + 1 < n → x + 1 < n →
      E (q y x) (q y (x+1)) + E (q y (x+1)) (q (y+1) (x+1)) =
      E (q y x) (q (y+1) x) + E (q (y+1) x) (q (y+1) (x+1)) := by
    intro y x hy hx
    have hs := hsquare (ix y) (ix (y+1)) (ix x) (ix (x+1))
      (by rw [ixval _ hy, ixval _ (by omega)])
      (by rw [ixval _ hx, ixval _ (by omega)])
    have ht := triple _ hs
    have h1 := ht (q y x) (by simp [q]) (q y (x+1)) (by simp [q]) (q (y+1) (x+1)) (by simp [q])
    have h2 := ht (q y x) (by simp [q]) (q (y+1) x) (by simp [q]) (q (y+1) (x+1)) (by simp [q])
    exact h1.trans h2.symm
  have iz : (ix 0).val = 0 := ixval 0 (by omega)
  have il : (ix (n-1)).val + 1 = n := by rw [ixval _ (by omega)]; omega
  have leftE : ∀ y, E (q y 0) (q (y+1) 0) = 0 := by
    intro y
    have h1 := cl (ix y, ix 0) iz
    have h2 := cl (ix (y+1), ix 0) iz
    simp [E, U, V, q, h1, h2]
  have rightE : ∀ y, E (q y (n-1)) (q (y+1) (n-1)) = 0 := by
    intro y
    have h1 := cr (ix y, ix (n-1)) il
    have h2 := cr (ix (y+1), ix (n-1)) il
    simp [E, U, V, q, h1, h2]
  have topE : ∀ x, E (q (n-1) x) (q (n-1) (x+1)) = 0 := by
    intro x
    have h1 := ct (ix (n-1), ix x) il
    have h2 := ct (ix (n-1), ix (x+1)) il
    simp [E, U, V, q, h1, h2]
  have bottomE : ∀ x, E (q 0 x) (q 0 (x+1)) = V (q 0 (x+1)) - V (q 0 x) := by
    intro x
    have h1 := cb (ix 0, ix x) iz
    have h2 := cb (ix 0, ix (x+1)) iz
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      simp [E, U, V, q, h1, h2]
  let S : ℕ → ℤ := fun y => ∑ x ∈ Finset.range (n-1), E (q y x) (q y (x+1))
  have row : ∀ y, y+1 < n → S y = S (y+1) := by
    intro y hy
    have eqs : ∀ x ∈ Finset.range (n-1),
        E (q y x) (q y (x+1)) - E (q (y+1) x) (q (y+1) (x+1)) =
        E (q y x) (q (y+1) x) - E (q y (x+1)) (q (y+1) (x+1)) := by
      intro x hx
      have hh := curl y x hy (by simp only [Finset.mem_range] at hx; omega)
      omega
    have hh := Finset.sum_congr rfl eqs
    rw [Finset.sum_sub_distrib] at hh
    have tel : (∑ x ∈ Finset.range (n-1),
        (E (q y x) (q (y+1) x) - E (q y (x+1)) (q (y+1) (x+1)))) =
        E (q y 0) (q (y+1) 0) - E (q y (n-1)) (q (y+1) (n-1)) := by
      exact Finset.sum_range_sub' _ _
    rw [tel, leftE, rightE] at hh
    dsimp [S]
    omega
  have invariant : ∀ y, y < n → S y = S 0 := by
    intro y
    induction y with
    | zero => intro _; rfl
    | succ y ih =>
      intro hy
      exact (row y hy).symm.trans (ih (by omega))
  have stop : S (n-1) = 0 := by
    dsimp [S]
    simp only [topE, Finset.sum_const_zero]
  have sbottom : S 0 = 1 := by
    have hh : S 0 = V (q 0 (n-1)) - V (q 0 0) := by
      dsimp [S]
      simp_rw [bottomE]
      exact Finset.sum_range_sub (fun x => V (q 0 x)) (n-1)
    have h0 := cl (ix 0, ix 0) iz
    have h1 := cb (ix 0, ix (n-1)) iz
    have hne := cr (ix 0, ix (n-1)) il
    have hlast : c (q 0 (n-1)) = 1 := h1.resolve_left hne
    rw [hh]
    simp [V, q] at hlast ⊢
    simp [hlast, h0]
  have hh := invariant (n-1) (by omega)
  omega }

