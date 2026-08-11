import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

namespace IMO2026P1

/-- Whether it is valid to move from `p₁` to `p₂`. -/
def ValidMove (p₁ p₂ : Fin 2026 → ℕ) : Prop :=
  ∃ i j, i ≠ j ∧ 1 < p₁ i ∧ 1 < p₁ j ∧ (∀ k, k ≠ i → k ≠ j → p₂ k = p₁ k) ∧
    p₂ i = Nat.gcd (p₁ i) (p₁ j) ∧
      p₂ j = Nat.lcm (p₁ i) (p₁ j) / Nat.gcd (p₁ i) (p₁ j)

/-- Whether it is valid to move from `p₁` to `p₂`, or they are the same and there is no valid move
from that position. -/
def ValidOrNoMove (p₁ p₂ : Fin 2026 → ℕ) : Prop :=
  ValidMove p₁ p₂ ∨ p₁ = p₂ ∧ ¬∃ i j, i ≠ j ∧ 1 < p₁ i ∧ 1 < p₁ j

/-- Whether a sequence of positions if a valid one starting with a given position (known to be a
valid starting position), with the convention that the position is unchanged when there are no
valid moves. -/
def ValidSeq (p₀ : Fin 2026 → ℕ) (p : ℕ → Fin 2026 → ℕ) : Prop :=
  p 0 = p₀ ∧ ∀ i, ValidOrNoMove (p i) (p (i + 1))

theorem validOrNoMove_eq_of_not_exists
    {p₁ p₂ : Fin 2026 → ℕ}
    (h : ValidOrNoMove p₁ p₂)
    (hn : ¬ ∃ i j, i ≠ j ∧ 1 < p₁ i ∧ 1 < p₁ j) :
    p₁ = p₂ := by
  rcases h with hmove | hsame
  · exfalso
    apply hn
    rcases hmove with ⟨i, j, hij, hi, hj, hrest, hgi, hlj⟩
    exact ⟨i, j, hij, hi, hj⟩
  · exact hsame.1

theorem test_pair_product {a b : ℕ} :
    Nat.gcd a b * (Nat.lcm a b / Nat.gcd a b) = Nat.lcm a b := by
  exact Nat.mul_div_cancel' (dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b))

theorem test_prod_two {α : Type} [Fintype α] [DecidableEq α]
    {f g : α → ℕ} {i j : α} (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → g k = f k) :
    (Finset.univ.prod g) = (((Finset.univ.erase i).erase j).prod f) * g i * g j := by
  have hi : i ∈ (Finset.univ : Finset α) := Finset.mem_univ i
  have hj : j ∈ (Finset.univ.erase i : Finset α) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm hij
  rw [← Finset.prod_erase_mul (s := (Finset.univ : Finset α)) (f := g) hi]
  rw [← Finset.prod_erase_mul (s := (Finset.univ.erase i : Finset α)) (f := g) hj]
  have hprod : (((Finset.univ.erase i).erase j).prod g) =
      ((Finset.univ.erase i).erase j).prod f := by
    apply Finset.prod_congr rfl
    intro k hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    exact hrest k hk.2 hk.1
  rw [hprod]
  ac_rfl

theorem test_filter_eq_erase {α : Type} [Fintype α] [DecidableEq α]
    {f g : α → ℕ} {i j : α} (hij : i ≠ j)
    (hi : 1 < f i) (hj : 1 < f j) (gi : g i = 1) (gj : 1 < g j)
    (hrest : ∀ k, k ≠ i → k ≠ j → g k = f k) :
    (Finset.univ.filter (fun k => 1 < g k)) =
      (Finset.univ.filter (fun k => 1 < f k)).erase i := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [gi, hi]
  · by_cases hkj : k = j
    · subst k
      simp [hki, gj, hj]
    · simp [hki, hrest k hki hkj]

theorem test_card_bound {f : Fin 2026 → ℕ} :
    (Finset.univ.filter (fun k => 1 < f k)).card ≤ 2026 := by
  calc
    (Finset.univ.filter (fun k => 1 < f k)).card ≤ (Finset.univ : Finset (Fin 2026)).card :=
      Finset.card_filter_le (Finset.univ : Finset (Fin 2026)) (fun k => 1 < f k)
    _ = 2026 := by simp

theorem test_measure_eq {x y c d : ℕ} (hxy : x = y) (hcd : c < d) :
    x * 2027 + c < y * 2027 + d := by omega

theorem test_measure_lt {x y c d : ℕ} (hxy : x < y) (hc : c ≤ 2026) :
    x * 2027 + c < y * 2027 + d := by omega

theorem test_measure {f g : Fin 2026 → ℕ} (hpos : ∀ k, 0 < f k)
    (hmove : ValidMove f g) :
    (Finset.univ.prod g) * 2027 + (Finset.univ.filter (fun k => 1 < g k)).card <
      (Finset.univ.prod f) * 2027 + (Finset.univ.filter (fun k => 1 < f k)).card := by
  rcases hmove with ⟨i, j, hij, hi, hj, hrest, hgi, hgj⟩
  let d := Nat.gcd (f i) (f j)
  let l := Nat.lcm (f i) (f j)
  let R := (Finset.univ.erase i).erase j |>.prod f
  have hprod_g : Finset.univ.prod g = R * d * (l / d) := by
    calc
      Finset.univ.prod g = R * g i * g j := by
        simpa [R] using test_prod_two (f := f) (g := g) hij hrest
      _ = R * d * (l / d) := by rw [hgi, hgj]
  have hprod_f : Finset.univ.prod f = R * f i * f j := by
    simpa [R] using test_prod_two (f := f) (g := f) hij (by intros; rfl)
  have hRpos : 0 < R := by
    apply Finset.prod_pos
    intro k hk
    exact hpos k
  have hdp : 0 < d := by
    dsimp [d]
    exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (hpos i)
  have hlp : 0 < l := by
    dsimp [l]
    exact Nat.lcm_pos (hpos i) (hpos j)
  by_cases hd : d = 1
  · have hle : 1 < l := by
      dsimp [l]
      exact lt_of_lt_of_le hj (Nat.le_lcm_right (m := f i) (n := f j) (hpos i))
    have hgi' : g i = 1 := by simpa [d, hd] using hgi
    have hgj' : 1 < g j := by
      rw [hgj]
      change 1 < l / d
      rw [hd]
      simpa using hle
    have hset := test_filter_eq_erase hij hi hj hgi' hgj' hrest
    have hmem : i ∈ (Finset.univ.filter (fun k => 1 < f k)) := by simp [hi]
    have hcard : (Finset.univ.filter (fun k => 1 < g k)).card =
        (Finset.univ.filter (fun k => 1 < f k)).card - 1 := by
      rw [hset, Finset.card_erase_of_mem hmem]
    have hleq : l = f i * f j := by
      dsimp [d, l] at hd ⊢
      have heq := Nat.gcd_mul_lcm (f i) (f j)
      rw [hd] at heq
      simpa using heq
    have hquot : d * (l / d) = l := by
      calc
        d * (l / d) = 1 * (l / 1) := by rw [hd]
        _ = l := by simp
    have hprod_eq : Finset.univ.prod g = Finset.univ.prod f := by
      calc
        Finset.univ.prod g = R * d * (l / d) := hprod_g
        _ = R * (d * (l / d)) := Nat.mul_assoc _ _ _
        _ = R * l := congrArg (fun z => R * z) hquot
        _ = R * (f i * f j) := congrArg (fun z => R * z) hleq
        _ = Finset.univ.prod f :=
          (Nat.mul_assoc R (f i) (f j)).symm.trans hprod_f.symm
    have hcardlt : (Finset.univ.filter (fun k => 1 < g k)).card <
        (Finset.univ.filter (fun k => 1 < f k)).card := by
      rw [hcard]
      have hcardpos : 0 < (Finset.univ.filter (fun k => 1 < f k)).card :=
        Finset.card_pos.mpr ⟨i, by simp [hi]⟩
      omega
    exact test_measure_eq hprod_eq hcardlt
  · have hdgt : 1 < d := by omega
    have hpair : l < f i * f j := by
      have heq : d * l = f i * f j := by
        dsimp [d, l]
        exact Nat.gcd_mul_lcm _ _
      nlinarith
    have hquot : d * (l / d) = l := by
      dsimp [d, l]
      exact test_pair_product (a := f i) (b := f j)
    have hprod_lt : Finset.univ.prod g < Finset.univ.prod f := by
      calc
        Finset.univ.prod g = R * d * (l / d) := hprod_g
        _ = R * (d * (l / d)) := Nat.mul_assoc _ _ _
        _ = R * l := congrArg (fun z => R * z) hquot
        _ < R * (f i * f j) := Nat.mul_lt_mul_of_pos_left hpair hRpos
        _ = Finset.univ.prod f :=
          (Nat.mul_assoc R (f i) (f j)).symm.trans hprod_f.symm
    have hcardg := test_card_bound (f := g)
    exact test_measure_lt hprod_lt hcardg

theorem pair_factorization_gcd {a b q : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd (a.factorization q) (b.factorization q) =
      Nat.gcd ((Nat.gcd a b).factorization q)
        ((Nat.lcm a b / Nat.gcd a b).factorization q) := by
  have hdiv : Nat.gcd a b ∣ Nat.lcm a b :=
    dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
  have hg := congrArg (fun z : ℕ →₀ ℕ => z q)
    (Nat.factorization_gcd (Nat.ne_of_gt ha) (Nat.ne_of_gt hb))
  have hl := congrArg (fun z : ℕ →₀ ℕ => z q)
    (Nat.factorization_lcm (Nat.ne_of_gt ha) (Nat.ne_of_gt hb))
  have hd := congrArg (fun z : ℕ →₀ ℕ => z q) (Nat.factorization_div hdiv)
  rw [hg, hd]
  change Nat.gcd (a.factorization q) (b.factorization q) =
    Nat.gcd ((a.factorization ⊓ b.factorization) q)
      ((Nat.lcm a b).factorization q - (Nat.gcd a b).factorization q)
  rw [hl, hg]
  change Nat.gcd (a.factorization q) (b.factorization q) =
    Nat.gcd (min (a.factorization q) (b.factorization q))
      (max (a.factorization q) (b.factorization q) -
        min (a.factorization q) (b.factorization q))
  by_cases h : a.factorization q ≤ b.factorization q
  · rw [min_eq_left h, max_eq_right h]
    exact (Nat.gcd_sub_self_right h).symm
  · have h' : b.factorization q ≤ a.factorization q := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [min_eq_right h', max_eq_left h']
    rw [Nat.gcd_comm]
    rw [Nat.gcd_sub_self_right h']

theorem gcd_replace_pair {α : Type} [DecidableEq α] {s : Finset α}
    {f g : α → ℕ} {i j : α} (hi : i ∈ s) (hj : j ∈ s) (_hij : i ≠ j)
    (hrest : ∀ k, k ∈ s → k ≠ i → k ≠ j → g k = f k)
    (hpair : Nat.gcd (f i) (f j) = Nat.gcd (g i) (g j)) :
    s.gcd f = s.gcd g := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd
    intro k hk
    by_cases hki : k = i
    · subst k
      have hfi : s.gcd f ∣ f i := Finset.gcd_dvd hi
      have hfj : s.gcd f ∣ f j := Finset.gcd_dvd hj
      have hpair' : s.gcd f ∣ Nat.gcd (g i) (g j) := by
        rw [← hpair]
        exact Nat.dvd_gcd hfi hfj
      exact dvd_trans hpair' (Nat.gcd_dvd_left _ _)
    · by_cases hkj : k = j
      · subst k
        have hfi : s.gcd f ∣ f i := Finset.gcd_dvd hi
        have hfj : s.gcd f ∣ f j := Finset.gcd_dvd hj
        have hpair' : s.gcd f ∣ Nat.gcd (g i) (g j) := by
          rw [← hpair]
          exact Nat.dvd_gcd hfi hfj
        exact dvd_trans hpair' (Nat.gcd_dvd_right _ _)
      · rw [hrest k hk hki hkj]
        exact Finset.gcd_dvd hk
  · apply Finset.dvd_gcd
    intro k hk
    by_cases hki : k = i
    · subst k
      have hgi : s.gcd g ∣ g i := Finset.gcd_dvd hi
      have hgj : s.gcd g ∣ g j := Finset.gcd_dvd hj
      have hpair' : s.gcd g ∣ Nat.gcd (f i) (f j) := by
        rw [hpair]
        exact Nat.dvd_gcd hgi hgj
      exact dvd_trans hpair' (Nat.gcd_dvd_left _ _)
    · by_cases hkj : k = j
      · subst k
        have hgi : s.gcd g ∣ g i := Finset.gcd_dvd hi
        have hgj : s.gcd g ∣ g j := Finset.gcd_dvd hj
        have hpair' : s.gcd g ∣ Nat.gcd (f i) (f j) := by
          rw [hpair]
          exact Nat.dvd_gcd hgi hgj
        exact dvd_trans hpair' (Nat.gcd_dvd_right _ _)
      · rw [← hrest k hk hki hkj]
        exact Finset.gcd_dvd hk

theorem validseq_terminal {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    {p : ℕ → Fin 2026 → ℕ} (hp : ValidSeq p₀ p) :
    ∃ j, ¬ ∃ i k, i ≠ k ∧ 1 < p j i ∧ 1 < p j k := by
  have hpos : ∀ n k, 0 < p n k := by
    intro n
    induction n with
    | zero =>
        intro k
        rw [hp.1]
        have hk := h0 k
        omega
    | succ n ih =>
        intro k
        rcases hp.2 n with hm | hs
        · rcases hm with ⟨i, j, hij, hi, hj, hrest, hgi, hgj⟩
          by_cases hki : k = i
          · subst k
            rw [hgi]
            exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (ih i)
          · by_cases hkj : k = j
            · subst k
              rw [hgj]
              apply Nat.div_pos
              · exact Nat.le_of_dvd (Nat.lcm_pos (ih i) (ih j))
                  (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _))
              · exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (ih i)
            · rw [hrest k hki hkj]
              exact ih k
        · rw [← hs.1]
          exact ih k
  have hdesc : ∀ (m : ℕ → ℕ), (∀ n, m (n + 1) < m n) → False := by
    intro m hm
    have hb : ∀ n, m n + n ≤ m 0 := by
      intro n
      induction n with
      | zero => omega
      | succ n ih =>
          have hs := hm n
          omega
    have hh := hb (m 0 + 1)
    omega
  by_contra h
  have hpair : ∀ n, ∃ i k, i ≠ k ∧ 1 < p n i ∧ 1 < p n k := by
    intro n
    by_contra hn
    apply h
    exact ⟨n, hn⟩
  have hmove : ∀ n, ValidMove (p n) (p (n + 1)) := by
    intro n
    rcases hp.2 n with hm | hs
    · exact hm
    · exfalso
      exact hs.2 (hpair n)
  let μ : (Fin 2026 → ℕ) → ℕ := fun f =>
    (Finset.univ.prod f) * 2027 + (Finset.univ.filter (fun k => 1 < f k)).card
  apply hdesc (fun n => μ (p n))
  intro n
  exact test_measure (hpos n) (hmove n)

theorem validseq_pos {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    {p : ℕ → Fin 2026 → ℕ} (hp : ValidSeq p₀ p) :
    ∀ n k, 0 < p n k := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [hp.1]
      have hk := h0 k
      omega
  | succ n ih =>
      intro k
      rcases hp.2 n with hm | hs
      · rcases hm with ⟨i, j, hij, hi, hj, hrest, hgi, hgj⟩
        by_cases hki : k = i
        · subst k
          rw [hgi]
          exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (ih i)
        · by_cases hkj : k = j
          · subst k
            rw [hgj]
            apply Nat.div_pos
            · exact Nat.le_of_dvd (Nat.lcm_pos (ih i) (ih j))
                (dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _))
            · exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) (ih i)
          · rw [hrest k hki hkj]
            exact ih k
      · rw [← hs.1]
        exact ih k

theorem validseq_exists_gt_one {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    {p : ℕ → Fin 2026 → ℕ} (hp : ValidSeq p₀ p) :
    ∀ n, ∃ k, 1 < p n k := by
  intro n
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      rw [hp.1]
      exact h0 0
  | succ n ih =>
      rcases hp.2 n with hm | hs
      · rcases hm with ⟨i, j, hij, hi, hj, hrest, hgi, hgj⟩
        by_cases hni : 1 < p (n + 1) i
        · exact ⟨i, hni⟩
        · by_cases hnj : 1 < p (n + 1) j
          · exact ⟨j, hnj⟩
          · have hpi : 0 < p (n + 1) i := validseq_pos h0 hp (n + 1) i
            have hpj : 0 < p (n + 1) j := validseq_pos h0 hp (n + 1) j
            have heqi : p (n + 1) i = 1 := by omega
            have heqj : p (n + 1) j = 1 := by omega
            have hgcd : Nat.gcd (p n i) (p n j) = 1 := by
              rw [← hgi, heqi]
            have hquot : Nat.lcm (p n i) (p n j) / Nat.gcd (p n i) (p n j) = 1 := by
              rw [← hgj, heqj]
            rw [hgcd] at hquot
            have hlcm : Nat.lcm (p n i) (p n j) = 1 := by
              simpa using hquot
            have hlcmpos : 0 < Nat.lcm (p n i) (p n j) :=
              Nat.lcm_pos (validseq_pos h0 hp n i) (validseq_pos h0 hp n j)
            have hle : p n i ≤ Nat.lcm (p n i) (p n j) :=
              Nat.le_of_dvd hlcmpos (Nat.dvd_lcm_left _ _)
            rw [hlcm] at hle
            omega
      · rw [← hs.1]
        exact ih

theorem validmove_factorization_gcd {f g : Fin 2026 → ℕ}
    (hpos : ∀ k, 0 < f k) (hm : ValidMove f g) (q : ℕ) :
    (Finset.univ : Finset (Fin 2026)).gcd (fun k => (f k).factorization q) =
      (Finset.univ : Finset (Fin 2026)).gcd (fun k => (g k).factorization q) := by
  rcases hm with ⟨i, j, hij, hi, hj, hrest, hgi, hgj⟩
  apply gcd_replace_pair (s := (Finset.univ : Finset (Fin 2026)))
    (f := fun k => (f k).factorization q) (g := fun k => (g k).factorization q)
    (Finset.mem_univ i) (Finset.mem_univ j) hij
  · intro k hk hki hkj
    rw [hrest k hki hkj]
  · simpa [hgi, hgj] using
      (pair_factorization_gcd (a := f i) (b := f j) (q := q) (hpos i) (hpos j))

theorem validseq_factorization_gcd {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    {p : ℕ → Fin 2026 → ℕ} (hp : ValidSeq p₀ p) (n q : ℕ) :
    (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p 0 k).factorization q) =
      (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p n k).factorization q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p 0 k).factorization q) =
            (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p n k).factorization q) := ih
        _ = (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p (n + 1) k).factorization q) := by
          rcases hp.2 n with hm | hs
          · exact validmove_factorization_gcd (fun k => validseq_pos h0 hp n k) hm q
          · rw [← hs.1]

theorem factorization_prime_power_product_apply {S : Finset ℕ}
    (hS : ∀ r ∈ S, Nat.Prime r) (e : ℕ → ℕ) (q : ℕ) :
    ((S.prod (fun r => r ^ e r)).factorization q) = if q ∈ S then e q else 0 := by
  classical
  rw [Nat.factorization_prod_apply]
  · by_cases hq : q ∈ S
    · rw [if_pos hq]
      rw [Finset.sum_eq_single q]
      · rw [Nat.factorization_pow, (hS q hq).factorization]
        simp
      · intro b hb hbq
        rw [Nat.factorization_pow, (hS b hb).factorization]
        simp [hbq]
      · intro hq'
        exact (hq' hq).elim
    · rw [if_neg hq]
      apply Finset.sum_eq_zero
      intro r hr
      rw [Nat.factorization_pow, (hS r hr).factorization]
      have hrq : r ≠ q := by
        intro heq
        apply hq
        rw [← heq]
        exact hr
      simp [hrq]
  · intro r hr
    exact pow_ne_zero _ (Nat.ne_of_gt (hS r hr).pos)

theorem canonical_factorization_gcd {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    ∃ M : ℕ, ∀ q : ℕ,
      M.factorization q =
        (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p₀ k).factorization q) := by
  let A : ℕ := (Finset.univ : Finset (Fin 2026)).prod p₀
  let S : Finset ℕ := A.primeFactors
  let e : ℕ → ℕ := fun q =>
    (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p₀ k).factorization q)
  let M : ℕ := S.prod (fun r => r ^ e r)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact (Finset.prod_ne_zero_iff).2 (by
      intro k hk
      exact Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 k)))
  have hS : ∀ r ∈ S, Nat.Prime r := by
    intro r hr
    exact (Nat.mem_primeFactors.mp hr).1
  refine ⟨M, ?_⟩
  intro q
  have hfac := factorization_prime_power_product_apply hS e q
  dsimp [M]
  rw [hfac]
  by_cases hq : q ∈ S
  · simp [hq, e]
  · rw [if_neg hq]
    have hGzero :
        (Finset.univ : Finset (Fin 2026)).gcd
            (fun k => (p₀ k).factorization q) = 0 := by
      apply (Finset.gcd_eq_zero_iff).2
      intro k hk
      rw [Nat.factorization_eq_zero_iff]
      by_cases hpq : Nat.Prime q
      · right
        left
        intro hdiv
        apply hq
        apply (Nat.mem_primeFactors).2
        refine ⟨hpq, ?_, hA⟩
        exact dvd_trans hdiv (by
          dsimp [A]
          exact Finset.dvd_prod_of_mem p₀ hk)
      · exact Or.inl hpq
    exact hGzero.symm

theorem factorization_eq_of_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : ∀ q, a.factorization q = b.factorization q) : a = b := by
  apply Nat.eq_of_factorization_eq (a := a) (b := b)
  · exact Nat.ne_of_gt ha
  · exact Nat.ne_of_gt hb
  · intro q
    exact h q

theorem canonical_factorization_gcd_pos {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    ∃ M : ℕ, 0 < M ∧ ∀ q : ℕ,
      M.factorization q =
        (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p₀ k).factorization q) := by
  let A : ℕ := (Finset.univ : Finset (Fin 2026)).prod p₀
  let S : Finset ℕ := A.primeFactors
  let e : ℕ → ℕ := fun q =>
    (Finset.univ : Finset (Fin 2026)).gcd (fun k => (p₀ k).factorization q)
  let M : ℕ := S.prod (fun r => r ^ e r)
  have hA : A ≠ 0 := by
    dsimp [A]
    exact (Finset.prod_ne_zero_iff).2 (by
      intro k hk
      exact Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one (h0 k)))
  have hS : ∀ r ∈ S, Nat.Prime r := by
    intro r hr
    exact (Nat.mem_primeFactors.mp hr).1
  have hMpos : 0 < M := by
    dsimp [M]
    exact Finset.prod_pos (by
      intro r hr
      exact pow_pos (hS r hr).pos _)
  refine ⟨M, hMpos, ?_⟩
  intro q
  have hfac := factorization_prime_power_product_apply hS e q
  dsimp [M]
  rw [hfac]
  by_cases hq : q ∈ S
  · simp [hq, e]
  · rw [if_neg hq]
    have hGzero :
        (Finset.univ : Finset (Fin 2026)).gcd
            (fun k => (p₀ k).factorization q) = 0 := by
      apply (Finset.gcd_eq_zero_iff).2
      intro k hk
      rw [Nat.factorization_eq_zero_iff]
      by_cases hpq : Nat.Prime q
      · right
        left
        intro hdiv
        apply hq
        apply (Nat.mem_primeFactors).2
        refine ⟨hpq, ?_, hA⟩
        exact dvd_trans hdiv (by
          dsimp [A]
          exact Finset.dvd_prod_of_mem p₀ hk)
      · exact Or.inl hpq
    exact hGzero.symm

set_option maxRecDepth 100000
theorem result {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    (∀ p, ValidSeq p₀ p → ∃ j, ∃! k, 1 < p j k) ∧
      ∃ M, ∀ p, ValidSeq p₀ p → ∀ j, (∃! k, 1 < p j k) → ∀ k, 1 < p j k → p j k = M := by
  constructor
  · intro p hp
    rcases validseq_terminal h0 hp with ⟨j, hj⟩
    rcases validseq_exists_gt_one h0 hp j with ⟨k, hk⟩
    refine ⟨j, k, hk, ?_⟩
    intro l hl
    by_contra hne
    apply hj
    refine ⟨k, l, ?_, hk, hl⟩
    intro hkl
    apply hne
    exact hkl.symm
  · rcases canonical_factorization_gcd_pos h0 with ⟨M, hMpos, hMfac⟩
    refine ⟨M, ?_⟩
    intro p hp j hjuniq k hk
    rcases hjuniq with ⟨i, hi, huniq⟩
    have hpos : ∀ l, 0 < p j l := validseq_pos h0 hp j
    have hki : k = i := huniq k hk
    subst k
    apply factorization_eq_of_pos (hpos i) hMpos
    intro q
    have hrow :
        (Finset.univ : Finset (Fin 2026)).gcd
            (fun l => (p j l).factorization q) = (p j i).factorization q := by
      apply Nat.dvd_antisymm
      · exact Finset.gcd_dvd (Finset.mem_univ i)
      · apply Finset.dvd_gcd
        intro l hl
        by_cases hli : l = i
        · subst l
          exact dvd_refl _
        · have hnot : ¬ 1 < p j l := by
            intro hlt
            exact hli (huniq l hlt)
          have hone : p j l = 1 := by
            have hpl := hpos l
            omega
          rw [hone]
          simp
    calc
      (p j i).factorization q =
          (Finset.univ : Finset (Fin 2026)).gcd
            (fun l => (p j l).factorization q) := hrow.symm
      _ = (Finset.univ : Finset (Fin 2026)).gcd
            (fun l => (p 0 l).factorization q) :=
        (validseq_factorization_gcd h0 hp j q).symm
      _ = (Finset.univ : Finset (Fin 2026)).gcd
            (fun l => (p₀ l).factorization q) := by rw [hp.1]
      _ = M.factorization q := (hMfac q).symm

end IMO2026P1
