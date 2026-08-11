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

private theorem existsUnique_of_nonempty_and_no_pair {p : Fin 2026 → ℕ}
    (hex : ∃ k, 1 < p k)
    (hpair : ¬ ∃ i j, i ≠ j ∧ 1 < p i ∧ 1 < p j) :
    ∃! k, 1 < p k := by
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, hk, ?_⟩
  intro y hy
  by_contra hne
  exact hpair ⟨k, y, (fun h => hne h.symm), hk, hy⟩

theorem no_unique_index_at_zero {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    (p : ℕ → Fin 2026 → ℕ) (hp : ValidSeq p₀ p) :
    ¬ ∃! k, 1 < p 0 k := by
  intro h
  rcases h with ⟨k, hk, huniq⟩
  have hp0 : p 0 = p₀ := hp.1
  let a : Fin 2026 := ⟨0, by omega⟩
  let b : Fin 2026 := ⟨1, by omega⟩
  have ha : 1 < p 0 a := by
    rw [hp0]
    exact h0 a
  have hb : 1 < p 0 b := by
    rw [hp0]
    exact h0 b
  have eab : a = b := (huniq a ha).trans (huniq b hb).symm
  have hab : a ≠ b := by
    simp [a, b]
  exact hab eab

theorem unique_witness_time_pos {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    (p : ℕ → Fin 2026 → ℕ) (hp : ValidSeq p₀ p) (j : ℕ)
    (hj : ∃! k, 1 < p j k) : 0 < j := by
  by_contra hn
  have hj0 : j = 0 := by omega
  subst j
  rcases hj with ⟨k, hk, huniq⟩
  have hp0 : p 0 = p₀ := hp.1
  let a : Fin 2026 := ⟨0, by omega⟩
  let b : Fin 2026 := ⟨1, by omega⟩
  have ha : 1 < p 0 a := by
    rw [hp0]
    exact h0 a
  have hb : 1 < p 0 b := by
    rw [hp0]
    exact h0 b
  have eab : a = b := (huniq a ha).trans (huniq b hb).symm
  have hab : a ≠ b := by
    simp [a, b]
  exact hab eab

private theorem exists_terminal_of_decreases_until
    (rank : ℕ → ℕ) (terminal : ℕ → Prop)
    (hstep : ∀ n, terminal n ∨ rank (n + 1) < rank n) :
    ∃ n, terminal n := by
  by_contra hnone
  push Not at hnone
  have hbound : ∀ n, rank n + n ≤ rank 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hlt : rank (n + 1) < rank n :=
          (hstep n).resolve_left (hnone n)
        omega
  have := hbound (rank 0 + 1)
  omega

private theorem prod_factor_of_validMove {p₁ p₂ : Fin 2026 → ℕ}
    (h : ValidMove p₁ p₂) :
    ∃ g, 0 < g ∧ (∏ k, p₁ k) = g * ∏ k, p₂ k := by
  set_option maxRecDepth 10000 in
  rcases h with ⟨i, j, hij, hi, hj, hrest, hpi, hpj⟩
  let g := Nat.gcd (p₁ i) (p₁ j)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  refine ⟨g, hg, ?_⟩
  have hp₂ : p₂ = Function.update (Function.update p₁ i g) j
      (Nat.lcm (p₁ i) (p₁ j) / g) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [Function.update, hij, hpi, g]
    by_cases hkj : k = j
    · subst k
      simp [Function.update, hpj, g]
    · simp [Function.update, hki, hkj, hrest k hki hkj]
  rw [hp₂]
  rw [Finset.prod_update_of_mem (by simp : j ∈ (Finset.univ : Finset (Fin 2026)))]
  have himem : i ∈ (Finset.univ : Finset (Fin 2026)) \ {j} := by simp [hij]
  rw [Finset.prod_update_of_mem himem]
  have himemErase : i ∈ (Finset.univ : Finset (Fin 2026)).erase j := by simp [hij]
  have hold : (∏ k, p₁ k) =
      p₁ j * (p₁ i * ∏ x ∈ (Finset.univ.erase j).erase i, p₁ x) := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) (f := p₁) (Finset.mem_univ j)]
    rw [← Finset.mul_prod_erase (s := Finset.univ.erase j) (f := p₁) himemErase]
  rw [hold]
  dsimp [g]
  have hd : Nat.gcd (p₁ i) (p₁ j) ∣ Nat.lcm (p₁ i) (p₁ j) :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _)
  conv_rhs => rw [← Nat.mul_assoc, Nat.mul_div_cancel' hd]
  calc
    p₁ j * (p₁ i * ∏ x ∈ (Finset.univ.erase j).erase i, p₁ x) =
        (p₁ i * p₁ j) * ∏ x ∈ (Finset.univ.erase j).erase i, p₁ x := by ac_rfl
    _ = (Nat.gcd (p₁ i) (p₁ j) * Nat.lcm (p₁ i) (p₁ j)) *
        ∏ x ∈ (Finset.univ.erase j).erase i, p₁ x := by rw [Nat.gcd_mul_lcm]
    _ = Nat.lcm (p₁ i) (p₁ j) *
        (Nat.gcd (p₁ i) (p₁ j) * ∏ x ∈ (Finset.univ.erase j).erase i, p₁ x) := by ac_rfl
    _ = Nat.lcm (p₁ i) (p₁ j) *
        (Nat.gcd (p₁ i) (p₁ j) * ∏ x ∈ (Finset.univ \ {j}) \ {i}, p₁ x) := by
          simp only [Finset.erase_eq]

def uniqueIndexRank (q : Fin 2026 → ℕ) : ℕ :=
  (∏ i, q i) * 2027 + (Finset.univ.filter fun i => 1 < q i).card

theorem uniqueIndex_activeCount_lt (q : Fin 2026 → ℕ) :
    (Finset.univ.filter fun i => 1 < q i).card < 2027 := by
  calc
    (Finset.univ.filter fun i => 1 < q i).card ≤ (Finset.univ : Finset (Fin 2026)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2026 := by rw [Finset.card_univ, Fintype.card_fin]
    _ < 2027 := by omega

theorem exists_rank_nondecrease (f : ℕ → ℕ) : ∃ n, f n ≤ f (n + 1) := by
  by_contra h
  push Not at h
  have hbound : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := h n
      omega
  have := hbound (f 0 + 1)
  omega

private theorem active_nonempty_of_validMove_candidate {q r : Fin 2026 → ℕ}
    (h : ValidMove q r) : ∃ k, 1 < r k := by
  rcases h with ⟨i, j, hij, hi, hj, hrest, hri, hrj⟩
  by_cases hg : 1 < Nat.gcd (q i) (q j)
  · exact ⟨i, by simpa [hri] using hg⟩
  · have hgpos : 0 < Nat.gcd (q i) (q j) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgeq : Nat.gcd (q i) (q j) = 1 := by omega
    have hqipos : 0 < q i := by omega
    have hdvd : q i ∣ Nat.lcm (q i) (q j) := Nat.dvd_lcm_left _ _
    have hlcm : 1 < Nat.lcm (q i) (q j) := by
      exact lt_of_lt_of_le hi (Nat.le_of_dvd (Nat.lcm_pos hqipos (by omega)) hdvd)
    refine ⟨j, ?_⟩
    rw [hrj, hgeq]
    simpa using hlcm

theorem uniqueIndex_pair_product (a b : ℕ) :
    Nat.gcd a b * (Nat.lcm a b / Nat.gcd a b) = Nat.lcm a b := by
  exact Nat.mul_div_cancel' ((Nat.gcd_dvd_left a b).trans (Nat.dvd_lcm_left a b))

private theorem active_support_antitone_of_validMove {q r : Fin 2026 → ℕ}
    (h : ValidMove q r) :
    (Finset.univ.filter fun k => 1 < r k) ⊆
      (Finset.univ.filter fun k => 1 < q k) := by
  rcases h with ⟨i, j, hij, hi, hj, hrest, hri, hrj⟩
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  by_cases hki : k = i
  · simpa [hki] using hi
  by_cases hkj : k = j
  · simpa [hkj] using hj
  rw [hrest k hki hkj] at hk
  exact hk

private theorem validMove_preserves_pos_local {q r : Fin 2026 → ℕ}
    (hq : ∀ k, 0 < q k) (hm : ValidMove q r) : ∀ k, 0 < r k := by
  rcases hm with ⟨i, j, hij, hi, hj, hrest, hri, hrj⟩
  intro k
  by_cases hki : k = i
  · subst k
    rw [hri]
    exact Nat.gcd_pos_of_pos_left _ (hq i)
  by_cases hkj : k = j
  · subst k
    rw [hrj]
    have hprod := uniqueIndex_pair_product (q i) (q j)
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.mul_zero] at hprod
    have := Nat.lcm_pos (hq i) (hq j)
    omega
  · rw [hrest k hki hkj]
    exact hq k

private theorem validMove_data_product {q r : Fin 2026 → ℕ} (h : ValidMove q r) :
    ∃ i j, i ≠ j ∧ 1 < q i ∧ 1 < q j ∧
      (∀ k, k ≠ i → k ≠ j → r k = q k) ∧
      r i = Nat.gcd (q i) (q j) ∧
      r j = Nat.lcm (q i) (q j) / Nat.gcd (q i) (q j) ∧
      (∏ k, q k) = Nat.gcd (q i) (q j) * ∏ k, r k := by
  set_option maxRecDepth 10000 in
  rcases h with ⟨i, j, hij, hi, hj, hrest, hri, hrj⟩
  refine ⟨i, j, hij, hi, hj, hrest, hri, hrj, ?_⟩
  let g := Nat.gcd (q i) (q j)
  have hr : r = Function.update (Function.update q i g) j
      (Nat.lcm (q i) (q j) / g) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [Function.update, hij, hri, g]
    by_cases hkj : k = j
    · subst k
      simp [Function.update, hrj, g]
    · simp [Function.update, hki, hkj, hrest k hki hkj]
  rw [hr]
  rw [Finset.prod_update_of_mem (by simp : j ∈ (Finset.univ : Finset (Fin 2026)))]
  have himem : i ∈ (Finset.univ : Finset (Fin 2026)) \ {j} := by simp [hij]
  rw [Finset.prod_update_of_mem himem]
  have himemErase : i ∈ (Finset.univ : Finset (Fin 2026)).erase j := by simp [hij]
  have hold : (∏ k, q k) =
      q j * (q i * ∏ x ∈ (Finset.univ.erase j).erase i, q x) := by
    rw [← Finset.mul_prod_erase (s := Finset.univ) (f := q) (Finset.mem_univ j)]
    rw [← Finset.mul_prod_erase (s := Finset.univ.erase j) (f := q) himemErase]
  rw [hold]
  dsimp [g]
  have hd : Nat.gcd (q i) (q j) ∣ Nat.lcm (q i) (q j) :=
    dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _)
  conv_rhs => rw [← Nat.mul_assoc, Nat.mul_div_cancel' hd]
  calc
    q j * (q i * ∏ x ∈ (Finset.univ.erase j).erase i, q x) =
        (q i * q j) * ∏ x ∈ (Finset.univ.erase j).erase i, q x := by ac_rfl
    _ = (Nat.gcd (q i) (q j) * Nat.lcm (q i) (q j)) *
        ∏ x ∈ (Finset.univ.erase j).erase i, q x := by rw [Nat.gcd_mul_lcm]
    _ = Nat.lcm (q i) (q j) *
        (Nat.gcd (q i) (q j) * ∏ x ∈ (Finset.univ.erase j).erase i, q x) := by ac_rfl
    _ = Nat.lcm (q i) (q j) *
        (Nat.gcd (q i) (q j) * ∏ x ∈ (Finset.univ \ {j}) \ {i}, q x) := by
          simp only [Finset.erase_eq]

theorem uniqueIndex_of_exists_no_pair {q : Fin 2026 → ℕ}
    (hex : ∃ k, 1 < q k)
    (hn : ¬ ∃ i j, i ≠ j ∧ 1 < q i ∧ 1 < q j) :
    ∃! k, 1 < q k := by
  rcases hex with ⟨k, hk⟩
  refine ⟨k, hk, ?_⟩
  intro y hy
  by_contra hne
  exact hn ⟨k, y, Ne.symm hne, hk, hy⟩

private theorem uniqueIndexRank_decreases_of_validMove {q r : Fin 2026 → ℕ}
    (hq : ∀ k, 0 < q k) (hm : ValidMove q r) :
    uniqueIndexRank r < uniqueIndexRank q := by
  obtain ⟨i, j, hij, hi, hj, hrest, hri, hrj, hprod⟩ := validMove_data_product hm
  have hrpos := validMove_preserves_pos_local hq hm
  have hprodpos : 0 < ∏ k, r k := Finset.prod_pos fun k _ => hrpos k
  let A := Finset.univ.filter fun k => 1 < q k
  let B := Finset.univ.filter fun k => 1 < r k
  have hsub : B ⊆ A := active_support_antitone_of_validMove hm
  by_cases hg : Nat.gcd (q i) (q j) = 1
  · have hiA : i ∈ A := by simp [A, hi]
    have hiB : i ∉ B := by simp [B, hri, hg]
    have hne : B ≠ A := by
      intro heq
      exact hiB (heq ▸ hiA)
    have hcard : B.card < A.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hprodEq : (∏ k, q k) = ∏ k, r k := by simpa [hg] using hprod
    simp only [uniqueIndexRank]
    change (∏ k, r k) * 2027 + B.card < (∏ k, q k) * 2027 + A.card
    omega
  · have hglt : 1 < Nat.gcd (q i) (q j) := by
      have := Nat.gcd_pos_of_pos_left (q j) (hq i)
      omega
    have hprodlt : (∏ k, r k) < ∏ k, q k := by
      rw [hprod]
      exact (Nat.lt_mul_iff_one_lt_left hprodpos).2 hglt
    have hA := uniqueIndex_activeCount_lt q
    have hB := uniqueIndex_activeCount_lt r
    simp only [uniqueIndexRank]
    omega

private theorem board_positive_all_times_candidate {p₀ : Fin 2026 → ℕ}
    (h0 : ∀ i, 1 < p₀ i) (p : ℕ → Fin 2026 → ℕ) (hp : ValidSeq p₀ p) :
    ∀ n k, 0 < p n k := by
  intro n
  induction n with
  | zero =>
      intro k
      rw [hp.1]
      exact lt_trans Nat.zero_lt_one (h0 k)
  | succ n ih =>
      intro k
      rcases hp.2 n with hmove | hstop
      · exact validMove_preserves_pos_local ih hmove k
      · rw [← hstop.1]
        exact ih k

private theorem active_nonempty_all_times_candidate {p₀ : Fin 2026 → ℕ}
    (h0 : ∀ i, 1 < p₀ i) (p : ℕ → Fin 2026 → ℕ) (hp : ValidSeq p₀ p) :
    ∀ n, ∃ k, 1 < p n k := by
  intro n
  induction n with
  | zero =>
      rw [hp.1]
      exact ⟨0, h0 0⟩
  | succ n ih =>
      rcases hp.2 n with hmove | hstop
      · exact active_nonempty_of_validMove_candidate hmove
      · rw [← hstop.1]
        exact ih

theorem unique_index_exists {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    ∀ p, ValidSeq p₀ p → ∃ j, ∃! k, 1 < p j k := by
  intro p hp
  have hpos := board_positive_all_times_candidate h0 p hp
  have hex := active_nonempty_all_times_candidate h0 p hp
  obtain ⟨n, hn⟩ := exists_rank_nondecrease (fun m => uniqueIndexRank (p m))
  rcases hp.2 n with hmove | hstop
  · have hlt := uniqueIndexRank_decreases_of_validMove (hpos n) hmove
    omega
  · exact ⟨n, uniqueIndex_of_exists_no_pair (hex n) hstop.2⟩

private noncomputable def p1Board (q : Fin 2026 → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset (Fin 2026)).val.map q

private lemma p1Board_split (q : Fin 2026 → ℕ) (i j : Fin 2026) (hij : i ≠ j) :
    p1Board q = q i ::ₘ q j ::ₘ ((Finset.univ.erase i).erase j).val.map q := by
  have hi : (Finset.univ.erase i).cons i (by simp) = Finset.univ := by
    ext x
    simp
  have hj : ((Finset.univ.erase i).erase j).cons j (by simp) =
      Finset.univ.erase i := by
    ext x
    simp only [Finset.mem_cons, Finset.mem_erase, Finset.mem_univ, and_true]
    grind
  have hiv := congrArg Finset.val hi
  have hjv := congrArg Finset.val hj
  simp only [Finset.cons_val] at hiv hjv
  unfold p1Board
  rw [← hiv, Multiset.map_cons, ← hjv, Multiset.map_cons]

-- The gcd of all exponents at one prime coordinate.
private def factorGCD (q : Fin 2026 → ℕ) (r : ℕ) : ℕ :=
  Finset.univ.gcd (fun i => (q i).factorization r)

private lemma p1Board_of_validMove {q₁ q₂ : Fin 2026 → ℕ}
    (hmove : ValidMove q₁ q₂) :
    ∃ i j R, i ≠ j ∧ 1 < q₁ i ∧ 1 < q₁ j ∧
      p1Board q₁ = q₁ i ::ₘ q₁ j ::ₘ R ∧
      p1Board q₂ = Nat.gcd (q₁ i) (q₁ j) ::ₘ
        (Nat.lcm (q₁ i) (q₁ j) / Nat.gcd (q₁ i) (q₁ j)) ::ₘ R := by
  set_option maxRecDepth 10000 in
    rcases hmove with ⟨i, j, hij, hi, hj, hrest, hpi, hpj⟩
    let R := ((Finset.univ.erase i).erase j).val.map q₁
    refine ⟨i, j, R, hij, hi, hj, p1Board_split q₁ i j hij, ?_⟩
    rw [p1Board_split q₂ i j hij, hpi, hpj]
    congr 2
    apply Multiset.map_congr rfl
    intro k hk
    have hk' : k ∈ (Finset.univ.erase i).erase j := hk
    have hkji : k ≠ j ∧ k ≠ i := by simpa using hk'
    exact hrest k hkji.2 hkji.1

-- The value reconstructed from the invariant prime-exponent gcds.
private def canonicalTerminalValue (p₀ : Fin 2026 → ℕ) : ℕ :=
  ∏ r ∈ (∏ i, p₀ i).primeFactors,
    r ^ (Finset.univ.gcd fun i => (p₀ i).factorization r)

private theorem board_pos_of_validMove {p₁ p₂ : Fin 2026 → ℕ}
    (hpos : ∀ k, 0 < p₁ k) (h : ValidMove p₁ p₂) : ∀ k, 0 < p₂ k := by
  rcases h with ⟨i, j, hij, hi, hj, hrest, hpi, hpj⟩
  intro k
  by_cases hki : k = i
  · subst k
    rw [hpi]
    exact Nat.gcd_pos_of_pos_left _ (hpos i)
  by_cases hkj : k = j
  · subst k
    rw [hpj]
    have hlcm : 0 < Nat.lcm (p₁ i) (p₁ j) := Nat.lcm_pos (hpos i) (hpos j)
    have hgcd : 0 < Nat.gcd (p₁ i) (p₁ j) := Nat.gcd_pos_of_pos_left _ (hpos i)
    have hdvd : Nat.gcd (p₁ i) (p₁ j) ∣ Nat.lcm (p₁ i) (p₁ j) :=
      dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _)
    exact Nat.div_pos (Nat.le_of_dvd hlcm hdvd) hgcd
  · rw [hrest k hki hkj]
    exact hpos k

private theorem board_pos_of_validSeq {p₀ : Fin 2026 → ℕ} {p : ℕ → Fin 2026 → ℕ}
    (hpos : ∀ k, 0 < p₀ k) (hp : ValidSeq p₀ p) : ∀ n k, 0 < p n k := by
  intro n
  induction n with
  | zero => simpa [hp.1] using hpos
  | succ n ih =>
      rcases hp.2 n with hm | ⟨heq, _⟩
      · simpa only [Nat.succ_eq_add_one] using board_pos_of_validMove ih hm
      · simpa only [Nat.succ_eq_add_one, ← heq] using ih

private lemma gcd_min_max_sub (x y : ℕ) :
    Nat.gcd (min x y) (max x y - min x y) = Nat.gcd x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]
    have hy : y - x + x = y := Nat.sub_add_cancel h
    rw [← hy]
    simp
  · rw [min_eq_right h, max_eq_left h]
    have hx : x - y + y = x := Nat.sub_add_cancel h
    rw [← hx]
    simp [Nat.gcd_comm]

private lemma factorization_move_coordinates (a b r : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (Nat.gcd a b).factorization r = min (a.factorization r) (b.factorization r) ∧
    (Nat.lcm a b / Nat.gcd a b).factorization r =
      max (a.factorization r) (b.factorization r) -
        min (a.factorization r) (b.factorization r) := by
  constructor
  · simp [Nat.factorization_gcd, ha.ne', hb.ne']
  · rw [Nat.factorization_div]
    · simp [Nat.factorization_lcm, Nat.factorization_gcd, ha.ne', hb.ne']
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _)

private lemma factorization_gcd_invariant_of_move_pair (a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd ((Nat.gcd a b).factorization r)
        ((Nat.lcm a b / Nat.gcd a b).factorization r) =
      Nat.gcd (a.factorization r) (b.factorization r) := by
  rw [Nat.factorization_div]
  · rw [Nat.factorization_gcd ha.ne' hb.ne',
      Nat.factorization_lcm ha.ne' hb.ne']
    simp only [Finsupp.coe_tsub, Pi.sub_apply]
    change Nat.gcd (min (a.factorization r) (b.factorization r))
        (max (a.factorization r) (b.factorization r) -
          min (a.factorization r) (b.factorization r)) =
      Nat.gcd (a.factorization r) (b.factorization r)
    rcases le_total (a.factorization r) (b.factorization r) with h | h
    · rw [min_eq_left h, max_eq_right h, Nat.gcd_sub_self_right h]
    · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h,
        Nat.gcd_comm]
  · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.dvd_lcm_left _ _)

private lemma dvd_min_max_sub_iff (d x y : ℕ) :
    d ∣ x ∧ d ∣ y ↔ d ∣ min x y ∧ d ∣ (max x y - min x y) := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy, max_eq_right hxy]
    constructor
    · rintro ⟨hdx, hdy⟩
      exact ⟨hdx, Nat.dvd_sub hdy hdx⟩
    · rintro ⟨hdx, hdsub⟩
      refine ⟨hdx, ?_⟩
      rw [← Nat.sub_add_cancel hxy]
      exact dvd_add hdsub hdx
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [min_eq_right hyx, max_eq_left hyx]
    constructor
    · rintro ⟨hdx, hdy⟩
      exact ⟨hdy, Nat.dvd_sub hdx hdy⟩
    · rintro ⟨hdy, hdsub⟩
      refine ⟨?_, hdy⟩
      rw [← Nat.sub_add_cancel hyx]
      exact dvd_add hdsub hdy

private lemma factorization_move_commonDivisor_iff
    (a b d r : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (d ∣ a.factorization r ∧ d ∣ b.factorization r) ↔
      (d ∣ (Nat.gcd a b).factorization r ∧
        d ∣ (Nat.lcm a b / Nat.gcd a b).factorization r) := by
  have hgl : Nat.gcd a b ∣ Nat.lcm a b :=
    dvd_trans (Nat.gcd_dvd_left a b) (Nat.dvd_lcm_left a b)
  rw [Nat.factorization_gcd ha.ne' hb.ne',
    Nat.factorization_div hgl,
    Nat.factorization_lcm ha.ne' hb.ne',
    Nat.factorization_gcd ha.ne' hb.ne']
  exact dvd_min_max_sub_iff d (a.factorization r) (b.factorization r)

private lemma finset_univ_gcd_pair_congr {ι : Type} [Fintype ι]
    (f g : ι → ℕ) (i j : ι) (hij : i ≠ j)
    (hrest : ∀ k, k ≠ i → k ≠ j → g k = f k)
    (hpair : Nat.gcd (g i) (g j) = Nat.gcd (f i) (f j)) :
    Finset.univ.gcd g = Finset.univ.gcd f := by
  classical
  have hu_i : (Finset.univ : Finset ι) = insert i (Finset.univ.erase i) := by
    exact (Finset.insert_erase (Finset.mem_univ i)).symm
  have hjmem : j ∈ (Finset.univ : Finset ι).erase i := by simp [hij.symm]
  have hu_j : (Finset.univ : Finset ι).erase i =
      insert j ((Finset.univ.erase i).erase j) := by
    exact (Finset.insert_erase hjmem).symm
  have hR : ((Finset.univ.erase i).erase j).gcd g =
      ((Finset.univ.erase i).erase j).gcd f := by
    apply Finset.gcd_congr rfl
    intro k hk
    have hkji : k ≠ j ∧ k ≠ i := by simpa using hk
    exact hrest k hkji.2 hkji.1
  rw [hu_i, hu_j, Finset.gcd_insert, Finset.gcd_insert,
    Finset.gcd_insert, Finset.gcd_insert]
  calc
    Nat.gcd (g i) (Nat.gcd (g j) (((Finset.univ.erase i).erase j).gcd g)) =
        Nat.gcd (Nat.gcd (g i) (g j)) (((Finset.univ.erase i).erase j).gcd g) := by
          rw [Nat.gcd_assoc]
    _ = Nat.gcd (Nat.gcd (f i) (f j)) (((Finset.univ.erase i).erase j).gcd f) := by
          rw [hpair, hR]
    _ = Nat.gcd (f i) (Nat.gcd (f j) (((Finset.univ.erase i).erase j).gcd f)) := by
          rw [Nat.gcd_assoc]

private lemma factorGCD_validMove {q₁ q₂ : Fin 2026 → ℕ}
    (hmove : ValidMove q₁ q₂) (r : ℕ) : factorGCD q₂ r = factorGCD q₁ r := by
  rcases hmove with ⟨i, j, hij, hi, hj, hrest, hpi, hpj⟩
  unfold factorGCD
  apply finset_univ_gcd_pair_congr _ _ i j hij
  · intro k hki hkj
    rw [hrest k hki hkj]
  · rw [hpi, hpj]
    exact factorization_gcd_invariant_of_move_pair (q₁ i) (q₁ j) r (by omega) (by omega)

private lemma validMove_factorization_commonDivisor_iff
    {q₁ q₂ : Fin 2026 → ℕ} (hmove : ValidMove q₁ q₂) (d r : ℕ) :
    (∀ k, d ∣ (q₁ k).factorization r) ↔
      (∀ k, d ∣ (q₂ k).factorization r) := by
  rcases hmove with ⟨i, j, hij, hi, hj, hrest, hqi, hqj⟩
  have hp := factorization_move_commonDivisor_iff
    (q₁ i) (q₁ j) d r (lt_trans Nat.zero_lt_one hi) (lt_trans Nat.zero_lt_one hj)
  constructor
  · intro h k
    by_cases hki : k = i
    · subst k
      rw [hqi]
      exact hp.mp ⟨h i, h j⟩ |>.1
    · by_cases hkj : k = j
      · subst k
        rw [hqj]
        exact hp.mp ⟨h i, h j⟩ |>.2
      · rw [hrest k hki hkj]
        exact h k
  · intro h k
    have hp' := hp.mpr ⟨by rw [← hqi]; exact h i, by rw [← hqj]; exact h j⟩
    by_cases hki : k = i
    · simpa [hki] using hp'.1
    · by_cases hkj : k = j
      · simpa [hkj] using hp'.2
      · rw [← hrest k hki hkj]
        exact h k

private lemma validSeq_factorization_commonDivisor_iff
    {p₀ : Fin 2026 → ℕ} {p : ℕ → Fin 2026 → ℕ}
    (hp : ValidSeq p₀ p) (n d r : ℕ) :
    (∀ k, d ∣ (p₀ k).factorization r) ↔
      (∀ k, d ∣ (p n k).factorization r) := by
  induction n with
  | zero => simp [hp.1]
  | succ n ih =>
      rcases hp.2 n with hm | ⟨heq, _⟩
      · exact ih.trans (validMove_factorization_commonDivisor_iff hm d r)
      · simpa [← heq] using ih

private lemma terminal_value_eq_of_validSeq
    {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i)
    {p q : ℕ → Fin 2026 → ℕ} (hp : ValidSeq p₀ p) (hq : ValidSeq p₀ q)
    {j l : ℕ} {k m : Fin 2026}
    (hup : ∃! x, 1 < p j x) (huq : ∃! x, 1 < q l x)
    (hpk : 1 < p j k) (hqm : 1 < q l m) : p j k = q l m := by
  apply Nat.factorization_inj
    (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hpk))
    (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hqm))
  ext r
  apply Nat.dvd_antisymm
  · have hallp : ∀ i, (p j k).factorization r ∣ (p j i).factorization r := by
      intro i
      by_cases hik : i = k
      · subst i
        exact dvd_rfl
      · have hnlt : ¬ 1 < p j i := fun hi => hik (hup.unique hi hpk)
        have hpos : 0 < p j i := board_pos_of_validSeq
          (fun x => lt_trans Nat.zero_lt_one (h0 x)) hp j i
        have hone : p j i = 1 := by omega
        simp [hone]
    have hall0 := (validSeq_factorization_commonDivisor_iff hp j
      ((p j k).factorization r) r).mpr hallp
    have hallq := (validSeq_factorization_commonDivisor_iff hq l
      ((p j k).factorization r) r).mp hall0
    exact hallq m
  · have hallq : ∀ i, (q l m).factorization r ∣ (q l i).factorization r := by
      intro i
      by_cases him : i = m
      · subst i
        exact dvd_rfl
      · have hnlt : ¬ 1 < q l i := fun hi => him (huq.unique hi hqm)
        have hpos : 0 < q l i := board_pos_of_validSeq
          (fun x => lt_trans Nat.zero_lt_one (h0 x)) hq l i
        have hone : q l i = 1 := by omega
        simp [hone]
    have hall0 := (validSeq_factorization_commonDivisor_iff hq l
      ((q l m).factorization r) r).mpr hallq
    have hallp := (validSeq_factorization_commonDivisor_iff hp j
      ((q l m).factorization r) r).mp hall0
    exact hallp k

private theorem gcd_min_max_sub_ds018b (a b : ℕ) :
    Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab, Nat.gcd_comm,
      Nat.gcd_sub_self_left hab, Nat.gcd_comm]
  · rw [min_eq_right hba, max_eq_left hba, Nat.gcd_sub_self_right hba,
      Nat.gcd_comm]

theorem universal_bound_exists {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    ∃ M, ∀ p, ValidSeq p₀ p → ∀ j, (∃! k, 1 < p j k) → ∀ k, 1 < p j k → p j k = M := by
  classical
  by_cases hex : ∃ p : ℕ → Fin 2026 → ℕ, ∃ j k,
      ValidSeq p₀ p ∧ (∃! x, 1 < p j x) ∧ 1 < p j k
  · rcases hex with ⟨p, j, k, hp, hup, hpk⟩
    refine ⟨p j k, ?_⟩
    intro q hq l huq m hqm
    exact terminal_value_eq_of_validSeq h0 hq hp huq hup hqm hpk
  · refine ⟨0, ?_⟩
    intro p hp j hup k hpk
    exact False.elim (hex ⟨p, j, k, hp, hup, hpk⟩)

theorem result {p₀ : Fin 2026 → ℕ} (h0 : ∀ i, 1 < p₀ i) :
    (∀ p, ValidSeq p₀ p → ∃ j, ∃! k, 1 < p j k) ∧
      ∃ M, ∀ p, ValidSeq p₀ p → ∀ j, (∃! k, 1 < p j k) → ∀ k, 1 < p j k → p j k = M := by
  exact ⟨unique_index_exists h0, universal_bound_exists h0⟩

end IMO2026P1
