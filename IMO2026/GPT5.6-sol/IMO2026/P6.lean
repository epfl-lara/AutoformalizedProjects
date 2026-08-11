import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

namespace IMO2026P6

private lemma result_strictMono {a : ℕ → ℕ}
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (h n).1.1

private lemma result_pairwise {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ i j, 1 < Nat.gcd (a i) (a j) := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hij)
    rw [Nat.gcd_comm]
    exact (h j).1.2 i (Nat.lt_succ_iff.mp hij)
  · simpa using one_lt i
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hji)
    exact (h i).1.2 j (Nat.lt_succ_iff.mp hji)

private lemma result_mem_range {a : ℕ → ℕ}
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    {m : ℕ} (hm0 : a 0 ≤ m) (hm : ∀ i, 1 < Nat.gcd m (a i)) :
    ∃ n, a n = m := by
  have hs := result_strictMono h
  have ha : ∀ n, a 0 + n ≤ a n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hn : a n < a (n + 1) := by simpa using hs (Nat.lt_succ_self n)
        omega
  have hex : ∃ n, m ≤ a n := ⟨m, by
    have := ha m
    omega⟩
  let k := Nat.find hex
  have hk : m ≤ a k := Nat.find_spec hex
  generalize hkdef : k = k' at hk
  rcases k' with _ | j
  · exact ⟨0, Nat.le_antisymm hm0 (by simpa using hk)⟩
  · have hj : a j < m := by
      have hnot : ¬m ≤ a j := by
        intro hle
        have hfind : Nat.find hex = j + 1 := by simpa [k] using hkdef
        have hjk : j < Nat.find hex := by omega
        exact Nat.find_min hex hjk hle
      omega
    have hle : a (j + 1) ≤ m := (h j).2 ⟨hj, fun i _ => hm i⟩
    exact ⟨j + 1, Nat.le_antisymm hle hk⟩

private lemma result_mem_iff {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    {m : ℕ} (hm0 : a 0 ≤ m) :
    (∀ i, 1 < Nat.gcd m (a i)) ↔ ∃ n, a n = m := by
  constructor
  · exact result_mem_range h hm0
  · rintro ⟨n, rfl⟩ i
    exact result_pairwise one_lt h n i

private lemma result_of_period {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    {L : ℕ} (hL : 0 < L)
    (hper : ∀ m, (∀ i, 1 < Nat.gcd (m + L) (a i)) ↔ ∀ i, 1 < Nat.gcd m (a i)) :
    ∃ T, 0 < T ∧ ∀ n, a (n + T) = a n + L := by
  have hp := result_pairwise one_lt h
  have hs := result_strictMono h
  have hbase : ∀ i, 1 < Nat.gcd (a 0 + L) (a i) :=
    (hper (a 0)).2 (hp 0)
  obtain ⟨T, hT⟩ := result_mem_range h (Nat.le_add_right _ _) hbase
  have Tpos : 0 < T := by
    by_contra hT0
    have : T = 0 := by omega
    subst T
    simp at hT
    omega
  refine ⟨T, Tpos, ?_⟩
  intro n
  induction n with
  | zero => simpa using hT
  | succ n ih =>
      have hidx : n + T + 1 = (n + 1) + T := by omega
      rw [← hidx]
      have hglob : ∀ i, 1 < Nat.gcd (a (n + 1) + L) (a i) :=
        (hper (a (n + 1))).2 (hp (n + 1))
      have hcur : a (n + T) < a (n + 1) + L := by
        rw [ih]
        exact Nat.add_lt_add_right (by simpa using hs (Nat.lt_succ_self n)) L
      have hupp : a (n + T + 1) ≤ a (n + 1) + L :=
        (h (n + T)).2 ⟨hcur, fun i _ => hglob i⟩
      have hxcur : a (n + T) < a (n + T + 1) := by
        simpa using hs (Nat.lt_succ_self (n + T))
      let y := a (n + T + 1) - L
      have hxy : a (n + T + 1) = y + L := by
        dsimp [y]
        rw [Nat.sub_add_cancel]
        rw [ih] at hxcur
        omega
      have hyglob : ∀ i, 1 < Nat.gcd y (a i) := by
        apply (hper y).1
        rw [← hxy]
        exact hp (n + T + 1)
      have hany : a n < y := by
        rw [ih] at hxcur
        rw [hxy] at hxcur
        omega
      have hlow : a (n + 1) ≤ y :=
        (h n).2 ⟨hany, fun i _ => hyglob i⟩
      rw [hxy]
      omega

private lemma result_of_common_bound {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    {B : ℕ} (hB : 0 < B)
    (hcommon : ∀ x i, (∀ j, 1 < Nat.gcd x (a j)) →
      ∃ d, 1 < d ∧ d ∣ x ∧ d ∣ a i ∧ d ∣ B) :
    ∃ T, 0 < T ∧ ∀ n, a (n + T) = a n + B := by
  apply result_of_period one_lt h hB
  intro m
  constructor
  · intro hm i
    obtain ⟨d, hd, hdm, hdai, hdB⟩ := hcommon (m + B) i hm
    have hdm' : d ∣ m :=
      (Nat.dvd_add_iff_left (k := d) (m := m) (n := B) hdB).mpr hdm
    have hdg : d ∣ Nat.gcd m (a i) := Nat.dvd_gcd hdm' hdai
    exact lt_of_lt_of_le hd
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m
        (by exact lt_trans Nat.zero_lt_one (one_lt i))) hdg)
  · intro hm i
    obtain ⟨d, hd, hdm, hdai, hdB⟩ := hcommon m i hm
    have hdmp : d ∣ m + B := dvd_add hdm hdB
    have hdg : d ∣ Nat.gcd (m + B) (a i) := Nat.dvd_gcd hdmp hdai
    exact lt_of_lt_of_le hd
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right (m + B)
        (by exact lt_trans Nat.zero_lt_one (one_lt i))) hdg)

private lemma result_mem_before {a : ℕ → ℕ}
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    {m n : ℕ} (hm0 : a 0 ≤ m) (hmn : m < a n)
    (hm : ∀ i < n, 1 < Nat.gcd m (a i)) :
    ∃ i < n, a i = m := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | j
      · omega
      · have hmle : m ≤ a j := by
          by_contra hnot
          have hajm : a j < m := by omega
          have hle : a (j + 1) ≤ m :=
            (h j).2 ⟨hajm, fun i hi => hm i (by omega)⟩
          omega
        rcases lt_or_eq_of_le hmle with hlt | heq
        · obtain ⟨i, hi, hai⟩ := ih j (by omega) hlt (fun i hi => hm i (by omega))
          exact ⟨i, by omega, hai⟩
        · exact ⟨j, by omega, heq.symm⟩

private lemma result_replace_large_prime {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ n q, Nat.Prime q → a 0 < q → q ∣ a n →
      ∃ l < n, ¬q ∣ a l ∧ ∀ p, Nat.Prime p → p ∣ a l → p ∣ a n := by
  have hp := result_pairwise one_lt h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro q hq hqbig hqan
      have han0 : a n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one (one_lt n))
      have hnpos : 0 < n := by
        by_contra hn
        have hn0 : n = 0 := by omega
        subst n
        have hqa0 : q ≤ a 0 := Nat.le_of_dvd (lt_trans Nat.zero_lt_one (one_lt 0)) hqan
        omega
      let b := (a n).divMaxPow q
      have hqb : ¬q ∣ b := Nat.not_dvd_divMaxPow hq.one_lt han0
      have hdecomp : q ^ padicValNat q (a n) * b = a n := by
        simp [b]
      have hbpos : 0 < b := by
        by_contra hb
        have hbz : b = 0 := by omega
        rw [hbz, mul_zero] at hdecomp
        exact han0 hdecomp.symm
      have prime_dvd_b {p : ℕ} (pp : Nat.Prime p) (hpan : p ∣ a n) (hpq : p ≠ q) :
          p ∣ b := by
        have hprod : p ∣ q ^ padicValNat q (a n) * b := by rwa [hdecomp]
        rcases pp.dvd_mul.mp hprod with hpqp | hpb
        · have hpq' : p ∣ q := pp.dvd_of_dvd_pow hpqp
          exact (hpq ((Nat.prime_dvd_prime_iff_eq pp hq).mp hpq')).elim
        · exact hpb
      have hbcompat : ∀ t < n, 1 < Nat.gcd b (a t) := by
        intro t htn
        by_cases hqat : q ∣ a t
        · obtain ⟨s, hst, hqas, hsupp⟩ := ih t htn q hq hqbig hqat
          let p := (Nat.gcd (a n) (a s)).minFac
          have hg : 1 < Nat.gcd (a n) (a s) := hp n s
          have pp : Nat.Prime p := Nat.minFac_prime (by omega)
          have hpan : p ∣ a n := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
          have hpas : p ∣ a s := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
          have hpq : p ≠ q := by
            intro heq
            apply hqas
            rw [← heq]
            exact hpas
          have hpb : p ∣ b := prime_dvd_b pp hpan hpq
          have hpat : p ∣ a t := hsupp p pp hpas
          have hpg : p ∣ Nat.gcd b (a t) := Nat.dvd_gcd hpb hpat
          exact lt_of_lt_of_le pp.one_lt
            (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right b
              (lt_trans Nat.zero_lt_one (one_lt t))) hpg)
        · let p := (Nat.gcd (a n) (a t)).minFac
          have hg : 1 < Nat.gcd (a n) (a t) := hp n t
          have pp : Nat.Prime p := Nat.minFac_prime (by omega)
          have hpan : p ∣ a n := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
          have hpat : p ∣ a t := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
          have hpq : p ≠ q := by
            intro heq
            apply hqat
            rw [← heq]
            exact hpat
          have hpb : p ∣ b := prime_dvd_b pp hpan hpq
          have hpg : p ∣ Nat.gcd b (a t) := Nat.dvd_gcd hpb hpat
          exact lt_of_lt_of_le pp.one_lt
            (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right b
              (lt_trans Nat.zero_lt_one (one_lt t))) hpg)
      have hb1 : 1 < b := by
        have hb0 := hbcompat 0 hnpos
        exact lt_of_lt_of_le hb0 (Nat.gcd_le_left (a 0) hbpos)
      obtain ⟨e, helo, hehi⟩ := exists_nat_pow_near (one_lt 0).le hb1
      let x := b ^ (e + 1)
      have hx0 : a 0 ≤ x := by dsimp [x]; omega
      have hv : 1 ≤ padicValNat q (a n) := by
        apply (Nat.pow_dvd_iff_le_padicValNat hq.ne_one han0).mp
        simpa using hqan
      have hqpow : q ≤ q ^ padicValNat q (a n) := by
        simpa using Nat.pow_le_pow_right hq.pos hv
      have hqban : q * b ≤ a n := by
        rw [← hdecomp]
        exact Nat.mul_le_mul_right b hqpow
      have hxlt : x < a n := by
        have hxb : x ≤ a 0 * b := by
          dsimp [x]
          rw [pow_succ]
          exact Nat.mul_le_mul_right b helo
        have habq : a 0 * b < q * b := Nat.mul_lt_mul_of_pos_right hqbig hbpos
        exact lt_of_le_of_lt hxb (lt_of_lt_of_le habq hqban)
      have hxcompat : ∀ t < n, 1 < Nat.gcd x (a t) := by
        intro t htn
        have hd : Nat.gcd b (a t) ∣ Nat.gcd x (a t) := by
          apply Nat.dvd_gcd
          · exact (Nat.gcd_dvd_left b (a t)).trans (dvd_pow_self b (by omega))
          · exact Nat.gcd_dvd_right b (a t)
        exact lt_of_lt_of_le (hbcompat t htn)
          (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right x
            (lt_trans Nat.zero_lt_one (one_lt t))) hd)
      obtain ⟨l, hln, hal⟩ := result_mem_before h hx0 hxlt hxcompat
      refine ⟨l, hln, ?_, ?_⟩
      · rw [hal]
        intro hqx
        apply hqb
        exact hq.dvd_of_dvd_pow hqx
      · intro p pp hpal
        rw [hal] at hpal
        have hpb : p ∣ b := pp.dvd_of_dvd_pow hpal
        exact hpb.trans ⟨q ^ padicValNat q (a n), by rw [Nat.mul_comm, hdecomp]⟩

private lemma result_common_small_prime {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ i j, ∃ p, Nat.Prime p ∧ p ≤ a 0 ∧ p ∣ a i ∧ p ∣ a j := by
  have hp := result_pairwise one_lt h
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro j
      let q := (Nat.gcd (a i) (a j)).minFac
      have hg : 1 < Nat.gcd (a i) (a j) := hp i j
      have hq : Nat.Prime q := Nat.minFac_prime (by omega)
      have hqai : q ∣ a i := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hqaj : q ∣ a j := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      by_cases hqsmall : q ≤ a 0
      · exact ⟨q, hq, hqsmall, hqai, hqaj⟩
      · have hqbig : a 0 < q := by omega
        obtain ⟨l, hli, hql, hsupp⟩ :=
          result_replace_large_prime one_lt h i q hq hqbig hqai
        obtain ⟨p, pp, hpsmall, hpal, hpaj⟩ := ih l hli j
        exact ⟨p, pp, hpsmall, hsupp p pp hpal, hpaj⟩

private lemma result_common_small_prime_external {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (h : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ x i, (∀ j, 1 < Nat.gcd x (a j)) →
      ∃ p, Nat.Prime p ∧ p ≤ a 0 ∧ p ∣ x ∧ p ∣ a i := by
  intro x i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hx
      let q := (Nat.gcd x (a i)).minFac
      have hg : 1 < Nat.gcd x (a i) := hx i
      have hq : Nat.Prime q := Nat.minFac_prime (by omega)
      have hqx : q ∣ x := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hqai : q ∣ a i := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      by_cases hqsmall : q ≤ a 0
      · exact ⟨q, hq, hqsmall, hqx, hqai⟩
      · have hqbig : a 0 < q := by omega
        obtain ⟨l, hli, hql, hsupp⟩ :=
          result_replace_large_prime one_lt h i q hq hqbig hqai
        obtain ⟨p, pp, hpsmall, hpx, hpal⟩ := ih l hli hx
        exact ⟨p, pp, hpsmall, hpx, hsupp p pp hpal⟩

/-- The sequence is indexed from zero: Lean's `a n` corresponds to `a_{n + 1}` in the
one-based statement of the problem. -/
theorem result {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∃ (T L : ℕ), 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  have hB : 0 < Nat.factorial (a 0) := Nat.factorial_pos _
  have hc : ∀ x i, (∀ j, 1 < Nat.gcd x (a j)) →
      ∃ d, 1 < d ∧ d ∣ x ∧ d ∣ a i ∧ d ∣ Nat.factorial (a 0) := by
    intro x i hx
    obtain ⟨p, pp, hpsmall, hpx, hpai⟩ :=
      result_common_small_prime_external one_lt one_lt_gcd x i hx
    exact ⟨p, pp.one_lt, hpx, hpai, Nat.dvd_factorial pp.pos hpsmall⟩
  obtain ⟨T, hT, hper⟩ :=
    result_of_common_bound one_lt one_lt_gcd hB hc
  exact ⟨T, Nat.factorial (a 0), hT, hB, hper⟩

end IMO2026P6
