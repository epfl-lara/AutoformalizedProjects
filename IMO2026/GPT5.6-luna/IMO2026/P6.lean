import Mathlib
import IMO2026.P6Helpers

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

namespace IMO2026P6

private lemma strict_increase_of_greedy_step {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ n, a n < a (n + 1) := by
  intro n
  exact (one_lt_gcd n).1.1

private lemma greedy_step_le_double {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ n, a (n + 1) ≤ 2 * a n := by
  intro n
  apply (one_lt_gcd n).2
  constructor
  · have hn := one_lt n
    omega
  · intro i hi
    by_cases h : i = n
    · subst i
      simpa [Nat.gcd_mul_left_left] using one_lt n
    · have hi' : i < n := lt_of_le_of_ne hi h
      have hn : 0 < n := by omega
      have hprev : 1 < Nat.gcd (a n) (a i) := by
        simpa [Nat.sub_add_cancel hn] using (one_lt_gcd (n - 1)).1.2 i (Nat.le_pred_of_lt hi')
      have hd : Nat.gcd (a n) (a i) ∣ Nat.gcd (2 * a n) (a i) := by
        exact Nat.gcd_dvd_gcd_mul_left_left (a n) (a i) 2
      have hia := one_lt i
      have hpos : 0 < Nat.gcd (2 * a n) (a i) :=
        Nat.gcd_pos_of_pos_right _ (by omega)
      exact lt_of_lt_of_le hprev (Nat.le_of_dvd hpos hd)

private lemma pairwise_gcd_of_greedy_step {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) := by
  intro i j hij
  have hj := (one_lt_gcd (j - 1)).1.2 i (Nat.le_pred_of_lt hij)
  simpa [Nat.sub_add_cancel (by omega : 0 < j)] using hj

private def admissible {a : ℕ → ℕ} (n m : ℕ) : Prop :=
  a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)

private lemma greedy_mem_admissible {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, admissible (a := a) n (a (n + 1)) := by
  intro n
  exact (one_lt_gcd n).1

private lemma greedy_le_of_admissible {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n m, admissible (a := a) n m → a (n + 1) ≤ m := by
  intro n m hm
  exact (one_lt_gcd n).2 hm

private lemma factorial_admissible_bound {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, ∃ m, a n < m ∧
      (∀ i ≤ n, 1 < Nat.gcd m (a i)) ∧
      m ≤ a n + Nat.factorial (a 0) := by
  intro n
  let F := Nat.factorial (a 0)
  let m := (a n / F + 1) * F
  have hF : 0 < F := by
    dsimp [F]
    exact Nat.factorial_pos _
  have ha0 : 0 < a 0 := by
    have h := one_lt 0
    omega
  have ha0dvd : a 0 ∣ F := by
    dsimp [F]
    exact Nat.dvd_factorial ha0 (le_refl _)
  have hgi : ∀ i, 1 < Nat.gcd (a i) (a 0) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa using one_lt 0
    · exact pairwise_gcd_of_greedy_step one_lt_gcd 0 i (Nat.pos_of_ne_zero hi)
  have hgi' : ∀ i, Nat.gcd (a i) (a 0) ∣ F := by
    intro i
    exact dvd_trans (Nat.gcd_dvd_right _ _) ha0dvd
  have hFgi : ∀ i, 1 < Nat.gcd m (a i) := by
    intro i
    have hd : Nat.gcd (a i) (a 0) ∣ m := by
      refine dvd_trans (hgi' i) ?_
      refine ⟨a n / F + 1, ?_⟩
      dsimp [m]
      simp [Nat.mul_comm]
    have hdg : Nat.gcd (a i) (a 0) ∣ Nat.gcd m (a i) :=
      Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
    have hai : 0 < a i := by
      have h := one_lt i
      omega
    have hgpos : 0 < Nat.gcd m (a i) := Nat.gcd_pos_of_pos_right _ hai
    have hle : Nat.gcd (a i) (a 0) ≤ Nat.gcd m (a i) :=
      Nat.le_of_dvd hgpos hdg
    exact lt_of_lt_of_le (hgi i) hle
  have hgt : a n < m := by
    have hrep : a n = (a n / F) * F + a n % F := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod (a n) F).symm
    rw [hrep]
    dsimp [m]
    simp only [Nat.add_mul, one_mul]
    have hr : a n % F < F := Nat.mod_lt _ hF
    omega
  have hle : m ≤ a n + F := by
    have hrep : a n = (a n / F) * F + a n % F := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod (a n) F).symm
    rw [hrep]
    dsimp [m]
    simp only [Nat.add_mul, one_mul]
    omega
  refine ⟨m, hgt, ?_, ?_⟩
  · intro i hi
    exact hFgi i
  · simpa [F] using hle

private lemma bounded_increment_alphabet {a : ℕ → ℕ}
    (hstep : ∀ n, a n < a (n + 1))
    (hbound : ∀ n, a (n + 1) ≤ a n + Nat.factorial (a 0)) :
    ∀ n, ∃ d, 0 < d ∧ d ≤ Nat.factorial (a 0) ∧ a (n + 1) = a n + d := by
  intro n
  let d := a (n + 1) - a n
  have hlt := hstep n
  have hle := Nat.le_of_lt hlt
  have hu := hbound n
  refine ⟨d, ?_, ?_, ?_⟩
  · dsimp [d]
    omega
  · dsimp [d]
    omega
  · dsimp [d]
    omega

private lemma gcd_gt_one_of_witness_family
    {D : Finset ℕ} {m x : ℕ}
    (hm : ∃ d ∈ D, d ∣ m)
    (hx : ∃ e ∈ D, e ∣ x)
    (hpair : ∀ d ∈ D, ∀ e ∈ D, 1 < Nat.gcd d e)
    (hmpos : 0 < m) (hxpos : 0 < x) :
    1 < Nat.gcd m x := by
  obtain ⟨d, hdD, hdm⟩ := hm
  obtain ⟨e, heD, hex⟩ := hx
  have hgd : Nat.gcd d e ∣ d := Nat.gcd_dvd_left _ _
  have hge : Nat.gcd d e ∣ e := Nat.gcd_dvd_right _ _
  have hdiv : Nat.gcd d e ∣ Nat.gcd m x :=
    Nat.dvd_gcd (dvd_trans hgd hdm) (dvd_trans hge hex)
  have hpos : 0 < Nat.gcd m x := Nat.gcd_pos_of_pos_right _ hxpos
  have hle : Nat.gcd d e ≤ Nat.gcd m x := Nat.le_of_dvd hpos hdiv
  exact lt_of_lt_of_le (hpair d hdD e heD) hle

private lemma consistency_model :
    let a : ℕ → ℕ := fun n => 2 * (n + 1)
    (∀ i, 1 < a i) ∧
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) := by
  dsimp
  constructor
  · intro i
    omega
  · intro n
    constructor
    · constructor
      · omega
      · intro i hi
        have hdm : 2 ∣ 2 * (n + 2) := by simp
        have hdi : 2 ∣ 2 * (i + 1) := by simp
        have hdg : 2 ∣ Nat.gcd (2 * (n + 2)) (2 * (i + 1)) :=
          Nat.dvd_gcd hdm hdi
        have hgpos : 0 < Nat.gcd (2 * (n + 2)) (2 * (i + 1)) :=
          Nat.gcd_pos_of_pos_right _ (by omega)
        exact lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd hgpos hdg)
    · intro m hm
      have hm' := hm.1
      have h0 := hm.2 0 (by omega)
      have h0' : 1 < Nat.gcd m 2 := by simpa using h0
      have hg_le : Nat.gcd m 2 ≤ 2 := Nat.gcd_le_right m (by omega)
      have hg_eq : Nat.gcd m 2 = 2 := by omega
      have hdm : 2 ∣ m := by
        rw [← hg_eq]
        exact Nat.gcd_dvd_left _ _
      obtain ⟨k, hk⟩ := hdm
      omega

private lemma admissible_shift_of_witness_family
    {a : ℕ → ℕ} {N L : ℕ} {D : Finset ℕ}
    (hchar : ∀ m, admissible (a := a) N m ↔ ∃ d ∈ D, d ∣ m)
    (hdiv : ∀ d ∈ D, d ∣ L) :
    ∀ m, admissible (a := a) N m → admissible (a := a) N (m + L) := by
  intro m hm
  apply (hchar (m + L)).2
  obtain ⟨d, hdD, hdm⟩ := (hchar m).1 hm
  refine ⟨d, hdD, ?_⟩
  exact dvd_add hdm (hdiv d hdD)

private lemma admissible_shift_of_threshold_witness_family
    {a : ℕ → ℕ} {N L : ℕ} {D : Finset ℕ}
    (hchar : ∀ m, a N < m →
      ((∀ i ≤ N, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m))
    (hdiv : ∀ d ∈ D, d ∣ L) :
    ∀ m, admissible (a := a) N m → admissible (a := a) N (m + L) := by
  intro m hm
  rcases hm with ⟨hmgt, hmG⟩
  have hmLgt : a N < m + L := by omega
  refine ⟨hmLgt, ?_⟩
  apply (hchar (m + L) hmLgt).2
  obtain ⟨d, hdD, hdm⟩ := (hchar m hmgt).1 hmG
  exact ⟨d, hdD, dvd_add hdm (hdiv d hdD)⟩

lemma finite_boundary_not_sufficient :
    let b : ℕ → ℕ := fun n => if n = 0 then 2 else 2 * (n + 2)
    (∀ n, 1 < b n) ∧
    (∀ n, b n < b (n + 1)) ∧
    (∀ n, b (n + 1) ≤ b n + 4) ∧
    (∀ i j, i < j → 1 < Nat.gcd (b j) (b i)) ∧
    ¬ ∃ (T L : ℕ), 0 < T ∧ 0 < L ∧ ∀ n, b (n + T) = b n + L := by
  dsimp
  have hpos : ∀ n : ℕ, 0 < (if n = 0 then 2 else 2 * (n + 2)) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  have heven : ∀ n : ℕ, 2 ∣ (if n = 0 then 2 else 2 * (n + 2)) := by
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  constructor
  · intro n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      omega
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hnp : n + 1 ≠ 0 := by omega
      simp [hn, hnp]
  constructor
  · intro n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hnp : n + 1 ≠ 0 := by omega
      simp [hn, hnp]
      omega
  constructor
  · intro i j hij
    have hd : 2 ∣ Nat.gcd
        (if j = 0 then 2 else 2 * (j + 2))
        (if i = 0 then 2 else 2 * (i + 2)) :=
      Nat.dvd_gcd (heven j) (heven i)
    have hg : 0 < Nat.gcd
        (if j = 0 then 2 else 2 * (j + 2))
        (if i = 0 then 2 else 2 * (i + 2)) :=
      Nat.gcd_pos_of_pos_right _ (hpos i)
    obtain ⟨k, hk⟩ := hd
    omega
  · rintro ⟨T, L, hT, hL, hper⟩
    have hT0 : T ≠ 0 := Nat.ne_of_gt hT
    have h0 := hper 0
    have h1 := hper 1
    simp [hT0] at h0 h1
    omega

private lemma greedy_shift_propagation
    {a : ℕ → ℕ} {T L : ℕ}
    (hT : 0 < T)
    (hgreedy : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hbase : ∀ n, n < T → a (n + T) = a n + L)
    (hcompat : ∀ n m, a n < m →
      ((∀ i ≤ n, 1 < Nat.gcd m (a i)) ↔
        (∀ i ≤ n + T, 1 < Nat.gcd (m + L) (a i)))) :
    ∀ n, a (n + T) = a n + L := by
  have hstep : ∀ n, a (n + T) = a n + L →
      a (n + 1 + T) = a (n + 1) + L := by
    intro n hshift
    have hxmem := (hgreedy n).1
    have hxgt : a n < a (n + 1) := hxmem.1
    have hxQ : ∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i) := hxmem.2
    have hxQL : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + 1) + L) (a i) :=
      (hcompat n (a (n + 1)) hxgt).1 hxQ
    have hcand : a (n + T) < a (n + 1) + L := by
      rw [hshift]
      omega
    have hle : a (n + T + 1) ≤ a (n + 1) + L :=
      (hgreedy (n + T)).2 ⟨hcand, hxQL⟩
    have hymem := (hgreedy (n + T)).1
    have hygt : a (n + T) < a (n + T + 1) := hymem.1
    have hyQ : ∀ i ≤ n + T, 1 < Nat.gcd (a (n + T + 1)) (a i) := hymem.2
    have hyminus : a n < a (n + T + 1) - L := by
      rw [hshift] at hygt
      omega
    have hLy : L ≤ a (n + T + 1) := by
      rw [hshift] at hygt
      omega
    have hyQ' : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + T + 1) - L + L) (a i) := by
      simpa [Nat.sub_add_cancel hLy] using hyQ
    have hyQL : ∀ i ≤ n, 1 < Nat.gcd (a (n + T + 1) - L) (a i) :=
      (hcompat n (a (n + T + 1) - L) hyminus).2 hyQ'
    have hle' : a (n + 1) ≤ a (n + T + 1) - L :=
      (hgreedy n).2 ⟨hyminus, hyQL⟩
    have heq : a (n + T + 1) = a (n + 1) + L := by
      omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < T
      · exact hbase n hn
      · have hnpos : 0 < n := by omega
        have hprev := ih (n - 1) (by omega)
        have hnext := hstep (n - 1) hprev
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hnext

private lemma descending_finset_stabilizes {α : Type} [Fintype α]
    (S : ℕ → Finset α) (hmono : ∀ n, S (n + 1) ⊆ S n) :
    ∃ N, ∀ n, N ≤ n → S n = S N := by
  classical
  have hex : ∃ k : ℕ, ∃ N : ℕ, (S N).card = k :=
    ⟨(S 0).card, 0, rfl⟩
  let k := Nat.find hex
  have hk : ∃ N : ℕ, (S N).card = k := Nat.find_spec hex
  obtain ⟨N, hN⟩ := hk
  have hmin : ∀ n, k ≤ (S n).card := by
    intro n
    exact Nat.find_min' hex ⟨n, rfl⟩
  have hsub : ∀ {i j : ℕ}, i ≤ j → S j ⊆ S i := by
    intro i j hij
    induction hij with
    | refl => exact Finset.Subset.rfl
    | @step j hij ih => exact Finset.Subset.trans (hmono j) ih
  refine ⟨N, ?_⟩
  intro n hn
  have hs : S n ⊆ S N := hsub hn
  have hmin' := hmin n
  have hminN : (S N).card ≤ (S n).card := by omega
  exact Finset.eq_of_subset_of_card_le hs hminN

private lemma tail_characterization_of_witness_family
    {a : ℕ → ℕ} {N : ℕ} {D : Finset ℕ}
    (hmono : ∀ i, N ≤ i → a N ≤ a i)
    (hpos : ∀ i, 0 < a i)
    (hchar : ∀ m, a N < m →
      ((∀ i ≤ N, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m))
    (hfuture : ∀ i, N ≤ i → ∃ d ∈ D, d ∣ a i)
    (hpair : ∀ d ∈ D, ∀ e ∈ D, 1 < Nat.gcd d e) :
    ∀ n, N ≤ n → ∀ m, a n < m →
      ((∀ i ≤ n, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m) := by
  intro n hn m hmn
  have hmN : a N < m := lt_of_le_of_lt (hmono n hn) hmn
  constructor
  · intro hall
    exact (hchar m hmN).1 (fun i hi => hall i (le_trans hi hn))
  · intro hw
    have hbase : ∀ i ≤ N, 1 < Nat.gcd m (a i) :=
      (hchar m hmN).2 hw
    have hmpos : 0 < m := lt_of_lt_of_le (hpos n) (Nat.le_of_lt hmn)
    intro i hi
    by_cases hin : i ≤ N
    · exact hbase i hin
    · have hNi : N ≤ i := Nat.le_of_lt (lt_of_not_ge hin)
      obtain ⟨e, heD, hei⟩ := hfuture i hNi
      exact gcd_gt_one_of_witness_family hw ⟨e, heD, hei⟩ hpair hmpos (hpos i)

private lemma greedy_step_eq_add_of_common_divisor
    {a : ℕ → ℕ} {p : ℕ}
    (hp : 1 < p)
    (hpos : ∀ n, 0 < a n)
    (hdiv : ∀ n, p ∣ a n)
    (hgreedy : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, a (n + 1) = a n + p := by
  intro n
  have hmem : a n + p ∈ {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} := by
    constructor
    · omega
    · intro i hi
      have hdp : p ∣ a n + p := dvd_add (hdiv n) (dvd_refl p)
      have hdi : p ∣ a i := hdiv i
      have hdg : p ∣ Nat.gcd (a n + p) (a i) := Nat.dvd_gcd hdp hdi
      have hgpos : 0 < Nat.gcd (a n + p) (a i) :=
        Nat.gcd_pos_of_pos_right _ (hpos i)
      exact lt_of_lt_of_le hp (Nat.le_of_dvd hgpos hdg)
  have hle := (hgreedy n).2 hmem
  have hgt := (hgreedy n).1.1
  have hdiffpos : 0 < a (n + 1) - a n := by omega
  have hpdiff : p ∣ a (n + 1) - a n := by
    exact Nat.dvd_sub (hdiv (n + 1)) (hdiv n)
  have hdiffge : p ≤ a (n + 1) - a n := Nat.le_of_dvd hdiffpos hpdiff
  omega

private lemma one_lt_gcd_iff_prime_support_inter {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) :
    1 < Nat.gcd u v ↔
      ∃ p, p ∈ u.primeFactors ∧ p ∈ v.primeFactors := by
  constructor
  · intro h
    obtain ⟨p, hp, hpd⟩ :=
      Nat.exists_prime_and_dvd (by omega : Nat.gcd u v ≠ 1)
    refine ⟨p, ?_, ?_⟩
    · apply Nat.mem_primeFactors.2
      exact ⟨hp, dvd_trans hpd (Nat.gcd_dvd_left u v), hu.ne'⟩
    · apply Nat.mem_primeFactors.2
      exact ⟨hp, dvd_trans hpd (Nat.gcd_dvd_right u v), hv.ne'⟩
  · rintro ⟨p, hpu, hpv⟩
    have hp : p.Prime := Nat.mem_primeFactors.mp hpu |>.1
    have hpd_u : p ∣ u := (Nat.mem_primeFactors.mp hpu).2.1
    have hpd_v : p ∣ v := (Nat.mem_primeFactors.mp hpv).2.1
    have hpd : p ∣ Nat.gcd u v := Nat.dvd_gcd hpd_u hpd_v
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hu) hpd)

private lemma prime_support_hits_initial {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, ∃ p, p ∈ (a 0).primeFactors ∧ p ∈ (a n).primeFactors := by
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using
      (one_lt_gcd_iff_prime_support_inter (ha_pos 0) (ha_pos 0)).1
        (by simpa using one_lt 0)
  · have hgn : 1 < Nat.gcd (a n) (a 0) := by
      simpa using
        (pairwise_gcd_of_greedy_step one_lt_gcd 0 n
          (Nat.pos_of_ne_zero hn))
    obtain ⟨p, hpn, hp0⟩ :=
      (one_lt_gcd_iff_prime_support_inter (ha_pos n) (ha_pos 0)).1 hgn
    exact ⟨p, hp0, hpn⟩

private lemma admissible_has_initial_prime {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n m, admissible (a := a) n m →
      ∃ p, p ∈ (a 0).primeFactors ∧ p ∣ m := by
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  intro n m hm
  have hgm : 1 < Nat.gcd m (a 0) := hm.2 0 (Nat.zero_le n)
  obtain ⟨p, hpm, hp0⟩ :=
    (one_lt_gcd_iff_prime_support_inter
      (lt_trans (ha_pos n) hm.1) (ha_pos 0)).1 hgm
  exact ⟨p, hp0, (Nat.mem_primeFactors.mp hpm).2.1⟩

private lemma a0_admissible_bound {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∀ n, ∃ m, a n < m ∧
      (∀ i ≤ n, 1 < Nat.gcd m (a i)) ∧
      m ≤ a n + a 0 := by
  intro n
  let A := a 0
  let m := (a n / A + 1) * A
  have hA : 0 < A := by
    dsimp [A]
    have h := one_lt 0
    omega
  have hgi : ∀ i, 1 < Nat.gcd (a i) (a 0) := by
    intro i
    by_cases hi : i = 0
    · subst i
      simpa using one_lt 0
    · exact pairwise_gcd_of_greedy_step one_lt_gcd 0 i (Nat.pos_of_ne_zero hi)
  have hAm : A ∣ m := by
    refine ⟨a n / A + 1, ?_⟩
    dsimp [m]
    simp [Nat.mul_comm]
  have hFgi : ∀ i, 1 < Nat.gcd m (a i) := by
    intro i
    have hd : Nat.gcd (a i) (a 0) ∣ m := by
      exact dvd_trans (Nat.gcd_dvd_right _ _) (by simpa [A] using hAm)
    have hdg : Nat.gcd (a i) (a 0) ∣ Nat.gcd m (a i) :=
      Nat.dvd_gcd hd (Nat.gcd_dvd_left _ _)
    have hai : 0 < a i := by
      have h := one_lt i
      omega
    have hgpos : 0 < Nat.gcd m (a i) := Nat.gcd_pos_of_pos_right _ hai
    have hle : Nat.gcd (a i) (a 0) ≤ Nat.gcd m (a i) :=
      Nat.le_of_dvd hgpos hdg
    exact lt_of_lt_of_le (hgi i) hle
  have hgt : a n < m := by
    have hrep : a n = (a n / A) * A + a n % A := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod (a n) A).symm
    rw [hrep]
    dsimp [m]
    simp only [Nat.add_mul, one_mul]
    have hr : a n % A < A := Nat.mod_lt _ hA
    omega
  have hle : m ≤ a n + A := by
    have hrep : a n = (a n / A) * A + a n % A := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod (a n) A).symm
    rw [hrep]
    dsimp [m]
    simp only [Nat.add_mul, one_mul]
    omega
  refine ⟨m, hgt, ?_, ?_⟩
  · intro i hi
    exact hFgi i
  · simpa [A] using hle

private lemma small_prime_of_consecutive {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, ∃ p, p.Prime ∧ p ≤ a 0 ∧ p ∣ a n ∧ p ∣ a (n + 1) := by
  have hpos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  have hstep : ∀ n, a n < a (n + 1) :=
    strict_increase_of_greedy_step one_lt_gcd
  have hbound : ∀ n, a (n + 1) ≤ a n + a 0 := by
    intro n
    obtain ⟨m, hmgt, hmad, hmle⟩ :=
      a0_admissible_bound one_lt one_lt_gcd n
    exact le_trans ((one_lt_gcd n).2 ⟨hmgt, hmad⟩) hmle
  intro n
  have hg : 1 < Nat.gcd (a (n + 1)) (a n) :=
    pairwise_gcd_of_greedy_step one_lt_gcd n (n + 1) (by omega)
  have hgne : Nat.gcd (a (n + 1)) (a n) ≠ 1 := by
    intro h
    rw [h] at hg
    omega
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgne
  have hpan : p ∣ a n := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  have hpan1 : p ∣ a (n + 1) := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hpdiff : p ∣ a (n + 1) - a n :=
    Nat.dvd_sub hpan1 hpan
  have hdiffpos : 0 < a (n + 1) - a n := by
    have hs := hstep n
    omega
  have hp_le_diff : p ≤ a (n + 1) - a n :=
    Nat.le_of_dvd hdiffpos hpdiff
  have hdiff_le : a (n + 1) - a n ≤ a 0 := by
    have hb := hbound n
    omega
  exact ⟨p, hp, le_trans hp_le_diff hdiff_le, hpan, hpan1⟩

private lemma result_of_stable_witness_family
    {a : ℕ → ℕ} {N T L : ℕ} {D : Finset ℕ}
    (hpos : ∀ i, 0 < a i)
    (hmono : ∀ i, N ≤ i → a N ≤ a i)
    (hgreedy : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hN : N < T)
    (hbase : ∀ n, n ≤ T → a (n + T) = a n + L)
    (hinit : ∀ i, i < N → a i ∣ L)
    (hchar : ∀ m, a N < m →
      ((∀ i ≤ N, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m))
    (hfuture : ∀ i, N ≤ i → ∃ d ∈ D, d ∣ a i)
    (hpair : ∀ d ∈ D, ∀ e ∈ D, 1 < Nat.gcd d e)
    (hdiv : ∀ d ∈ D, d ∣ L) :
    ∀ n, a (n + T) = a n + L := by
  have hcompat : ∀ n m, N ≤ n → a n < m →
      ((∀ i ≤ n, 1 < Nat.gcd m (a i)) ↔
        (∀ i ≤ n + T, 1 < Nat.gcd (m + L) (a i))) := by
    intro n m hn hmn
    have hmN : a N < m := lt_of_le_of_lt (hmono n hn) hmn
    have hmL_N : a N < m + L := by omega
    have hmpos : 0 < m := lt_trans (hpos n) hmn
    constructor
    · intro hall i hi
      by_cases hiN : i < N
      · have hgi : 1 < Nat.gcd m (a i) := hall i (by omega)
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd m (a i) ≠ 1)
        have hpm : p ∣ m := dvd_trans hpg (Nat.gcd_dvd_left _ _)
        have hpi : p ∣ a i := dvd_trans hpg (Nat.gcd_dvd_right _ _)
        have hpiL : p ∣ L := dvd_trans hpi (hinit i hiN)
        have hpml : p ∣ m + L := dvd_add hpm hpiL
        have hpgcd : p ∣ Nat.gcd (m + L) (a i) := Nat.dvd_gcd hpml hpi
        have hgpos : 0 < Nat.gcd (m + L) (a i) :=
          Nat.gcd_pos_of_pos_right _ (hpos i)
        exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpgcd)
      · have hiN' : N ≤ i := by omega
        obtain ⟨e, heD, hei⟩ := hfuture i hiN'
        obtain ⟨d, hdD, hdm⟩ := (hchar m hmN).1 (by
          intro j hj
          exact hall j (le_trans hj hn))
        have hdml : d ∣ m + L := dvd_add hdm (hdiv d hdD)
        exact gcd_gt_one_of_witness_family
          ⟨d, hdD, hdml⟩ ⟨e, heD, hei⟩ hpair
          (by omega) (hpos i)
    · intro hall i hi
      by_cases hiN : i < N
      · have hgi : 1 < Nat.gcd (m + L) (a i) := hall i (by omega)
        obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd (m + L) (a i) ≠ 1)
        have hpml : p ∣ m + L := dvd_trans hpg (Nat.gcd_dvd_left _ _)
        have hpi : p ∣ a i := dvd_trans hpg (Nat.gcd_dvd_right _ _)
        have hpiL : p ∣ L := dvd_trans hpi (hinit i hiN)
        have hpm' : p ∣ (m + L) - L := Nat.dvd_sub hpml hpiL
        have hpm : p ∣ m := by simpa using hpm'
        have hpgcd : p ∣ Nat.gcd m (a i) := Nat.dvd_gcd hpm hpi
        have hgpos : 0 < Nat.gcd m (a i) := Nat.gcd_pos_of_pos_right _ (hpos i)
        exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpgcd)
      · have hiN' : N ≤ i := by omega
        have hshiftN : ∀ j ≤ N, 1 < Nat.gcd (m + L) (a j) :=
          fun j hj => hall j (le_trans hj (by omega))
        obtain ⟨d, hdD, hdml⟩ := (hchar (m + L) hmL_N).1 hshiftN
        have hdm' : d ∣ (m + L) - L := Nat.dvd_sub hdml (hdiv d hdD)
        have hdm : d ∣ m := by simpa using hdm'
        obtain ⟨e, heD, hei⟩ := hfuture i hiN'
        exact gcd_gt_one_of_witness_family
          ⟨d, hdD, hdm⟩ ⟨e, heD, hei⟩ hpair hmpos (hpos i)
  have hstep : ∀ n, T ≤ n → a (n + T) = a n + L →
      a (n + 1 + T) = a (n + 1) + L := by
    intro n hn hshift
    have hxmem := (hgreedy n).1
    have hxgt : a n < a (n + 1) := hxmem.1
    have hxQ : ∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i) := hxmem.2
    have hxQL : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + 1) + L) (a i) :=
      (hcompat n (a (n + 1)) (by omega) hxgt).1 hxQ
    have hcand : a (n + T) < a (n + 1) + L := by
      rw [hshift]
      omega
    have hle : a (n + T + 1) ≤ a (n + 1) + L :=
      (hgreedy (n + T)).2 ⟨hcand, hxQL⟩
    have hymem := (hgreedy (n + T)).1
    have hygt : a (n + T) < a (n + T + 1) := hymem.1
    have hyQ : ∀ i ≤ n + T, 1 < Nat.gcd (a (n + T + 1)) (a i) := hymem.2
    have hyminus : a n < a (n + T + 1) - L := by
      rw [hshift] at hygt
      omega
    have hLy : L ≤ a (n + T + 1) := by
      rw [hshift] at hygt
      omega
    have hyQ' : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + T + 1) - L + L) (a i) := by
      simpa [Nat.sub_add_cancel hLy] using hyQ
    have hyQL : ∀ i ≤ n, 1 < Nat.gcd (a (n + T + 1) - L) (a i) :=
      (hcompat n (a (n + T + 1) - L) (by omega) hyminus).2 hyQ'
    have hle' : a (n + 1) ≤ a (n + T + 1) - L :=
      (hgreedy n).2 ⟨hyminus, hyQL⟩
    have heq : a (n + T + 1) = a (n + 1) + L := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ T
      · exact hbase n hn
      · have hnpos : 0 < n := by omega
        have hprev := ih (n - 1) (by omega)
        have hTprev : T ≤ n - 1 := by omega
        have hnext := hstep (n - 1) hTprev hprev
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hnext

private lemma common_divisor_branch {a : ℕ → ℕ} {p : ℕ}
    (hp : 1 < p) (hpos : ∀ n, 0 < a n)
    (hdiv : ∀ n, p ∣ a n)
    (hgreedy : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∃ T L : ℕ, 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  refine ⟨1, p, by omega, by omega, ?_⟩
  intro n
  simpa using greedy_step_eq_add_of_common_divisor hp hpos hdiv hgreedy n

private lemma future_initial_prime_divisor {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ i, ∃ p, p ∈ (a 0).primeFactors ∧ p ∣ a i := by
  intro i
  obtain ⟨p, hp0, hpi⟩ := prime_support_hits_initial one_lt one_lt_gcd i
  exact ⟨p, hp0, (Nat.mem_primeFactors.mp hpi).2.1⟩

private lemma result_of_shift_compatibility
    {a : ℕ → ℕ} {N T L : ℕ}
    (hgreedy : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hN : N < T)
    (hbase : ∀ n, n ≤ T → a (n + T) = a n + L)
    (hcompat : ∀ n m, N ≤ n → a n < m →
      ((∀ i ≤ n, 1 < Nat.gcd m (a i)) ↔
        (∀ i ≤ n + T, 1 < Nat.gcd (m + L) (a i)))) :
    ∀ n, a (n + T) = a n + L := by
  have hstep : ∀ n, T ≤ n → a (n + T) = a n + L →
      a (n + 1 + T) = a (n + 1) + L := by
    intro n hn hshift
    have hxmem := (hgreedy n).1
    have hxgt : a n < a (n + 1) := hxmem.1
    have hxQ : ∀ i ≤ n, 1 < Nat.gcd (a (n + 1)) (a i) := hxmem.2
    have hxQL : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + 1) + L) (a i) :=
      (hcompat n (a (n + 1)) (by omega) hxgt).1 hxQ
    have hcand : a (n + T) < a (n + 1) + L := by
      rw [hshift]
      omega
    have hle : a (n + T + 1) ≤ a (n + 1) + L :=
      (hgreedy (n + T)).2 ⟨hcand, hxQL⟩
    have hymem := (hgreedy (n + T)).1
    have hygt : a (n + T) < a (n + T + 1) := hymem.1
    have hyQ : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + T + 1)) (a i) := hymem.2
    have hyminus : a n < a (n + T + 1) - L := by
      rw [hshift] at hygt
      omega
    have hLy : L ≤ a (n + T + 1) := by
      rw [hshift] at hygt
      omega
    have hyQ' : ∀ i ≤ n + T,
        1 < Nat.gcd (a (n + T + 1) - L + L) (a i) := by
      simpa [Nat.sub_add_cancel hLy] using hyQ
    have hyQL : ∀ i ≤ n, 1 < Nat.gcd (a (n + T + 1) - L) (a i) :=
      (hcompat n (a (n + T + 1) - L) (by omega) hyminus).2 hyQ'
    have hle' : a (n + 1) ≤ a (n + T + 1) - L :=
      (hgreedy n).2 ⟨hyminus, hyQL⟩
    have heq : a (n + T + 1) = a (n + 1) + L := by omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heq
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n ≤ T
      · exact hbase n hn
      · have hnpos : 0 < n := by omega
        have hprev := ih (n - 1) (by omega)
        have hTprev : T ≤ n - 1 := by omega
        have hnext := hstep (n - 1) hTprev hprev
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hnext

private lemma witness_family_shift_iff {D : Finset ℕ} {L : ℕ}
    (hDdiv : ∀ d ∈ D, d ∣ L) :
    ∀ m, (∃ d ∈ D, d ∣ m) ↔ ∃ d ∈ D, d ∣ m + L := by
  intro m
  constructor
  · rintro ⟨d, hd, hdm⟩
    exact ⟨d, hd, dvd_add hdm (hDdiv d hd)⟩
  · rintro ⟨d, hd, hdmL⟩
    refine ⟨d, hd, ?_⟩
    simpa using Nat.dvd_sub hdmL (hDdiv d hd)

private lemma erased_product_pos {D : Finset ℕ}
    (hD : ∃ d ∈ D, d ≠ 0) :
    0 < ∏ d ∈ D.erase 0, d := by
  apply Finset.prod_pos
  intro d hd
  have hd0 : d ≠ 0 := (Finset.mem_erase.mp hd).1
  omega

private lemma large_prime_not_consecutive {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n q, q.Prime → a 0 < q → q ∣ a n → ¬ q ∣ a (n + 1) := by
  have hstep : ∀ n, a n < a (n + 1) :=
    strict_increase_of_greedy_step one_lt_gcd
  have hbound : ∀ n, a (n + 1) ≤ a n + a 0 := by
    intro n
    obtain ⟨m, hmgt, hmad, hmle⟩ :=
      a0_admissible_bound one_lt one_lt_gcd n
    exact le_trans ((one_lt_gcd n).2 ⟨hmgt, hmad⟩) hmle
  intro n q hq hqbig hqn
  intro hnext
  have hdiff : q ∣ a (n + 1) - a n := Nat.dvd_sub hnext hqn
  have hdiffpos : 0 < a (n + 1) - a n := by
    have hs := hstep n
    omega
  have hqle : q ≤ a (n + 1) - a n := Nat.le_of_dvd hdiffpos hdiff
  have hdiffle : a (n + 1) - a n ≤ a 0 := by
    have hb := hbound n
    omega
  omega

private lemma future_initial_witness_of_pairwise_prefix
    {a : ℕ → ℕ} {D : Finset ℕ}
    (one_lt : ∀ i, 1 < a i)
    (hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i))
    (hchar0 : ∀ m, 0 < m →
      ((∀ i ≤ 0, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m)) :
    ∀ i, ∃ d ∈ D, d ∣ a i := by
  intro i
  have hgi : 1 < Nat.gcd (a i) (a 0) := by
    by_cases hi0 : i = 0
    · subst i
      simpa only [Nat.gcd_self] using one_lt 0
    · exact hpair 0 i (Nat.pos_of_ne_zero hi0)
  have hall : ∀ j ≤ 0, 1 < Nat.gcd (a i) (a j) := by
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    simpa only [hj0] using hgi
  obtain ⟨d, hdD, hdi⟩ :=
    (hchar0 (a i) (lt_trans Nat.zero_lt_one (one_lt i))).1 hall
  exact ⟨d, hdD, hdi⟩

private lemma finite_prefix_state_audit {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i) :
    ∃ K : ℕ, ∃ D : Finset ℕ, 0 < K ∧
      ∀ m, 0 < m → ((∀ i ≤ 0, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m) := by
  simpa using finite_prefix_gcd_family (a := a) (N := 0) (by
    intro i
    have hi := one_lt i
    omega)

private lemma stable_char_of_initial_witness_family
    {a : ℕ → ℕ} {D : Finset ℕ}
    (hpos : ∀ i, 0 < a i)
    (hchar0 : ∀ m, 0 < m →
      ((∀ i ≤ 0, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m))
    (hfuture : ∀ i, ∃ d ∈ D, d ∣ a i)
    (hDpair : ∀ d ∈ D, ∀ e ∈ D, 1 < Nat.gcd d e) :
    ∀ m, 0 < m →
      ((∀ i, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D, d ∣ m) := by
  intro m hm
  constructor
  · intro hall
    apply (hchar0 m hm).1
    intro i hi
    exact hall i
  · rintro ⟨d, hdD, hdm⟩ i
    obtain ⟨e, heD, hei⟩ := hfuture i
    exact gcd_gt_one_of_witness_family
      ⟨d, hdD, hdm⟩ ⟨e, heD, hei⟩ hDpair
      hm (hpos i)

private lemma consistency_audit_reuse :
    ∃ (a : ℕ → ℕ),
      (∀ i, 1 < a i) ∧
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) ∧
      ∃ (T L : ℕ), 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  let a : ℕ → ℕ := fun n => 2 * (n + 1)
  have hmodel := consistency_model
  refine ⟨a, ?_, ?_, ?_⟩
  · simpa [a] using hmodel.1
  · simpa [a] using hmodel.2
  · refine ⟨1, 2, by omega, by omega, ?_⟩
    intro n
    simp [a]
    omega

private lemma finite_state_eventually_periodic_det {α : Type} [Fintype α]
    (s : ℕ → α) (f : α → α)
    (hrec : ∀ n, s (n + 1) = f (s n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → s (n + T) = s n := by
  obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite s
  rcases lt_or_gt_of_ne hij with hij' | hji
  · refine ⟨i, j - i, Nat.sub_pos_of_lt hij', ?_⟩
    have hper : ∀ k, s (i + k) = s (j + k) := by
      intro k
      induction k with
      | zero => simpa using heq
      | succ k ih =>
          rw [show i + (k + 1) = (i + k) + 1 by omega,
            show j + (k + 1) = (j + k) + 1 by omega,
            hrec, hrec, ih]
    intro n hn
    have hh := hper (n - i)
    have hright : i + (n - i) = n := Nat.add_sub_of_le hn
    have hleft : j + (n - i) = n + (j - i) := by
      omega
    calc
      s (n + (j - i)) = s (j + (n - i)) := congrArg s hleft.symm
      _ = s (i + (n - i)) := hh.symm
      _ = s n := congrArg s hright
  · refine ⟨j, i - j, Nat.sub_pos_of_lt hji, ?_⟩
    have hper : ∀ k, s (j + k) = s (i + k) := by
      intro k
      induction k with
      | zero => simpa using heq.symm
      | succ k ih =>
          rw [show j + (k + 1) = (j + k) + 1 by omega,
            show i + (k + 1) = (i + k) + 1 by omega,
            hrec, hrec, ih]
    intro n hn
    have hh := hper (n - j)
    have hright : j + (n - j) = n := Nat.add_sub_of_le hn
    have hleft : i + (n - j) = n + (i - j) := by
      omega
    calc
      s (n + (i - j)) = s (i + (n - j)) := congrArg s hleft.symm
      _ = s (j + (n - j)) := hh.symm
      _ = s n := congrArg s hright

private lemma bounded_pair_support_of_small_prime_pair
    {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (hsmall : ∀ i j, i < j →
      ∃ p, p.Prime ∧ p ≤ a 0 ∧ p ∣ a i ∧ p ∣ a j) :
    ∀ i j, i < j →
      ∃ p, p.Prime ∧ p ≤ a 0 ∧
        p ∈ (a i).primeFactors ∧ p ∈ (a j).primeFactors := by
  have hpos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  intro i j hij
  obtain ⟨p, hp, hpA, hpi, hpj⟩ := hsmall i j hij
  refine ⟨p, hp, hpA, ?_, ?_⟩
  · exact Nat.mem_primeFactors.2 ⟨hp, hpi, (hpos i).ne'⟩
  · exact Nat.mem_primeFactors.2 ⟨hp, hpj, (hpos j).ne'⟩

private lemma finite_support_history_residue_periodic
    {P : Finset ℕ} {M : ℕ} [NeZero M]
    (history : ℕ → Finset (Finset P))
    (residue : ℕ → Fin M)
    (next : Finset (Finset P) × Fin M → Finset (Finset P) × Fin M)
    (hrec : ∀ n,
      (history (n + 1), residue (n + 1)) =
        next (history n, residue n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n →
      (history (n + T), residue (n + T)) = (history n, residue n) := by
  simpa using
    (finite_state_eventually_periodic_det
      (s := fun n => (history n, residue n)) next hrec)

private lemma greedy_no_admissible_hole {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (n m : ℕ) (hmn : a n < m) (hmnext : m < a (n + 1)) :
    ∃ i ≤ n, Nat.gcd m (a i) ≤ 1 := by
  by_contra hbad
  push_neg at hbad
  have hmad : ∀ i ≤ n, 1 < Nat.gcd m (a i) := by
    intro i hi
    have hnot := hbad i hi
    omega
  have hle : a (n + 1) ≤ m := (one_lt_gcd n).2 ⟨hmn, hmad⟩
  omega

private lemma finite_initial_prime_history_residue_periodic
    {P : Finset ℕ} [NeZero (∏ p ∈ P, p)]
    (history : ℕ → Finset (Finset P))
    (residue : ℕ → Fin (∏ p ∈ P, p))
    (next : Finset (Finset P) × Fin (∏ p ∈ P, p) →
      Finset (Finset P) × Fin (∏ p ∈ P, p))
    (hrec : ∀ n,
      (history (n + 1), residue (n + 1)) =
        next (history n, residue n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n →
      (history (n + T), residue (n + T)) = (history n, residue n) := by
  simpa using
    (finite_state_eventually_periodic_det
      (s := fun n => (history n, residue n)) next hrec)

private lemma canonical_initial_prime_support
    {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, ∃ p ∈ (a 0).primeFactors, p ∣ a n := by
  have hpos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  intro n
  have hgn : 1 < Nat.gcd (a n) (a 0) := by
    by_cases hn : n = 0
    · subst n
      simpa using one_lt 0
    · exact pairwise_gcd_of_greedy_step one_lt_gcd 0 n (Nat.pos_of_ne_zero hn)
  have hgne : Nat.gcd (a n) (a 0) ≠ 1 := by omega
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgne
  have hpn : p ∣ a n := dvd_trans hpg (Nat.gcd_dvd_left _ _)
  have hp0 : p ∣ a 0 := dvd_trans hpg (Nat.gcd_dvd_right _ _)
  refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hp0, (hpos 0).ne'⟩, hpn⟩

private lemma amplify_eventual_period
    {α : Type} (σ : ℕ → α) {N T : ℕ}
    (hT : 0 < T)
    (hper : ∀ n, N ≤ n → σ (n + T) = σ n) :
    ∃ T', 0 < T' ∧ N < T' ∧ ∀ n, N ≤ n → σ (n + T') = σ n := by
  let T' := T * (N + 1)
  have hT' : 0 < T' := by
    dsimp [T']
    exact Nat.mul_pos hT (by omega)
  have hNT' : N < T' := by
    dsimp [T']
    nlinarith
  refine ⟨T', hT', hNT', ?_⟩
  intro n hn
  have hiter : ∀ k : ℕ, σ (n + T * k) = σ n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        σ (n + T * (k + 1)) = σ ((n + T * k) + T) := by
          simp [Nat.mul_succ, Nat.add_assoc]
        _ = σ (n + T * k) := hper (n + T * k) (by omega)
        _ = σ n := ih
  simpa [T', Nat.mul_comm] using hiter (N + 1)

private lemma affine_of_eventual_state_period
    {α : Type} (x : ℕ → ℕ) (σ : ℕ → α) (inc : α → ℕ)
    {N T : ℕ} (hT : 0 < T)
    (hper : ∀ n, N ≤ n → σ (n + T) = σ n)
    (hstep : ∀ n, x (n + 1) = x n + inc (σ n)) :
    ∃ L, ∀ n, N ≤ n → x (n + T) = x n + L := by
  have hmono : ∀ n k, x n ≤ x (n + k) := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        x n ≤ x (n + k) := ih
        _ ≤ x (n + k + 1) := by rw [hstep (n + k)]; omega
  let L := x (N + T) - x N
  have hdiff_step : ∀ n, N ≤ n →
      x (n + 1 + T) - x (n + 1) = x (n + T) - x n := by
    intro n hn
    have hs := hper n hn
    have h1 := hstep (n + T)
    have h2 := hstep n
    have heq : n + 1 + T = n + T + 1 := by omega
    rw [heq, h1, h2, hs]
    omega
  have hconst : ∀ k, x (N + k + T) - x (N + k) = L := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      calc
        x (N + (k + 1) + T) - x (N + (k + 1)) =
            x ((N + k) + 1 + T) - x ((N + k) + 1) := by congr 1 <;> omega
        _ = x (N + k + T) - x (N + k) := hdiff_step (N + k) (by omega)
        _ = L := ih
  refine ⟨L, ?_⟩
  intro n hn
  have hc : x (n + T) - x n = L := by
    have hk := hconst (n - N)
    rw [Nat.add_sub_of_le hn] at hk
    simpa [Nat.add_assoc] using hk
  have hle : x n ≤ x (n + T) := hmono n T
  omega

private lemma finite_small_prime_divisor_of_increment
    {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, ∃ p ∈ (Finset.range (a 0 + 1)).filter Nat.Prime,
      p ∣ a (n + 1) - a n := by
  intro n
  obtain ⟨p, hp, hple, hpn, hpn1⟩ :=
    small_prime_of_consecutive one_lt one_lt_gcd n
  refine ⟨p, ?_, Nat.dvd_sub hpn1 hpn⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hple, hp⟩

private lemma consistency_audit_even_affine :
    (∀ i : ℕ, 1 < 2 * i + 2) ∧
      (∀ n : ℕ, IsLeast
        {m | 2 * n + 2 < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (2 * i + 2)}
        (2 * (n + 1) + 2)) := by
  constructor
  · intro i
    omega
  · intro n
    constructor
    · constructor
      · omega
      · intro i hi
        have hdivm : 2 ∣ 2 * (n + 1) + 2 := by omega
        have hdivi : 2 ∣ 2 * i + 2 := by omega
        have hdivg : 2 ∣ Nat.gcd (2 * (n + 1) + 2) (2 * i + 2) :=
          Nat.dvd_gcd hdivm hdivi
        have hposg : 0 < Nat.gcd (2 * (n + 1) + 2) (2 * i + 2) :=
          Nat.gcd_pos_of_pos_left _ (by omega)
        have hle : 2 ≤ Nat.gcd (2 * (n + 1) + 2) (2 * i + 2) :=
          Nat.le_of_dvd hposg hdivg
        omega
    · intro m hm
      by_contra hlt
      have hmgt : 2 * n + 2 < m := hm.1
      have hle : m ≤ 2 * n + 3 := by omega
      have hge : 2 * n + 3 ≤ m := by omega
      have heq : m = 2 * n + 3 := by omega
      have h0 := hm.2 0 (by omega)
      rw [heq] at h0
      simp only [Nat.mul_zero] at h0
      have hodd : Odd (2 * n + 3) := ⟨n + 1, by omega⟩
      have hc : Nat.Coprime (2 * n + 3) 2 :=
        hodd.coprime_two_left.symm
      have hg : Nat.gcd (2 * n + 3) 2 = 1 :=
        (Nat.coprime_iff_gcd_eq_one).mp hc
      rw [hg] at h0
      omega

private lemma candidate_ap_shift_forward {p q m : ℕ} :
    (0 < m ∧ (2 * p ∣ m ∨ 2 * q ∣ m ∨ p * q ∣ m)) →
      0 < m + 2 * p * q ∧
        (2 * p ∣ m + 2 * p * q ∨
          2 * q ∣ m + 2 * p * q ∨
          p * q ∣ m + 2 * p * q) := by
  intro hm
  have hpos : 0 < m + 2 * p * q := by omega
  have h₁ : 2 * p ∣ 2 * p * q := by
    refine ⟨q, ?_⟩
    ring
  have h₂ : 2 * q ∣ 2 * p * q := by
    refine ⟨p, ?_⟩
    ring
  have h₃ : p * q ∣ 2 * p * q := by
    refine ⟨2, ?_⟩
    ring
  refine ⟨hpos, ?_⟩
  rcases hm.2 with h | h | h
  · exact Or.inl (dvd_add h h₁)
  · exact Or.inr (Or.inl (dvd_add h h₂))
  · exact Or.inr (Or.inr (dvd_add h h₃))

private lemma candidate_ap_shift_iff {p q m : ℕ} (hm : 0 < m) :
    (2 * p ∣ m ∨ 2 * q ∣ m ∨ p * q ∣ m) ↔
      (2 * p ∣ m + 2 * p * q ∨
        2 * q ∣ m + 2 * p * q ∨
        p * q ∣ m + 2 * p * q) := by
  have h₁ : 2 * p ∣ 2 * p * q := by
    refine ⟨q, ?_⟩
    ring
  have h₂ : 2 * q ∣ 2 * p * q := by
    refine ⟨p, ?_⟩
    ring
  have h₃ : p * q ∣ 2 * p * q := by
    refine ⟨2, ?_⟩
    ring
  constructor
  · intro h
    rcases h with h | h | h
    · exact Or.inl (dvd_add h h₁)
    · exact Or.inr (Or.inl (dvd_add h h₂))
    · exact Or.inr (Or.inr (dvd_add h h₃))
  · intro h
    rcases h with h | h | h
    · left
      have hs := Nat.dvd_sub h h₁
      simpa using hs
    · right; left
      have hs := Nat.dvd_sub h h₂
      simpa using hs
    · right; right
      have hs := Nat.dvd_sub h h₃
      simpa using hs

private lemma candidate_ap_pairwise_gcd {p q x y : ℕ}
    (hp : 1 < p) (hq : 1 < q) (hx : 0 < x) (hy : 0 < y)
    (hxm : 2 * p ∣ x ∨ 2 * q ∣ x ∨ p * q ∣ x)
    (hym : 2 * p ∣ y ∨ 2 * q ∣ y ∨ p * q ∣ y) :
    1 < Nat.gcd x y := by
  have common_of {d : ℕ} (hd : 1 < d) (hdx : d ∣ x) (hdy : d ∣ y) :
      1 < Nat.gcd x y := by
    have hdg := Nat.dvd_gcd hdx hdy
    have hgpos : 0 < Nat.gcd x y := by
      exact Nat.gcd_pos_of_pos_left y hx
    exact lt_of_lt_of_le hd (Nat.le_of_dvd hgpos hdg)
  have h2p : 2 ∣ 2 * p := by
    exact ⟨p, rfl⟩
  have h2q : 2 ∣ 2 * q := by
    exact ⟨q, rfl⟩
  have hp2p : p ∣ 2 * p := by
    refine ⟨2, ?_⟩
    ring
  have hq2q : q ∣ 2 * q := by
    refine ⟨2, ?_⟩
    ring
  have hpq : p ∣ p * q := by
    exact ⟨q, rfl⟩
  have hqq : q ∣ p * q := by
    refine ⟨p, ?_⟩
    ring
  rcases hxm with hxm | hxm | hxm <;>
    rcases hym with hym | hym | hym
  · exact common_of (by omega) (dvd_trans h2p hxm) (dvd_trans h2p hym)
  · exact common_of (by omega) (dvd_trans h2p hxm) (dvd_trans h2q hym)
  · exact common_of hp (dvd_trans hp2p hxm) (dvd_trans hpq hym)
  · exact common_of (by omega) (dvd_trans h2q hxm) (dvd_trans h2p hym)
  · exact common_of (by omega) (dvd_trans h2q hxm) (dvd_trans h2q hym)
  · exact common_of hq (dvd_trans hq2q hxm) (dvd_trans hqq hym)
  · exact common_of hp (dvd_trans hpq hxm) (dvd_trans hp2p hym)
  · exact common_of hq (dvd_trans hqq hxm) (dvd_trans hq2q hym)
  · exact common_of hp (dvd_trans hpq hxm) (dvd_trans hpq hym)

private lemma interval_candidate_lower_bound
    {p r : ℕ} (hpodd : p % 2 = 1)
    (hr : (p + 1) / 2 ≤ r) : p < 2 * r := by
  omega

private lemma interval_candidate_blocks
    {p q s r : ℕ}
    (hqpos : 0 < q)
    (hrlo : p < 2 * r)
    (hrhi : 2 * q * r < p * s)
    (hcop : Nat.Coprime (2 * q * r) (p * s)) :
    ∃ x, p * q < x ∧ x < p * s ∧ Nat.Coprime x (p * s) := by
  refine ⟨2 * q * r, ?_, hrhi, hcop⟩
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (Nat.mul_lt_mul_of_pos_right hrlo hqpos)

private lemma globalize_eventual_additive_shift {a : ℕ → ℕ} {T L N : ℕ}
    (hback : ∀ n, a (n + 1 + T) = a (n + 1) + L → a (n + T) = a n + L)
    (heventual : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  intro n
  by_cases hn : N ≤ n
  · exact heventual n hn
  · have hnlt : n < N := by omega
    exact Nat.decreasingInduction'
      (P := fun k => a (k + T) = a k + L) (m := n) (n := N)
      (fun k hk hkn ih => hback k ih) (Nat.le_of_lt hnlt)
      (heventual N (le_refl N))

private lemma shifted_history_admissible_iff_false :
    ¬ (∀ (a : ℕ → ℕ) (T L : ℕ),
      (∀ i, 1 < a i) →
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) →
      (∀ n, a (n + 1 + T) = a (n + 1) + L) →
      ∀ n m, a n < m →
        ((∀ i ≤ n, 1 < Nat.gcd m (a i)) ↔
          (∀ i ≤ n + T, 1 < Nat.gcd (m + L) (a i)))) := by
  let a : ℕ → ℕ := fun n => 2 * n + 6
  have hone : ∀ i, 1 < a i := by
    intro i
    dsimp [a]
    omega
  have hleast : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)) := by
    intro n
    constructor
    · constructor
      · dsimp [a]
        omega
      · intro i hi
        have hdivm : 2 ∣ a (n + 1) := by
          refine ⟨n + 4, ?_⟩
          dsimp [a]
          omega
        have hdivi : 2 ∣ a i := by
          refine ⟨i + 3, ?_⟩
          dsimp [a]
          omega
        have hdivg := Nat.dvd_gcd hdivm hdivi
        have hposg : 0 < Nat.gcd (a (n + 1)) (a i) := by
          apply Nat.gcd_pos_of_pos_left
          dsimp [a]
          omega
        have hle : 2 ≤ Nat.gcd (a (n + 1)) (a i) :=
          Nat.le_of_dvd hposg hdivg
        omega
    · intro m hm
      dsimp [a] at hm ⊢
      by_contra hlt
      have heq : m = 2 * n + 7 := by omega
      have hg : Nat.gcd (2 * n + 7) (2 * n + 6) = 1 := by
        have heq' : 2 * n + 7 = 1 + (2 * n + 6) := by omega
        rw [heq', Nat.gcd_add_self_left]
        simp
      have hbad := hm.2 n (by omega)
      rw [heq] at hbad
      rw [hg] at hbad
      omega
  have hshift : ∀ n, a (n + 1 + 1) = a (n + 1) + 2 := by
    intro n
    dsimp [a]
    omega
  intro h
  have hh := h a 1 2 hone hleast hshift 0 9 (by dsimp [a]; omega)
  have hleft : ∀ i ≤ 0, 1 < Nat.gcd 9 (a i) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    dsimp [a]
    norm_num
  have hright := hh.mp hleft
  have h0 := hright 0 (by omega)
  dsimp [a] at h0
  norm_num at h0

private lemma audit_target_model :
    ∃ (a : ℕ → ℕ),
      (∀ i, 1 < a i) ∧
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) ∧
      ∃ (T L : ℕ), 0 < T ∧ 0 < L ∧
        (∀ n, a (n + 1 + T) = a (n + 1) + L) ∧
        (∀ n, a (n + T) = a n + L) := by
  rcases consistency_audit_reuse with ⟨a, ha, hg, T, L, hT, hL, hs⟩
  refine ⟨a, ha, hg, T, L, hT, hL, ?_, hs⟩
  intro n
  exact hs (n + 1)

private lemma greedy_backward_shift_succ_index
    {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, 0 < n → a (n + T) = a n + L := by
  intro n hn
  have h := hshift_succ (n - 1)
  have hn1 : 1 ≤ n := by omega
  simpa [Nat.sub_add_cancel hn1, Nat.add_assoc] using h

private lemma greedy_backward_shift_reduce_to_zero {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    (∀ n, a (n + T) = a n + L) ↔ a T = a 0 + L := by
  constructor
  · intro h
    simpa using h 0
  · intro h0 n
    by_cases hn : 0 < n
    · exact greedy_backward_shift_succ_index hshift_succ n hn
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simpa using h0

private lemma greedy_backward_shift_boundary_reduction
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hboundary : a T = a 0 + L) :
    ∀ n, a (n + T) = a n + L := by
  intro n
  by_cases hn : 0 < n
  · exact greedy_backward_shift_succ_index hshift_succ n hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa using hboundary

private lemma greedy_backward_shift_boundary_iff_increment
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    (a T = a 0 + L) ↔
      (a (T + 1) - a T = a 1 - a 0) := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h0 : a 0 ≤ a 1 := Nat.le_of_lt (hinc 0)
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hinc T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  constructor
  · intro h
    rw [h, hs]
    omega
  · intro h
    omega

private lemma greedy_backward_shift_propagation_of_increment_boundary
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hincrement : a (T + 1) - a T = a 1 - a 0) :
    ∀ n, a (n + T) = a n + L := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h0 : a 0 ≤ a 1 := Nat.le_of_lt (hinc 0)
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hinc T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  have hboundary : a T = a 0 + L := by
    omega
  intro n
  by_cases hn : 0 < n
  · exact greedy_backward_shift_succ_index hshift_succ n hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simpa using hboundary

private lemma greedy_backward_shift_of_common_prime
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hp : ∃ p, Nat.Prime p ∧ p ∣ a 0 ∧ ∀ i, p ∣ a i) :
    ∀ n, a (n + T) = a n + L := by
  rcases hp with ⟨p, hpprime, hp0, hpall⟩
  have hp_pos : 0 < p := Nat.Prime.pos hpprime
  have hstep : ∀ n, a (n + 1) = a n + p := by
    intro n
    have hmem : ∀ i ≤ n, 1 < Nat.gcd (a n + p) (a i) := by
      intro i hi
      have hpd : p ∣ a n + p := by
        exact dvd_add (hpall n) (dvd_refl p)
      have hpg : p ∣ Nat.gcd (a n + p) (a i) :=
        Nat.dvd_gcd hpd (hpall i)
      have hposg : 0 < Nat.gcd (a n + p) (a i) := by
        apply Nat.gcd_pos_of_pos_left
        have han := one_lt n
        omega
      have hple : p ≤ Nat.gcd (a n + p) (a i) := Nat.le_of_dvd hposg hpg
      have hpp : 1 < p := hpprime.one_lt
      omega
    have hupper : a (n + 1) ≤ a n + p := by
      apply (one_lt_gcd n).2
      constructor
      · have han := one_lt n
        omega
      · exact hmem
    have hstrict := strict_increase_of_greedy_step one_lt_gcd n
    have hdiv : p ∣ a (n + 1) - a n := by
      exact Nat.dvd_sub (hpall (n + 1)) (hpall n)
    have hdiff : 0 < a (n + 1) - a n := by
      omega
    have hplower : p ≤ a (n + 1) - a n := Nat.le_of_dvd hdiff hdiv
    omega
  have hformula : ∀ n, a n = a 0 + n * p := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [hstep n, ih]
        simp [Nat.succ_mul, Nat.add_assoc]
  have hL : L = T * p := by
    have hs : a (T + 1) = a 1 + L := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
    rw [hformula (T + 1), hformula 1] at hs
    simp [Nat.succ_mul, Nat.add_assoc] at hs
    omega
  intro n
  rw [hformula (n + T), hformula n, hL]
  simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private lemma greedy_first_shift_prefix_witness :
    ∃ (a : ℕ → ℕ) (T L : ℕ),
      (∀ i ≤ 3, 1 < a i) ∧
      (IsLeast {m | a 0 < m ∧ ∀ i ≤ 0, 1 < Nat.gcd m (a i)} (a (0 + 1))) ∧
      (IsLeast {m | a 1 < m ∧ ∀ i ≤ 1, 1 < Nat.gcd m (a i)} (a (1 + 1))) ∧
      (IsLeast {m | a 2 < m ∧ ∀ i ≤ 2, 1 < Nat.gcd m (a i)} (a (2 + 1))) ∧
      a (1 + T) = a 1 + L ∧ a T ≠ a 0 + L := by
  let a : ℕ → ℕ := fun n =>
    match n with
    | 0 => 15
    | 1 => 18
    | 2 => 20
    | 3 => 24
    | _ => 100
  refine ⟨a, 2, 6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    interval_cases i <;> norm_num [a]
  · dsimp [a]
    constructor
    · constructor
      · norm_num
      · intro i hi
        have hi0 : i = 0 := by omega
        subst i
        norm_num
    · intro m hm
      rcases hm with ⟨hmgt, hmdiv⟩
      norm_num [a] at hmgt ⊢
      by_contra hnot
      have hle : m ≤ 17 := by omega
      have hge : 16 ≤ m := by omega
      interval_cases m <;>
        have hbad := hmdiv 0 (by omega) <;>
        norm_num [a] at hbad
  · dsimp [a]
    constructor
    · constructor
      · norm_num
      · intro i hi
        interval_cases i <;> norm_num [a]
    · intro m hm
      rcases hm with ⟨hmgt, hmdiv⟩
      norm_num [a] at hmgt ⊢
      by_contra hnot
      have hle : m ≤ 19 := by omega
      have hge : 19 ≤ m := by omega
      have heq : m = 19 := by omega
      subst m
      have hbad := hmdiv 0 (by omega)
      norm_num [a] at hbad
  · dsimp [a]
    constructor
    · constructor
      · norm_num
      · intro i hi
        interval_cases i <;> norm_num [a]
    · intro m hm
      rcases hm with ⟨hmgt, hmdiv⟩
      norm_num [a] at hmgt ⊢
      by_contra hnot
      have hle : m ≤ 23 := by omega
      have hge : 21 ≤ m := by omega
      interval_cases m
      · have hbad := hmdiv 2 (by omega)
        norm_num [a] at hbad
      · have hbad := hmdiv 0 (by omega)
        norm_num [a] at hbad
      · have hbad := hmdiv 0 (by omega)
        norm_num [a] at hbad
  · norm_num [a]
  · norm_num [a]

private lemma greedy_infinite_model
    : ∃ (a : ℕ → ℕ),
      (∀ i, 1 < a i) ∧
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) ∧
      a 0 = 15 := by
  classical
  let P : ℕ → Finset ℕ → ℕ → Prop :=
    fun x S m => x < m ∧ ∀ y ∈ S, 1 < Nat.gcd m y
  let next : ℕ → Finset ℕ → ℕ := fun x S =>
    if h : ∃ m, P x S m then Nat.find h else 0
  have hnext_spec : ∀ x S, (∃ m, P x S m) → P x S (next x S) := by
    intro x S h
    dsimp [next]
    split
    · rename_i h'
      exact Nat.find_spec h'
    · contradiction
  have hnext_min : ∀ x S, (∃ m, P x S m) →
      ∀ m, P x S m → next x S ≤ m := by
    intro x S h m hm
    dsimp [next]
    split
    · rename_i h'
      exact Nat.find_min' h' hm
    · contradiction
  let s : ℕ → ℕ × Finset ℕ :=
    Nat.rec (15, {15}) (fun _ q =>
      let z := next q.1 q.2
      (z, insert z q.2))
  have hs : ∀ n, s (n + 1) =
      (next (s n).1 (s n).2, insert (next (s n).1 (s n).2) (s n).2) := by
    intro n
    simp [s]
  have hinv : ∀ n, 1 < (s n).1 ∧
      (s n).1 ∈ (s n).2 ∧ ∀ y ∈ (s n).2, 1 < y := by
    intro n
    induction n with
    | zero =>
        norm_num [s]
    | succ n ih =>
        rw [hs n]
        change 1 < next (s n).1 (s n).2 ∧
          next (s n).1 (s n).2 ∈ insert (next (s n).1 (s n).2) (s n).2 ∧
          ∀ y ∈ insert (next (s n).1 (s n).2) (s n).2, 1 < y
        have hex : ∃ m, P (s n).1 (s n).2 m := by
          simpa [P] using greedy_history_product_witness ih.2.1 ih.2.2
        have hz := hnext_spec _ _ hex
        dsimp [P] at hz
        refine ⟨?_, ?_, ?_⟩
        · omega
        · simp
        · intro y hy
          simp only [Finset.mem_insert] at hy
          rcases hy with rfl | hy
          · omega
          · exact ih.2.2 y hy
  let a : ℕ → ℕ := fun n => (s n).1
  have ha_step : ∀ n, a (n + 1) = next (s n).1 (s n).2 := by
    intro n
    change (s (n + 1)).1 = _
    rw [hs n]
  have hmem : ∀ n y, y ∈ (s n).2 ↔ ∃ i, i ≤ n ∧ a i = y := by
    intro n
    induction n with
    | zero =>
        intro y
        simp [s, a, eq_comm]
    | succ n ih =>
        intro y
        rw [hs n]
        simp only [Finset.mem_insert]
        constructor
        · intro hy
          rcases hy with hy | hy
          · refine ⟨n + 1, le_rfl, ?_⟩
            exact (ha_step n).trans hy.symm
          · rcases (ih y).1 hy with ⟨i, hi, hai⟩
            exact ⟨i, by omega, hai⟩
        · rintro ⟨i, hi, hai⟩
          by_cases hEq : i = n + 1
          · subst i
            left
            exact hai.symm.trans (ha_step n)
          · right
            apply (ih y).2
            exact ⟨i, by omega, hai⟩
  have hone : ∀ i, 1 < a i := by
    intro i
    change 1 < (s i).1
    exact (hinv i).1
  have hgreedy : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)) := by
    intro n
    have hex : ∃ m, P (s n).1 (s n).2 m := by
      simpa [P] using greedy_history_product_witness (hinv n).2.1 (hinv n).2.2
    have hz := hnext_spec _ _ hex
    dsimp [P] at hz
    have hstep := ha_step n
    constructor
    · constructor
      · rw [hstep]
        exact hz.1
      · intro i hi
        have hiy : a i ∈ (s n).2 := (hmem n (a i)).2 ⟨i, hi, rfl⟩
        exact hz.2 _ hiy
    · intro m hm
      rcases hm with ⟨hmgt, hmall⟩
      have hmP : P (s n).1 (s n).2 m := by
        refine ⟨?_, ?_⟩
        · simpa [a] using hmgt
        · intro y hy
          rcases (hmem n y).1 hy with ⟨i, hi, hai⟩
          rw [← hai]
          exact hmall i hi
      have hmin := hnext_min _ _ hex m hmP
      rw [hstep]
      exact hmin
  refine ⟨a, hone, hgreedy, ?_⟩
  simp [a, s]

private lemma greedy_prefix_values
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (ha0 : a 0 = 15) :
    a 1 = 18 ∧ a 2 = 20 ∧ a 3 = 24 := by
  have h0 := one_lt_gcd 0
  have h18 : 15 < 18 ∧ ∀ i ≤ 0, 1 < Nat.gcd 18 (a i) := by
    constructor
    · norm_num
    · intro i hi
      have hi0 : i = 0 := by omega
      subst i
      norm_num [ha0]
  have h1le : a 1 ≤ 18 := by
    apply h0.2
    simpa [ha0] using h18
  have h1ge : 18 ≤ a 1 := by
    have hgt : 15 < a 1 := by simpa [ha0] using h0.1.1
    by_contra hnot
    have h16 : 16 ≤ a 1 := by omega
    have h17 : a 1 ≤ 17 := by omega
    have hor : a 1 = 16 ∨ a 1 = 17 := by omega
    rcases hor with h | h
    · have hbad := h0.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
    · have hbad := h0.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
  have ha1 : a 1 = 18 := by omega
  have h1 := one_lt_gcd 1
  have h20 : 18 < 20 ∧ ∀ i ≤ 1, 1 < Nat.gcd 20 (a i) := by
    constructor
    · norm_num
    · intro i hi
      interval_cases i <;> norm_num [ha0, ha1]
  have h2le : a 2 ≤ 20 := by
    apply h1.2
    simpa [ha1] using h20
  have h2ge : 20 ≤ a 2 := by
    have hgt : 18 < a 2 := by simpa [ha1] using h1.1.1
    by_contra hnot
    have h19 : a 2 = 19 := by omega
    have hbad := h1.1.2 0 (by omega)
    norm_num [ha0, h19] at hbad
  have ha2 : a 2 = 20 := by omega
  have h2 := one_lt_gcd 2
  have h24 : 20 < 24 ∧ ∀ i ≤ 2, 1 < Nat.gcd 24 (a i) := by
    constructor
    · norm_num
    · intro i hi
      interval_cases i <;> norm_num [ha0, ha1, ha2]
  have h3le : a 3 ≤ 24 := by
    apply h2.2
    simpa [ha2] using h24
  have h3ge : 24 ≤ a 3 := by
    have hgt : 20 < a 3 := by simpa [ha2] using h2.1.1
    by_contra hnot
    have hor : a 3 = 21 ∨ a 3 = 22 ∨ a 3 = 23 := by omega
    rcases hor with h | h | h
    · have hbad := h2.1.2 2 (by omega)
      norm_num [ha2, h] at hbad
    · have hbad := h2.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
    · have hbad := h2.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
  exact ⟨by omega, by omega, by omega⟩

private lemma greedy_zero_backward_boundary_iff_increment_from_first
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hfirst : a (1 + T) = a 1 + L) :
    (a T = a 0 + L) ↔
      (a (T + 1) - a T = a 1 - a 0) := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h0 : a 0 ≤ a 1 := Nat.le_of_lt (hinc 0)
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hinc T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfirst
  constructor
  · intro h
    rw [h, hs]
    omega
  · intro h
    omega

private lemma greedy_zero_backward_nonimplication_witness :
    ∃ (a : ℕ → ℕ) (T L : ℕ),
      (∀ i, 1 < a i) ∧
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) ∧
      a (1 + T) = a 1 + L ∧
      a T ≠ a 0 + L := by
  rcases greedy_infinite_model with ⟨a, hone, hgreedy, ha0⟩
  obtain ⟨ha1, ha2, ha3⟩ := greedy_prefix_values hgreedy ha0
  refine ⟨a, 2, 6, hone, hgreedy, ?_, ?_⟩
  · norm_num [ha1, ha3]
  · norm_num [ha0, ha2]

private lemma greedy_zero_backward_from_first_shift_is_false :
    ¬ (∀ {a : ℕ → ℕ} {T L : ℕ},
      (∀ i, 1 < a i) →
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) →
      a (1 + T) = a 1 + L →
      a T = a 0 + L) := by
  intro h
  obtain ⟨a, T, L, hone, hgreedy, hfirst, hneq⟩ :=
    greedy_zero_backward_nonimplication_witness
  exact hneq (h hone hgreedy hfirst)



private lemma greedy_prefix_fifth_value
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (ha0 : a 0 = 15) :
    a 1 = 18 ∧ a 2 = 20 ∧ a 3 = 24 ∧ a 4 = 30 := by
  obtain ⟨ha1, ha2, ha3⟩ := greedy_prefix_values one_lt_gcd ha0
  have h3 := one_lt_gcd 3
  have h30 : 24 < 30 ∧ ∀ i ≤ 3, 1 < Nat.gcd 30 (a i) := by
    constructor
    · norm_num
    · intro i hi
      interval_cases i <;> norm_num [ha0, ha1, ha2, ha3]
  have h4le : a 4 ≤ 30 := by
    apply h3.2
    simpa [ha3] using h30
  have h4ge : 30 ≤ a 4 := by
    have hgt : 24 < a 4 := by simpa [ha3] using h3.1.1
    by_contra hnot
    have hcases : a 4 = 25 ∨ a 4 = 26 ∨ a 4 = 27 ∨ a 4 = 28 ∨ a 4 = 29 := by omega
    rcases hcases with h | h | h | h | h
    · have hbad := h3.1.2 1 (by omega)
      norm_num [ha1, h] at hbad
    · have hbad := h3.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
    · have hbad := h3.1.2 2 (by omega)
      norm_num [ha2, h] at hbad
    · have hbad := h3.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
    · have hbad := h3.1.2 0 (by omega)
      norm_num [ha0, h] at hbad
  exact ⟨by omega, by omega, by omega, by omega⟩

private lemma greedy_backward_shift_suffix_candidate
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ n, a (n + T) < a (n + 1 + T) ∧
      ∀ i ≤ n, 1 < Nat.gcd (a (n + 1 + T)) (a (i + T)) := by
  intro n
  have hmem := (one_lt_gcd (n + T)).1
  constructor
  · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem.1
  · intro i hi
    have hi' : i + T ≤ n + T := by omega
    have h := hmem.2 (i + T) hi'
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private lemma shifted_increment_periodicity {a : ℕ → ℕ} {T L : ℕ}
    (hmono : ∀ i, a i ≤ a (i + 1))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, 0 < n →
      a (n + T + 1) - a (n + T) = a (n + 1) - a n := by
  intro n hn
  have hprev := hshift_succ (n - 1)
  have hnext := hshift_succ n
  have hn1 : 1 ≤ n := by omega
  have hprev' : a (n + T) = a n + L := by
    simpa [Nat.sub_add_cancel hn1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprev
  have hnext' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  have hle : a n ≤ a (n + 1) := hmono n
  omega

private lemma shifted_cross_identity {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, 0 < n →
      a (n + T + 1) + a n = a (n + 1) + a (n + T) := by
  intro n hn
  have hprev := hshift_succ (n - 1)
  have hnext := hshift_succ n
  have hn1 : 1 ≤ n := by omega
  have hprev' : a (n + T) = a n + L := by
    simpa [Nat.sub_add_cancel hn1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hprev
  have hnext' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  omega

private lemma greedy_backward_shift_zero_parameter_case {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hT : T = 0) :
    ∀ n, a (n + T) = a n + L := by
  subst T
  have hL : L = 0 := by
    have h := hshift_succ 0
    simp at h
    omega
  intro n
  simp [hL]

private lemma greedy_backward_shift_boundary_of_zero_shifted_history
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hcompat0 : ∀ m,
      ((∀ i ≤ 0, 1 < Nat.gcd m (a i)) ↔
        (∀ i ≤ T, 1 < Nat.gcd (m + L) (a i)))) :
    a T = a 0 + L := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h01 : a 0 < a 1 := hinc 0
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  have hzero_a0 : ∀ i ≤ 0, 1 < Nat.gcd (a 0) (a i) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using one_lt 0
  have hcand : ∀ i ≤ T, 1 < Nat.gcd (a 0 + L) (a i) := by
    simpa using (hcompat0 (a 0)).1 hzero_a0
  have hle : a 0 + L ≤ a T := by
    by_contra hnot
    have hlt : a T < a 0 + L := by omega
    have hmin := (one_lt_gcd T).2 ⟨hlt, hcand⟩
    rw [hs] at hmin
    omega
  have hge : a T ≤ a 0 + L := by
    by_contra hnot
    have hlt : a 0 + L < a T := by omega
    have hL : L ≤ a T := by
      have ha0 := one_lt 0
      omega
    have hzero_x : ∀ i ≤ T, 1 < Nat.gcd (a T) (a i) := by
      intro i hi
      by_cases hiT : i = T
      · subst i
        simpa using one_lt T
      · have hi_lt : i < T := by omega
        have hTpos : 1 ≤ T := by omega
        have hg := (one_lt_gcd (T - 1)).1.2 i (by omega)
        simpa [Nat.sub_add_cancel hTpos] using hg
    have hzero_m : ∀ i ≤ 0, 1 < Nat.gcd (a T - L) (a i) := by
      have hshifted := (hcompat0 (a T - L)).2
        (by simpa [Nat.sub_add_cancel hL] using hzero_x)
      simpa [Nat.sub_add_cancel hL] using hshifted
    have hmin := (one_lt_gcd 0).2 ⟨by omega, hzero_m⟩
    have hmin' := Nat.add_le_add_right hmin L
    rw [Nat.sub_add_cancel hL] at hmin'
    have hTlt' : a T < a 1 + L := by
      calc
        a T < a (T + 1) := hinc T
        _ = a 1 + L := hs
    exact (Nat.not_lt_of_ge hmin') hTlt'
  exact Nat.le_antisymm hge hle

private lemma greedy_backward_shift_increment_periodicity
    {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, 0 < n →
      a (n + T + 1) - a (n + T) = a (n + 1) - a n := by
  intro n hn
  have h1 := hshift_succ n
  have h0 := hshift_succ (n - 1)
  have hn1 : 1 ≤ n := by omega
  have h0' : a (n + T) = a n + L := by
    simpa [Nat.sub_add_cancel hn1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h0
  have h1' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  omega

private lemma additive_shift_boundary_iff_first_increment
    {a : ℕ → ℕ} {T L : ℕ}
    (hinc : ∀ n, a n < a (n + 1))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    (a T = a 0 + L) ↔
      (a (T + 1) - a T = a 1 - a 0) := by
  have h0 : a 0 ≤ a 1 := Nat.le_of_lt (hinc 0)
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hinc T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  constructor
  · intro h
    rw [h, hs]
    omega
  · intro h
    omega

private lemma greedy_backward_shift_propagation_iff_increment
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    (∀ n, a (n + T) = a n + L) ↔
      a (T + 1) - a T = a 1 - a 0 := by
  rw [greedy_backward_shift_reduce_to_zero hshift_succ,
    greedy_backward_shift_boundary_iff_increment one_lt_gcd hshift_succ]

private lemma greedy_backward_shift_prime_power_affine_common_prime
    {a : ℕ → ℕ} {p e : ℕ}
    (hp : Nat.Prime p)
    (he : 0 < e)
    (ha : ∀ n, a n = p ^ e + n * p) :
    ∃ q, Nat.Prime q ∧ q ∣ a 0 ∧ ∀ i, q ∣ a i := by
  refine ⟨p, hp, ?_, ?_⟩
  · rw [ha 0]
    simp only [Nat.zero_mul, Nat.add_zero]
    exact dvd_pow_self p (Nat.ne_of_gt he)
  · intro i
    rw [ha i]
    exact dvd_add (dvd_pow_self p (Nat.ne_of_gt he))
      (by simpa [Nat.mul_comm] using (dvd_mul_right p i))

private lemma greedy_backward_shift_prime_power_affine_propagation
    {a : ℕ → ℕ} {T L p e : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hp : Nat.Prime p)
    (he : 0 < e)
    (ha : ∀ n, a n = p ^ e + n * p) :
    ∀ n, a (n + T) = a n + L := by
  apply greedy_backward_shift_of_common_prime one_lt one_lt_gcd hshift_succ
  refine ⟨p, hp, ?_, ?_⟩
  · rw [ha 0]
    simp only [Nat.zero_mul, Nat.add_zero]
    exact dvd_pow_self p (Nat.ne_of_gt he)
  · intro i
    rw [ha i]
    exact dvd_add (dvd_pow_self p (Nat.ne_of_gt he))
      (by simpa [Nat.mul_comm] using (dvd_mul_right p i))

private lemma greedy_backward_shift_global_candidate_lower_bound
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hglobal : ∀ i, 1 < Nat.gcd (a 0 + L) (a i)) :
    a 0 + L ≤ a T := by
  have hstep0 := (one_lt_gcd 0).1
  have h0lt : a 0 < a 1 := by
    simpa using hstep0.1
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  by_contra hnot
  have hlt : a T < a 0 + L := Nat.lt_of_not_ge hnot
  have hle : a (T + 1) ≤ a 0 + L := by
    apply (one_lt_gcd T).2
    refine ⟨hlt, ?_⟩
    intro i hi
    exact hglobal i
  omega

private lemma prime_power_affine_common_prime
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e) :
    let a : ℕ → ℕ := fun n => p ^ e + n * p
    ∃ q, Nat.Prime q ∧ q ∣ a 0 ∧ ∀ i, q ∣ a i := by
  dsimp
  refine ⟨p, hp, ?_, ?_⟩
  · simpa using dvd_pow_self p (Nat.ne_of_gt he)
  · intro i
    apply dvd_add
    · exact dvd_pow_self p (Nat.ne_of_gt he)
    · simpa [Nat.mul_comm] using (dvd_mul_right p i)

private lemma candidate_tail_terms_share_shift_gcd
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hT : 0 < T) :
    ∀ i, 1 < Nat.gcd L (a (i + 1)) := by
  intro i
  have hmem := (one_lt_gcd (i + T)).1
  have hpair := hmem.2 (i + 1) (by omega)
  have hpair' : 1 < Nat.gcd (a (i + 1 + T)) (a (i + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpair
  rw [hshift_succ i] at hpair'
  rw [Nat.add_comm (a (i + 1)) L, Nat.gcd_add_self_left] at hpair'
  exact hpair'

private lemma prime_power_greedy_recurrence
    {p e : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (one_lt : ∀ n, 1 < p ^ e + n * p)
    (one_lt_gcd : ∀ n, IsLeast
      {m | p ^ e + n * p < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (p ^ e + i * p)}
      (p ^ e + (n + 1) * p)) :
    ∀ n, p ^ e + (n + 1) * p = (p ^ e + n * p) + p := by
  have hpos : ∀ n, 0 < p ^ e + n * p := by
    intro n
    have hp_pos : 0 < p := hp.pos
    have hpow_pos : 0 < p ^ e := pow_pos hp_pos e
    omega
  have hdiv : ∀ n, p ∣ p ^ e + n * p := by
    intro n
    exact dvd_add (dvd_pow_self p (Nat.ne_of_gt he))
      (by simpa [Nat.mul_comm] using (dvd_mul_right p n))
  have hstep := greedy_step_eq_add_of_common_divisor
    (a := fun n => p ^ e + n * p) hp.one_lt hpos hdiv one_lt_gcd
  intro n
  exact hstep n

private lemma prime_power_affine_backward_shift
    {p e T L : ℕ} (hp : Nat.Prime p) (he : 0 < e)
    (one_lt : ∀ i, 1 < p ^ e + i * p)
    (one_lt_gcd : ∀ n, IsLeast
      {m | p ^ e + n * p < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (p ^ e + i * p)}
      (p ^ e + (n + 1) * p))
    (hshift_succ : ∀ n,
      p ^ e + (n + 1 + T) * p = (p ^ e + (n + 1) * p) + L) :
    ∀ n, p ^ e + (n + T) * p = (p ^ e + n * p) + L := by
  apply greedy_backward_shift_of_common_prime
    (a := fun n => p ^ e + n * p) (T := T) (L := L)
    one_lt one_lt_gcd hshift_succ
  refine ⟨p, hp, ?_, ?_⟩
  · simpa using dvd_pow_self p (Nat.ne_of_gt he)
  · intro i
    exact dvd_add (dvd_pow_self p (Nat.ne_of_gt he))
      (by simpa [Nat.mul_comm] using (dvd_mul_right p i))

private lemma audit_forward_transport_not_derivable :
    ¬ (∀ (a : ℕ → ℕ) (T L : ℕ),
      (∀ i, 1 < a i) →
      (∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) →
      (∀ n, a (n + 1 + T) = a (n + 1) + L) →
      ∀ m i, i ≤ T →
        (∀ j ≤ 0, 1 < Nat.gcd m (a j)) →
          1 < Nat.gcd (m + L) (a i)) := by
  intro h
  let a : ℕ → ℕ := fun n => 2 * n + 6
  have hone : ∀ i, 1 < a i := by
    intro i
    dsimp [a]
    omega
  have hleast : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)) := by
    intro n
    constructor
    · constructor
      · dsimp [a]
        omega
      · intro i hi
        have hdivm : 2 ∣ a (n + 1) := by
          refine ⟨n + 4, ?_⟩
          dsimp [a]
          omega
        have hdivi : 2 ∣ a i := by
          refine ⟨i + 3, ?_⟩
          dsimp [a]
          omega
        have hdivg := Nat.dvd_gcd hdivm hdivi
        have hposg : 0 < Nat.gcd (a (n + 1)) (a i) := by
          apply Nat.gcd_pos_of_pos_left
          dsimp [a]
          omega
        have hle : 2 ≤ Nat.gcd (a (n + 1)) (a i) :=
          Nat.le_of_dvd hposg hdivg
        omega
    · intro m hm
      dsimp [a] at hm ⊢
      by_contra hnot
      have heq : m = 2 * n + 7 := by omega
      have hg : Nat.gcd (2 * n + 7) (2 * n + 6) = 1 := by
        have heq' : 2 * n + 7 = 1 + (2 * n + 6) := by omega
        rw [heq', Nat.gcd_add_self_left]
        simp
      have hbad := hm.2 n (by omega)
      rw [heq] at hbad
      rw [hg] at hbad
      omega
  have hshift : ∀ n, a (n + 1 + 1) = a (n + 1) + 2 := by
    intro n
    dsimp [a]
    omega
  have hh := h a 1 2 hone hleast hshift
  have hleft : ∀ j ≤ 0, 1 < Nat.gcd 9 (a j) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    dsimp [a]
    norm_num
  have hbad := hh 9 0 (by omega) hleft
  dsimp [a] at hbad
  norm_num at hbad

private lemma audit_boundary_from_endpoint_admissibility
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hupper : ∀ i ≤ T, 1 < Nat.gcd (a 0 + L) (a i))
    (hlower : a 0 + L < a T → 1 < Nat.gcd (a T - L) (a 0)) :
    a T = a 0 + L := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  have hle : a 0 + L ≤ a T := by
    by_contra hnot
    have hlt : a T < a 0 + L := by omega
    have hmin := (one_lt_gcd T).2 ⟨hlt, hupper⟩
    rw [hs] at hmin
    have h01 : a 0 < a 1 := hinc 0
    omega
  have hge : a T ≤ a 0 + L := by
    by_contra hnot
    have hlt : a 0 + L < a T := by omega
    have hL : L ≤ a T := by
      have ha0 := one_lt 0
      omega
    have hzero : ∀ i ≤ 0, 1 < Nat.gcd (a T - L) (a i) := by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      exact hlower hlt
    have hmin := (one_lt_gcd 0).2 ⟨by omega, hzero⟩
    have hmin' := Nat.add_le_add_right hmin L
    rw [Nat.sub_add_cancel hL] at hmin'
    have hTlt' : a T < a 1 + L := by
      calc
        a T < a (T + 1) := hinc T
        _ = a 1 + L := hs
    exact (Nat.not_lt_of_ge hmin') hTlt'
  exact Nat.le_antisymm hge hle

private lemma greedy_backward_shift_boundary_dichotomy
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hneq : a T ≠ a 0 + L) :
    (a T < a 0 + L ∧ ∃ i ≤ T, Nat.gcd (a 0 + L) (a i) = 1) ∨
      (a 0 + L < a T ∧ Nat.gcd (a T - L) (a 0) = 1) := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h01 : a 0 < a 1 := hinc 0
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hinc T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  by_cases hlt : a T < a 0 + L
  · left
    refine ⟨hlt, ?_⟩
    have hupper : a 0 + L < a (T + 1) := by
      rw [hs]
      omega
    have hnot : ¬ (∀ i ≤ T, 1 < Nat.gcd (a 0 + L) (a i)) := by
      intro hgood
      have hmin := (one_lt_gcd T).2 ⟨by omega, hgood⟩
      rw [hs] at hmin
      omega
    have hex : ∃ i, i ≤ T ∧ ¬ (1 < Nat.gcd (a 0 + L) (a i)) := by
      by_contra h
      apply hnot
      intro i hi
      by_contra hbad
      apply h
      exact ⟨i, hi, hbad⟩
    rcases hex with ⟨i, hi, hbad⟩
    refine ⟨i, hi, ?_⟩
    have hgpos : 0 < Nat.gcd (a 0 + L) (a i) := by
      apply Nat.gcd_pos_of_pos_left
      have ha0 := one_lt 0
      omega
    omega
  · have hgt : a 0 + L < a T := by omega
    right
    refine ⟨hgt, ?_⟩
    have hnot : ¬ (1 < Nat.gcd (a T - L) (a 0)) := by
      intro hgood
      have hmem : a T - L ∈ {m | a 0 < m ∧ ∀ i ≤ 0, 1 < Nat.gcd m (a i)} := by
        constructor
        · omega
        · intro i hi
          have hi0 : i = 0 := by omega
          subst i
          exact hgood
      have hmin := (one_lt_gcd 0).2 hmem
      have hmin' : a 1 ≤ a T - L := by simpa using hmin
      have hlt1 : a T - L < a 1 := by
        have hnext := hT
        rw [hs] at hnext
        omega
      exact (Nat.not_lt_of_ge hmin') hlt1
    have hgpos : 0 < Nat.gcd (a T - L) (a 0) := by
      apply Nat.gcd_pos_of_pos_left
      have ha0 := one_lt 0
      omega
    omega

private lemma greedy_backward_shift_signed_defect
    {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ((a T : ℤ) - (a 0 : ℤ) - (L : ℤ)) =
      ((a 1 : ℤ) - (a 0 : ℤ)) - ((a (T + 1) : ℤ) - (a T : ℤ)) := by
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  omega

private lemma greedy_backward_shift_translated_prefix_minimality
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, IsLeast
      {m | a (n + T) < m ∧ ∀ i ≤ n + T, 1 < Nat.gcd m (a i)}
      (a (n + 1) + L) := by
  intro n
  have h := one_lt_gcd (n + T)
  have hv : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ n
  rw [hv] at h
  exact h

private lemma greedy_shift_iterate
    {a : ℕ → ℕ} {T L : ℕ}
    (hshift : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ n, 0 < n → ∀ k, a (n + k * T) = a n + k * L := by
  have hpos : ∀ n, 0 < n → a (n + T) = a n + L := by
    intro n hn
    have h := hshift (n - 1)
    have hn1 : 1 ≤ n := by omega
    simpa [Nat.sub_add_cancel hn1, Nat.add_assoc] using h
  intro n hn k
  induction k with
  | zero => simp
  | succ k ih =>
      have hp := hpos (n + k * T) (by omega)
      calc
        a (n + Nat.succ k * T) = a ((n + k * T) + T) := by
          congr 1
          simp [Nat.succ_mul, Nat.add_assoc]
        _ = a (n + k * T) + L := hp
        _ = a n + k * L + L := by rw [ih]
        _ = a n + Nat.succ k * L := by
          simp [Nat.succ_mul, Nat.add_assoc]

private lemma greedy_backward_shift_shifted_boundary_gcd
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ i, 0 < i → 1 < Nat.gcd (a i + L) (a 0) := by
  intro i hi
  have hi1 : 1 ≤ i := by omega
  have hidx : i - 1 + 1 = i := by omega
  have hshift : a (i + T) = a i + L := by
    have h := hshift_succ (i - 1)
    simpa [Nat.sub_add_cancel hi1, Nat.add_assoc] using h
  have hmem := (one_lt_gcd (i + T - 1)).1
  have hbound : 0 ≤ i + T - 1 := by omega
  have hzero : 0 ≤ i + T - 1 := hbound
  have hterm : a (i + T - 1 + 1) = a i + L := by
    rw [show i + T - 1 + 1 = i + T by omega]
    exact hshift
  rw [hterm] at hmem
  exact hmem.2 0 (by omega)

private lemma research_shift_strictly_positive {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hT : 0 < T) :
    1 < L := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have hmono : ∀ k, a 1 < a (1 + (k + 1)) := by
    intro k
    induction k with
    | zero => simpa using hinc 1
    | succ k ih =>
        have hs := hinc (1 + (k + 1))
        have hs' : a (1 + (k + 1)) < a (1 + (k + 1) + 1) := by
          simpa using hs
        exact lt_trans ih hs'
  obtain ⟨k, hTk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  have hstep : a 1 < a (T + 1) := by
    rw [hTk]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmono k
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  have hLpos : 0 < L := by omega
  have hg := candidate_tail_terms_share_shift_gcd one_lt_gcd hshift_succ hT 0
  have hg' : 1 < Nat.gcd L (a (0 + 1)) := by
    simpa using hg
  have hle : Nat.gcd L (a (0 + 1)) ≤ L :=
    Nat.le_of_dvd hLpos (Nat.gcd_dvd_left L (a (0 + 1)))
  omega

private lemma candidate_boundary_increment_reduces_boundary_with_greedy
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hinc : a (T + 1) - a T = a 1 - a 0) :
    a T = a 0 + L := by
  have hstep := strict_increase_of_greedy_step one_lt_gcd
  have h0 : a 0 ≤ a 1 := Nat.le_of_lt (hstep 0)
  have hT : a T < a (T + 1) := by
    simpa [Nat.add_comm] using hstep T
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  omega

private lemma greedy_backward_shift_upper_endpoint_cut
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hupper : ∀ i ≤ T, 1 < Nat.gcd (a 0 + L) (a i)) :
    a 0 + L ≤ a T := by
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have h01 : a 0 < a 1 := hinc 0
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  by_contra hnot
  have hlt : a T < a 0 + L := by omega
  have hmin := (one_lt_gcd T).2 ⟨hlt, hupper⟩
  rw [hs] at hmin
  omega

private lemma greedy_backward_shift_lower_endpoint_cut
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L)
    (hlower : a 0 + L < a T → 1 < Nat.gcd (a T - L) (a 0)) :
    a T ≤ a 0 + L := by
  by_contra hnot
  have hlt : a 0 + L < a T := by omega
  have hL : L ≤ a T := by
    have ha0 := one_lt 0
    omega
  have hzero : ∀ i ≤ 0, 1 < Nat.gcd (a T - L) (a i) := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    exact hlower hlt
  have hmin := (one_lt_gcd 0).2 ⟨by omega, hzero⟩
  have hmin' := Nat.add_le_add_right hmin L
  rw [Nat.sub_add_cancel hL] at hmin'
  have hinc := strict_increase_of_greedy_step one_lt_gcd
  have hTlt' : a T < a 1 + L := by
    calc
      a T < a (T + 1) := by simpa [Nat.add_comm] using hinc T
      _ = a 1 + L := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  exact (Nat.not_lt_of_ge hmin') hTlt'

private lemma greedy_backward_shift_all_translates_boundary_gcd
    {a : ℕ → ℕ} {T L : ℕ}
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1)))
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    ∀ i, 0 < i → ∀ k, 1 < Nat.gcd (a i + k * L) (a 0) := by
  intro i hi k
  have hiter := greedy_shift_iterate hshift_succ i hi k
  have hmem := (one_lt_gcd (i + k * T - 1)).1.2 0 (by omega)
  have hidx : i + k * T - 1 + 1 = i + k * T := by omega
  rw [hidx] at hmem
  rw [hiter] at hmem
  exact hmem

private lemma greedy_backward_shift_propagation_cross_add_iff
    {a : ℕ → ℕ} {T L : ℕ}
    (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) :
    (∀ n, a (n + T) = a n + L) ↔
      a (T + 1) + a 0 = a 1 + a T := by
  rw [greedy_backward_shift_reduce_to_zero hshift_succ]
  have hs : a (T + 1) = a 1 + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hshift_succ 0
  constructor
  · intro h
    rw [h, hs]
    omega
  · intro h
    omega

private lemma candidate_prime_cover_period
    {x L A k : ℕ} :
    Nat.gcd (x + (k + A) * L) A = Nat.gcd (x + k * L) A := by
  have hmul : ∀ u t : ℕ, Nat.gcd (u + A * t) A = Nat.gcd u A := by
    intro u t
    induction t with
    | zero => simp
    | succ t ih =>
        calc
          Nat.gcd (u + A * Nat.succ t) A = Nat.gcd ((u + A * t) + A) A := by
            congr 1
            simp [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ = Nat.gcd (u + A * t) A := by
            rw [Nat.gcd_add_self_left]
          _ = Nat.gcd u A := ih
  have harg : x + (k + A) * L = (x + k * L) + A * L := by
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  rw [harg]
  exact hmul (x + k * L) L

private lemma candidate_prime_cover_finite_residues
    {x L A : ℕ} (hA : 0 < A)
    (h : ∀ k, k < A → 1 < Nat.gcd (x + k * L) A) :
    ∀ k, 1 < Nat.gcd (x + k * L) A := by
  have hmul : ∀ u t : ℕ, Nat.gcd (u + A * t) A = Nat.gcd u A := by
    intro u t
    induction t with
    | zero => simp
    | succ t ih =>
        calc
          Nat.gcd (u + A * Nat.succ t) A = Nat.gcd ((u + A * t) + A) A := by
            congr 1
            simp [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ = Nat.gcd (u + A * t) A := by
            rw [Nat.gcd_add_self_left]
          _ = Nat.gcd u A := ih
  intro k
  let r := k % A
  let q := k / A
  have hr : r < A := by
    dsimp [r]
    exact Nat.mod_lt k hA
  have hdecomp : r + A * q = k := by
    dsimp [r, q]
    exact Nat.mod_add_div k A
  rw [← hdecomp]
  have harg : x + (r + A * q) * L = (x + r * L) + A * (q * L) := by
    rw [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.add_assoc]
  rw [harg, hmul]
  exact h r hr

private lemma candidate_prime_cover_bridge
    {x L A : ℕ}
    (hforall : ∀ k, 1 < Nat.gcd (x + k * L) A)
    (havoid : Nat.gcd x (Nat.gcd L A) = 1 →
      ∃ k, Nat.gcd (x + k * L) A = 1)
    (hpos : 0 < Nat.gcd x (Nat.gcd L A)) :
    1 < Nat.gcd x (Nat.gcd L A) := by
  have hne : Nat.gcd x (Nat.gcd L A) ≠ 1 := by
    intro hone
    rcases havoid hone with ⟨k, hk⟩
    have h := hforall k
    omega
  omega

private lemma prime_progression_avoidance_delta
    {x L p : ℕ} (hp : Nat.Prime p)
    (h : Nat.gcd x (Nat.gcd L p) = 1) :
    ∃ k, Nat.gcd (x + k * L) p = 1 := by
  by_cases hx : p ∣ x
  · have hL : ¬ p ∣ L := by
      intro hLp
      have hg : p ∣ Nat.gcd x (Nat.gcd L p) :=
        Nat.dvd_gcd hx (Nat.dvd_gcd hLp (dvd_refl p))
      rw [h] at hg
      have hp_le : p ≤ 1 := Nat.le_of_dvd (by omega) hg
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hsum : ¬ p ∣ x + L := by
      intro hs
      have hdiff : p ∣ (x + L) - x := Nat.dvd_sub hs hx
      have hdiff' : p ∣ L := by simpa using hdiff
      exact hL hdiff'
    have hc : Nat.Coprime p (x + L) :=
      (hp.coprime_iff_not_dvd).2 hsum
    exact ⟨1, by simpa using hc.symm⟩
  · have hc : Nat.Coprime p x :=
      (hp.coprime_iff_not_dvd).2 hx
    exact ⟨0, by simpa using hc.symm⟩

private lemma proposed_backward_gcd_at_predecessor
    {a : ℕ → ℕ} {T L : ℕ}
    (hT : 0 < T)
    (hA : 0 < a 0)
    (hL : L ≤ a T)
    (hglobal : ∀ i, 0 < i → ∀ k, 1 < Nat.gcd (a i + k * L) (a 0)) :
    1 < Nat.gcd (a T - L) (a 0) := by
  have h := hglobal T hT (a 0 - 1)
  have hrewrite : (a T - L) + a 0 * L = a T + (a 0 - 1) * L := by
    calc
      (a T - L) + a 0 * L = (a T - L) + ((a 0 - 1) * L + L) := by
        rw [show a 0 = (a 0 - 1) + 1 by omega, Nat.add_mul]
        simp
      _ = ((a T - L) + L) + (a 0 - 1) * L := by ac_rfl
      _ = a T + (a 0 - 1) * L := by rw [Nat.sub_add_cancel hL]
  rw [← hrewrite] at h
  have hperiod := candidate_prime_cover_period (x := a T - L) (L := L) (A := a 0) (k := 0)
  have hperiod' : Nat.gcd ((a T - L) + a 0 * L) (a 0) = Nat.gcd (a T - L) (a 0) := by
    simpa using hperiod
  rw [hperiod'] at h
  exact h

private lemma positive_coprime_translate
    {x L A : ℕ} (hA : 0 < A)
    (h : Nat.gcd x (Nat.gcd L A) = 1) :
    ∃ k, Nat.gcd (x + k * L) A = 1 := by
  classical
  let Q : ℕ := Finset.prod A.primeFactors (fun p => if p ∣ x then 1 else p)
  have hprime : ∀ p ∈ A.primeFactors, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hprod : ∀ (p : ℕ), Nat.Prime p → p ∣ x → ∀ (s : Finset ℕ),
      (∀ q ∈ s, Nat.Prime q) →
      ¬ p ∣ Finset.prod s (fun q => if q ∣ x then 1 else q) := by
    intro p hp hpx s
    induction s using Finset.induction_on with
    | empty =>
        intro hs
        simpa using hp.ne_one
    | @insert q s hqs ih =>
        intro hs
        have hqprime : Nat.Prime q := hs q (Finset.mem_insert_self q s)
        have hs' : ∀ r ∈ s, Nat.Prime r := by
          intro r hr
          exact hs r (Finset.mem_insert_of_mem hr)
        by_cases hqx : q ∣ x
        · simpa [Finset.prod_insert hqs, hqx] using ih hs'
        · simp only [Finset.prod_insert hqs, hqx, ↓reduceIte]
          intro hpq
          rcases (Nat.Prime.dvd_mul hp).mp hpq with hpqdiv | hps
          · have hpq' : p = q := by
              rcases (Nat.dvd_prime hqprime).mp hpqdiv with hpone | hpeq
              · exact False.elim (hp.ne_one hpone)
              · exact hpeq
            exact hqx (by simpa [← hpq'] using hpx)
          · exact ih hs' hps
  refine ⟨Q, ?_⟩
  by_contra hne
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hne
  have hpA : p ∣ A := dvd_trans hpdiv (Nat.gcd_dvd_right _ _)
  have hpxy : p ∣ x + Q * L := dvd_trans hpdiv (Nat.gcd_dvd_left _ _)
  by_cases hpx : p ∣ x
  · have hpL : ¬ p ∣ L := by
      intro hpL
      have hpg : p ∣ Nat.gcd x (Nat.gcd L A) :=
        Nat.dvd_gcd hpx (Nat.dvd_gcd hpL hpA)
      rw [h] at hpg
      have hp1 : p = 1 := Nat.dvd_one.mp hpg
      exact hp.ne_one hp1
    have hpQ : ¬ p ∣ Q := by
      dsimp [Q]
      exact hprod p hp hpx A.primeFactors hprime
    have hpQL : p ∣ Q * L := by
      have hd : p ∣ (x + Q * L) - x := Nat.dvd_sub hpxy hpx
      simpa using hd
    rcases hp.dvd_mul.mp hpQL with hpQ' | hpL'
    · exact hpQ hpQ'
    · exact hpL hpL'
  · have hpmem : p ∈ A.primeFactors := hp.mem_primeFactors hpA hA.ne'
    have hpQ : p ∣ Q := by
      dsimp [Q]
      simpa [hpx] using
        (Finset.dvd_prod_of_mem (fun q => if q ∣ x then 1 else q) hpmem)
    have hpQL : p ∣ Q * L := dvd_mul_of_dvd_left hpQ L
    have hdiff : p ∣ (x + Q * L) - Q * L := Nat.dvd_sub hpxy hpQL
    exact hpx (by simpa using hdiff)

private lemma greedy_backward_shift_propagation {a : ℕ → ℕ} {T L : ℕ} (one_lt : ∀ i, 1 < a i) (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) (hshift_succ : ∀ n, a (n + 1 + T) = a (n + 1) + L) : ∀ n, a (n + T) = a n + L := by
  intro n
  by_cases hn : 0 < n
  · exact greedy_backward_shift_succ_index hshift_succ n hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hTzero : T = 0 → L = 0 := by
      intro hT
      subst T
      have h := hshift_succ 0
      simp at h
      omega
    by_cases hT : T = 0
    · have hL := hTzero hT
      subst T
      simp [hL]
    · have hTpos : 0 < T := by omega
      have hboundary : a T = a 0 + L := by
        by_contra hneq
        rcases greedy_backward_shift_boundary_dichotomy one_lt one_lt_gcd hshift_succ hneq with hlow | hhigh
        · rcases hlow with ⟨hlt, ⟨i, hiT, hcop⟩⟩
          have hglobal := greedy_backward_shift_all_translates_boundary_gcd one_lt_gcd hshift_succ
          by_cases hi : i = 0
          · subst i
            have hD : Nat.gcd L (a 0) = 1 := by
              apply Nat.dvd_one.mp
              have hdadd : Nat.gcd L (a 0) ∣ a 0 + L := by
                exact Nat.dvd_add (Nat.gcd_dvd_right L (a 0)) (Nat.gcd_dvd_left L (a 0))
              have hdg : Nat.gcd L (a 0) ∣ Nat.gcd (a 0 + L) (a 0) := by
                exact Nat.dvd_gcd hdadd (Nat.gcd_dvd_right L (a 0))
              rw [hcop] at hdg
              exact hdg
            have haux : Nat.gcd (a 1) (Nat.gcd L (a 0)) = 1 := by
              rw [hD]
              simp
            obtain ⟨k, hk⟩ := positive_coprime_translate (x := a 1) (L := L) (A := a 0)
              (by have ha0 := one_lt 0; omega) haux
            have hb := hglobal 1 (by omega) k
            rw [hk] at hb
            omega
          · have hi0 : 0 < i := by omega
            have haux : Nat.gcd (a i) (Nat.gcd L (a 0)) = 1 := by
              apply Nat.dvd_one.mp
              have hdL : Nat.gcd (a i) (Nat.gcd L (a 0)) ∣ L := by
                exact dvd_trans (Nat.gcd_dvd_right (a i) (Nat.gcd L (a 0)))
                  (Nat.gcd_dvd_left L (a 0))
              have hd0 : Nat.gcd (a i) (Nat.gcd L (a 0)) ∣ a 0 := by
                exact dvd_trans (Nat.gcd_dvd_right (a i) (Nat.gcd L (a 0)))
                  (Nat.gcd_dvd_right L (a 0))
              have hdadd : Nat.gcd (a i) (Nat.gcd L (a 0)) ∣ a 0 + L :=
                Nat.dvd_add hd0 hdL
              have hdai : Nat.gcd (a i) (Nat.gcd L (a 0)) ∣ a i :=
                Nat.gcd_dvd_left (a i) (Nat.gcd L (a 0))
              have hdg : Nat.gcd (a i) (Nat.gcd L (a 0)) ∣ Nat.gcd (a 0 + L) (a i) :=
                Nat.dvd_gcd hdadd hdai
              rw [hcop] at hdg
              exact hdg
            obtain ⟨k, hk⟩ := positive_coprime_translate (x := a i) (L := L) (A := a 0)
              (by have ha0 := one_lt 0; omega) haux
            have hb := hglobal i hi0 k
            rw [hk] at hb
            omega
        · rcases hhigh with ⟨hgt, hcop⟩
          have hL : L ≤ a T := by
            have ha0 := one_lt 0
            omega
          have hD : Nat.gcd (a T - L) (Nat.gcd L (a 0)) = 1 := by
            apply Nat.dvd_one.mp
            have hd0 : Nat.gcd (a T - L) (Nat.gcd L (a 0)) ∣ a 0 := by
              exact dvd_trans (Nat.gcd_dvd_right (a T - L) (Nat.gcd L (a 0)))
                (Nat.gcd_dvd_right L (a 0))
            have hdx : Nat.gcd (a T - L) (Nat.gcd L (a 0)) ∣ a T - L :=
              Nat.gcd_dvd_left (a T - L) (Nat.gcd L (a 0))
            have hdg : Nat.gcd (a T - L) (Nat.gcd L (a 0)) ∣ Nat.gcd (a T - L) (a 0) :=
              Nat.dvd_gcd hdx hd0
            rw [hcop] at hdg
            exact hdg
          have hDplus : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) = 1 := by
            apply Nat.dvd_one.mp
            have hd0 : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) ∣ a 0 := by
              exact dvd_trans (Nat.gcd_dvd_right ((a T - L) + L) (Nat.gcd L (a 0)))
                (Nat.gcd_dvd_right L (a 0))
            have hdD : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) ∣ Nat.gcd L (a 0) :=
              Nat.gcd_dvd_right ((a T - L) + L) (Nat.gcd L (a 0))
            have hdL : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) ∣ L := by
              exact dvd_trans hdD (Nat.gcd_dvd_left L (a 0))
            have hdxL : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) ∣ a T - L := by
              have hsub := Nat.dvd_sub
                (Nat.gcd_dvd_left ((a T - L) + L) (Nat.gcd L (a 0))) hdL
              simpa using hsub
            have hdg : Nat.gcd ((a T - L) + L) (Nat.gcd L (a 0)) ∣ Nat.gcd (a T - L) (Nat.gcd L (a 0)) :=
              Nat.dvd_gcd hdxL hdD
            rw [hD] at hdg
            exact hdg
          obtain ⟨k, hk⟩ := positive_coprime_translate (x := (a T - L) + L) (L := L) (A := a 0)
            (by have ha0 := one_lt 0; omega) hDplus
          have hglobalT := greedy_backward_shift_all_translates_boundary_gcd one_lt_gcd hshift_succ
          have hb := hglobalT T hTpos k
          have hk' : Nat.gcd (a T + k * L) (a 0) = 1 := by
            simpa [Nat.sub_add_cancel hL, Nat.add_assoc] using hk
          rw [hk'] at hb
          omega
      simpa using hboundary

private lemma positive_increment_of_global_shift {a : ℕ → ℕ} {T L : ℕ}
    (hinc : ∀ n, a n < a (n + 1))
    (hT : 0 < T)
    (hshift : ∀ n, a (n + T) = a n + L) :
    0 < L := by
  have hlong : ∀ n k, a n < a (n + k + 1) := by
    intro n k
    induction k with
    | zero =>
        simpa using hinc n
    | succ k ih =>
        have hnext : a (n + k + 1) < a (n + Nat.succ k + 1) := by
          have harg : (n + k + 1) + 1 = n + Nat.succ k + 1 := by omega
          rw [← harg]
          exact hinc (n + k + 1)
        exact ih.trans hnext
  cases T with
  | zero => omega
  | succ k =>
      have hlt : a 0 < a (Nat.succ k) := by
        have harg : 0 + k + 1 = Nat.succ k := by omega
        rw [← harg]
        exact hlong 0 k
      have hs : a (Nat.succ k) = a 0 + L := by
        simpa only [Nat.zero_add] using hshift 0
      omega

private lemma audit_target_zero_threshold {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, 0 ≤ n → a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  intro n
  exact hevent n (by omega)

private lemma audit_greedy_backward_affine_upper_bound_false :
    ∃ (a : ℕ → ℕ),
      (∀ i, 1 < a i) ∧
      (∀ n, IsLeast
        {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) ∧
      ¬ (∀ n, a (n + 1 + 1) = a (n + 1) + 2 →
        a (n + 1) ≤ a n + 2) := by
  rcases greedy_infinite_model with ⟨a, hone, hgreedy, ha0⟩
  obtain ⟨ha1, ha2, ha3⟩ := greedy_prefix_values hgreedy ha0
  refine ⟨a, hone, hgreedy, ?_⟩
  intro h
  have h0 := h 0
  norm_num [ha0, ha1, ha2] at h0

private lemma audit_exact_greedy_backward_affine_upper_bound_negation :
    ¬ (∀ {a : ℕ → ℕ},
      (∀ i, 1 < a i) →
      (∀ n, IsLeast
        {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
        (a (n + 1))) →
      ∀ {T L : ℕ}, 0 < T → 0 < L →
        ∀ n, a (n + 1 + T) = a (n + 1) + L →
          a (n + T) ≤ a n + L) := by
  intro h
  rcases greedy_infinite_model with ⟨a, hone, hgreedy, ha0⟩
  obtain ⟨ha1, ha2, ha3⟩ := greedy_prefix_values hgreedy ha0
  have hu := h hone hgreedy (T := 1) (L := 2) (by omega) (by omega)
  have h0 := hu 0
  norm_num [ha0, ha1, ha2] at h0

private lemma eventual_affine_residue_offset
    {a : ℕ → ℕ} {N T L : ℕ}
    (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ r, ∃ k0 x, ∀ k, k0 ≤ k →
      a (r + k * T) = x + (k - k0) * L := by
  intro r
  refine ⟨N, a (r + N * T), ?_⟩
  intro k hk
  have hiter : ∀ d : ℕ,
      a (r + (N + d) * T) = a (r + N * T) + d * L := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hmul : N ≤ (N + d) * T := by
          have hT1 : 1 ≤ T := by omega
          have hN : N ≤ N * T := by
            simpa using (Nat.mul_le_mul_left N hT1)
          have hNd : N * T ≤ (N + d) * T := by
            exact Nat.mul_le_mul_right T (Nat.le_add_right N d)
          omega
        have hidx : N ≤ r + (N + d) * T := by omega
        have he := hevent (r + (N + d) * T) hidx
        have harg : r + (N + Nat.succ d) * T =
            (r + (N + d) * T) + T := by
          simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm]
        rw [harg, he, ih]
        simp [Nat.succ_mul, Nat.add_assoc]
  have hkd : k = N + (k - N) := by omega
  rw [hkd]
  simpa using hiter (k - N)

private lemma eventual_affine_iterate_from_threshold
    {a : ℕ → ℕ} {N T L : ℕ}
    (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i, N ≤ i → ∀ k, a (i + k * T) = a i + k * L := by
  intro i hi k
  induction k with
  | zero => simp
  | succ k ih =>
      have hidx : N ≤ i + k * T := by omega
      have he := hevent (i + k * T) hidx
      have harg : i + (Nat.succ k) * T = (i + k * T) + T := by
        simp [Nat.succ_eq_add_one, Nat.add_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      rw [harg, he, ih]
      simp [Nat.succ_mul, Nat.add_assoc]

private lemma eventual_affine_common_shift_gcd
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i, 1 < Nat.gcd L (a i) := by
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  intro i
  have hi : 0 < a i := by
    have h := one_lt i
    omega
  obtain ⟨k0, x, hx⟩ := eventual_affine_residue_offset hT hevent i
  by_contra hnot
  have hDpos : 0 < Nat.gcd L (a i) := by
    apply Nat.gcd_pos_of_pos_left
    omega
  have hD : Nat.gcd L (a i) = 1 := by omega
  have hcop : Nat.gcd (x + L) (Nat.gcd L (a i)) = 1 := by
    simp [hD]
  obtain ⟨q, hq⟩ := positive_coprime_translate (x := x + L) (L := L) (A := a i)
    hi hcop
  have hprog : ∀ q, a (i + (k0 + 1 + q) * T) = (x + L) + q * L := by
    intro q
    have h := hx (k0 + 1 + q) (by omega)
    have hsub : k0 + 1 + q - k0 = 1 + q := by omega
    rw [hsub] at h
    calc
      a (i + (k0 + 1 + q) * T) = x + (1 + q) * L := by simpa using h
      _ = (x + L) + q * L := by
        rw [Nat.add_mul]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hidx : i < i + (k0 + 1 + q) * T := by
    have hkpos : 0 < k0 + 1 + q := by omega
    have hmul : 0 < (k0 + 1 + q) * T := Nat.mul_pos hkpos hT
    omega
  have hp := hpair i (i + (k0 + 1 + q) * T) hidx
  rw [hprog q] at hp
  omega

private lemma tail_prime_support_of_all_gcd
    {A x L : ℕ} (hA : 0 < A)
    (hall : ∀ k, 1 < Nat.gcd (x + k * L) A) :
    ∃ p, Nat.Prime p ∧ p ∣ A ∧ p ∣ L ∧ p ∣ x := by
  have hbad : Nat.gcd x (Nat.gcd L A) ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := positive_coprime_translate (x := x) (L := L) (A := A) hA h
    have hh := hall k
    rw [hk] at hh
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hbad
  have hpxg : p ∣ Nat.gcd L A := dvd_trans hpd (Nat.gcd_dvd_right x (Nat.gcd L A))
  have hpA : p ∣ A := dvd_trans hpxg (Nat.gcd_dvd_right L A)
  have hpL : p ∣ L := dvd_trans hpxg (Nat.gcd_dvd_left L A)
  have hpx : p ∣ x := dvd_trans hpd (Nat.gcd_dvd_left x (Nat.gcd L A))
  exact ⟨p, hp, hpA, hpL, hpx⟩

private lemma candidate_shift_admissible_of_common_prime
    {a : ℕ → ℕ} {n L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (hcoh : ∀ i ≤ n, ∃ p, p.Prime ∧ p ∣ L ∧ p ∣ a i ∧ p ∣ a n) :
    ∀ i ≤ n, 1 < Nat.gcd (a n + L) (a i) := by
  intro i hi
  obtain ⟨p, hp, hpL, hpi, hpn⟩ := hcoh i hi
  have hpadd : p ∣ a n + L := Nat.dvd_add hpn hpL
  have hpg : p ∣ Nat.gcd (a n + L) (a i) := Nat.dvd_gcd hpadd hpi
  have hgpos : 0 < Nat.gcd (a n + L) (a i) := by
    apply Nat.gcd_pos_of_pos_left
    have hn := one_lt n
    omega
  exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)

private lemma common_difference_pairwise_gcd
    {x y L : ℕ} (hx : 0 < x) (hxy : x < y) (hL : 0 < L)
    (hforall : ∀ k, 1 < Nat.gcd (x + k * L) (y + k * L)) :
    1 < Nat.gcd x (Nat.gcd L (y - x)) := by
  have hA : 0 < y - x := by omega
  have hDpos : 0 < Nat.gcd L (y - x) := by
    apply Nat.gcd_pos_of_pos_left
    exact hL
  have hpos : 0 < Nat.gcd x (Nat.gcd L (y - x)) := by
    apply Nat.gcd_pos_of_pos_left
    exact hx
  by_contra hnot
  have hD : Nat.gcd x (Nat.gcd L (y - x)) = 1 := by omega
  obtain ⟨k, hk⟩ := positive_coprime_translate (x := x) (L := L) (A := y - x)
    hA hD
  have hd : Nat.gcd (x + k * L) (y + k * L) ∣ y - x := by
    have hsub := Nat.dvd_sub
      (Nat.gcd_dvd_right (x + k * L) (y + k * L))
      (Nat.gcd_dvd_left (x + k * L) (y + k * L))
    have harg : (y + k * L) - (x + k * L) = y - x := by omega
    rw [harg] at hsub
    exact hsub
  have hdg : Nat.gcd (x + k * L) (y + k * L) ∣
      Nat.gcd (x + k * L) (y - x) := by
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hd
  rw [hk] at hdg
  have hone : Nat.gcd (x + k * L) (y + k * L) = 1 := Nat.dvd_one.mp hdg
  have hbad := hforall k
  omega

private lemma greedy_tail_upper_bound
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    a (n + T) ≤ a n + L := by
  have hstrict : ∀ k, a k < a (k + 1) := by
    intro k
    exact (one_lt_gcd k).1.1
  have hiter : ∀ k, a (n + T + k * T) = a (n + T) + k * L := by
    intro k
    have hi : n + 1 ≤ n + T := by omega
    have hh := eventual_affine_iterate_from_threshold
      (a := a) (N := n + 1) (T := T) (L := L) hT htail
      (n + T) hi k
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  have hall : ∀ i ≤ n, ∀ k, 1 < Nat.gcd (a (n + T) + k * L) (a i) := by
    intro i hi k
    have hj : i < n + T + k * T := by omega
    have hp := pairwise_gcd_of_greedy_step one_lt_gcd
      i (n + T + k * T) hj
    rw [hiter k] at hp
    exact hp
  by_contra hnot
  have hbad : a n + L < a (n + T) := by omega
  have hmem : a (n + T) - L ∈
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} := by
    constructor
    · omega
    · intro i hi
      obtain ⟨p, hp, hpi, hpL, hpx⟩ := tail_prime_support_of_all_gcd
        (A := a i) (x := a (n + T)) (L := L) (by
          have hh := one_lt i
          omega) (hall i hi)
      have hsub : p ∣ a (n + T) - L := by
        exact Nat.dvd_sub hpx hpL
      have hpg : p ∣ Nat.gcd (a (n + T) - L) (a i) :=
        Nat.dvd_gcd hsub hpi
      have hgpos : 0 < Nat.gcd (a (n + T) - L) (a i) := by
        apply Nat.gcd_pos_of_pos_left
        have hh := one_lt i
        omega
      exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)
  have hle := (one_lt_gcd n).2 hmem
  have hnext := htail (n + 1) (by omega)
  have hxc : a (n + T) < a (n + 1) + L := by
    calc
      a (n + T) < a (n + T + 1) := hstrict (n + T)
      _ = a (n + 1) + L := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext
  omega

private lemma backward_shift_step {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (n : ℕ)
    (hshift : ∀ k, a (k + 1 + T) = a (k + 1) + L) :
    a (n + T) = a n + L := by
  have hglobal := greedy_backward_shift_propagation one_lt one_lt_gcd hshift
  exact hglobal n

private lemma common_difference_pairwise_gcd_eventual
    {x y L K : ℕ} (hx : 0 < x) (hxy : x < y) (hL : 0 < L)
    (hforall : ∀ k, K ≤ k → 1 < Nat.gcd (x + k * L) (y + k * L)) :
    1 < Nat.gcd x (Nat.gcd L (y - x)) := by
  have hA : 0 < y - x := by omega
  have hDpos : 0 < Nat.gcd L (y - x) := by
    apply Nat.gcd_pos_of_pos_left
    exact hL
  have hpos : 0 < Nat.gcd x (Nat.gcd L (y - x)) := by
    apply Nat.gcd_pos_of_pos_left
    exact hx
  by_contra hnot
  have hD : Nat.gcd x (Nat.gcd L (y - x)) = 1 := by omega
  have hshiftcop : Nat.gcd (x + K * L) (Nat.gcd L (y - x)) = 1 := by
    apply Nat.dvd_one.mp
    have hgD : Nat.gcd (x + K * L) (Nat.gcd L (y - x)) ∣
        Nat.gcd L (y - x) := Nat.gcd_dvd_right _ _
    have hgL : Nat.gcd (x + K * L) (Nat.gcd L (y - x)) ∣ L :=
      dvd_trans hgD (Nat.gcd_dvd_left L (y - x))
    have hgKL : Nat.gcd (x + K * L) (Nat.gcd L (y - x)) ∣ K * L :=
      dvd_mul_of_dvd_right hgL K
    have hgx : Nat.gcd (x + K * L) (Nat.gcd L (y - x)) ∣ x := by
      have hsub := Nat.dvd_sub
        (Nat.gcd_dvd_left (x + K * L) (Nat.gcd L (y - x))) hgKL
      simpa using hsub
    have hg := Nat.dvd_gcd hgx hgD
    rw [hD] at hg
    exact hg
  obtain ⟨q, hq⟩ := positive_coprime_translate
    (x := x + K * L) (L := L) (A := y - x) hA hshiftcop
  have hq' : Nat.gcd (x + (K + q) * L) (y - x) = 1 := by
    simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
  have hbad := hforall (K + q) (by omega)
  have hd : Nat.gcd (x + (K + q) * L) (y + (K + q) * L) ∣ y - x := by
    have hsub := Nat.dvd_sub
      (Nat.gcd_dvd_right (x + (K + q) * L) (y + (K + q) * L))
      (Nat.gcd_dvd_left (x + (K + q) * L) (y + (K + q) * L))
    have harg : (y + (K + q) * L) - (x + (K + q) * L) = y - x := by omega
    rw [harg] at hsub
    exact hsub
  have hdg : Nat.gcd (x + (K + q) * L) (y + (K + q) * L) ∣
      Nat.gcd (x + (K + q) * L) (y - x) := by
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) hd
  rw [hq'] at hdg
  have hone : Nat.gcd (x + (K + q) * L) (y + (K + q) * L) = 1 :=
    Nat.dvd_one.mp hdg
  omega

private lemma eventual_boundary_upper_bound_candidate
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hN : 0 < N) (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    a (N - 1 + T) ≤ a (N - 1) + L := by
  apply greedy_tail_upper_bound one_lt one_lt_gcd hT hL
  intro k hk
  exact hevent k (by omega)

private lemma globalize_from_tail_backstep
    {a : ℕ → ℕ} {N T L : ℕ}
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (htail_back : ∀ n,
      (∀ k, n + 1 ≤ k → a (k + T) = a k + L) →
        a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  have hQ : ∀ q, q ≤ N →
      (∀ r, q ≤ r → a (r + T) = a r + L) := by
    intro q hq
    exact Nat.decreasingInduction' (P := fun q =>
      ∀ r, q ≤ r → a (r + T) = a r + L) (m := q) (n := N)
      (fun k hk hkn ih => by
        intro r hr
        by_cases hkr : r = k
        · subst r
          apply htail_back k
          exact ih
        · have hk1 : k + 1 ≤ r := by omega
          exact ih r hk1)
      hq (by
        intro r hr
        exact hevent r (by omega))
  intro n
  exact hQ 0 (Nat.zero_le N) n (Nat.zero_le n)

private lemma eventual_affine_residue_common_prime
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ r, ∃ k0 x p, 0 < k0 ∧ Nat.Prime p ∧ p ∣ a 0 ∧ p ∣ L ∧ p ∣ x ∧
      a (r + k0 * T) = x ∧
      ∀ k, k0 ≤ k → a (r + k * T) = x + (k - k0) * L := by
  intro r
  obtain ⟨kbase, xbase, hbase⟩ := eventual_affine_residue_offset hT hevent r
  let k0 := kbase + 1
  have hk0pos : 0 < k0 := by
    dsimp [k0]
    omega
  have hbase_k0 : a (r + k0 * T) = xbase + (k0 - kbase) * L := by
    apply hbase
    dsimp [k0]
    omega
  have hk0sub : k0 - kbase = 1 := by
    dsimp [k0]
    omega
  have hx0 : a (r + k0 * T) = xbase + L := by
    rw [hbase_k0, hk0sub]
    simp
  let x := xbase + L
  have htail : ∀ k, k0 ≤ k →
      a (r + k * T) = x + (k - k0) * L := by
    intro k hk
    have hraw := hbase k (by dsimp [k0] at hk ⊢; omega)
    have hsub : k - kbase = (k - k0) + 1 := by
      dsimp [k0]
      omega
    rw [hraw, hsub]
    dsimp [x]
    simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hxval : a (r + k0 * T) = x := by
    simpa [x] using hx0
  have hnot : Nat.gcd x (Nat.gcd L (a 0)) ≠ 1 := by
    intro hcop
    obtain ⟨q, hq⟩ := positive_coprime_translate (x := x) (L := L) (A := a 0)
      (by have ha0 := one_lt 0; omega) hcop
    have htailq := htail (k0 + q) (by omega)
    have hprod : 0 < k0 * T := Nat.mul_pos hk0pos hT
    have hidx : 0 < r + (k0 + q) * T := by
      have hmul : k0 * T ≤ (k0 + q) * T :=
        Nat.mul_le_mul_right T (Nat.le_add_right k0 q)
      omega
    have hgood : 1 < Nat.gcd (a (r + (k0 + q) * T)) (a 0) := by
      have hmem := (one_lt_gcd (r + (k0 + q) * T - 1)).1.2 0 (by omega)
      have harg : r + (k0 + q) * T - 1 + 1 = r + (k0 + q) * T := by omega
      rw [harg] at hmem
      exact hmem
    have hsubq : k0 + q - k0 = q := by omega
    rw [hsubq] at htailq
    rw [htailq, hq] at hgood
    omega
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hnot
  have hpx : p ∣ x := dvd_trans hpdiv (Nat.gcd_dvd_left x (Nat.gcd L (a 0)))
  have hpD : p ∣ Nat.gcd L (a 0) :=
    dvd_trans hpdiv (Nat.gcd_dvd_right x (Nat.gcd L (a 0)))
  have hpL : p ∣ L := dvd_trans hpD (Nat.gcd_dvd_left L (a 0))
  have hpA : p ∣ a 0 := dvd_trans hpD (Nat.gcd_dvd_right L (a 0))
  exact ⟨k0, x, p, hk0pos, hp, hpA, hpL, hpx, hxval, htail⟩

private lemma affine_of_global_increment_period
    {a d : ℕ → ℕ} {N T L : ℕ}
    (hT : 0 < T)
    (hstep : ∀ n, a (n + 1) = a n + d n)
    (hper : ∀ n, d (n + T) = d n)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  have hprev : ∀ n,
      a (n + 1 + T) = a (n + 1) + L →
        a (n + T) = a n + L := by
    intro n hnext
    apply Nat.add_right_cancel
    calc
      a (n + T) + d n = a (n + T) + d (n + T) := by rw [hper n]
      _ = a (n + T + 1) := by
        rw [hstep (n + T)]
      _ = a (n + 1 + T) := by congr 1 <;> omega
      _ = a (n + 1) + L := hnext
      _ = (a n + d n) + L := by rw [hstep n]
      _ = (a n + L) + d n := by omega
  have hQ : ∀ q, q ≤ N →
      (∀ r, q ≤ r → a (r + T) = a r + L) := by
    intro q hq
    exact Nat.decreasingInduction' (P := fun q =>
      ∀ r, q ≤ r → a (r + T) = a r + L) (m := q) (n := N)
      (fun k hk hkn ih => by
        intro r hr
        by_cases hkr : r = k
        · subst r
          apply hprev k
          exact ih (k + 1) (by omega)
        · have hk1 : k + 1 ≤ r := by omega
          exact ih r hk1)
      hq (by
        intro r hr
        exact hevent r hr)
  intro n
  exact hQ 0 (Nat.zero_le N) n (Nat.zero_le n)

private lemma eventual_residue_offset_common_prime_all
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ r i, ∃ k0 x p, Nat.Prime p ∧ p ∣ a i ∧ p ∣ L ∧ p ∣ x ∧
      ∀ k, k0 ≤ k → a (r + k * T) = x + (k - k0) * L := by
  intro r i
  obtain ⟨k0, x, hx⟩ := eventual_affine_residue_offset hT hevent r
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  have hall : ∀ q, 1 < Nat.gcd (x + (i + 1) * L + q * L) (a i) := by
    intro q
    have hval0 := hx (k0 + (i + 1) + q) (by omega)
    have hsub : k0 + (i + 1) + q - k0 = (i + 1) + q := by omega
    have hval : a (r + (k0 + (i + 1) + q) * T) =
        x + (i + 1) * L + q * L := by
      calc
        a (r + (k0 + (i + 1) + q) * T) =
            x + (k0 + (i + 1) + q - k0) * L := hval0
        _ = x + ((i + 1) + q) * L := by rw [hsub]
        _ = x + (i + 1) * L + q * L := by
          rw [Nat.add_mul]
          simp [Nat.add_assoc]
    have hidx : i < r + (k0 + (i + 1) + q) * T := by
      have hT1 : 1 ≤ T := by omega
      have hmul0 : i + 1 ≤ (i + 1) * T := by
        have hh := Nat.mul_le_mul_left (i + 1) hT1
        simpa only [Nat.mul_one] using hh
      have hmul1 : (i + 1) * T ≤ (k0 + (i + 1) + q) * T := by
        exact Nat.mul_le_mul_right T (by omega)
      have hmul : i + 1 ≤ (k0 + (i + 1) + q) * T := le_trans hmul0 hmul1
      omega
    have hp := hpair i (r + (k0 + (i + 1) + q) * T) hidx
    rw [hval] at hp
    exact hp
  have hai : 0 < a i := by
    have hi := one_lt i
    omega
  obtain ⟨p, hp, hpa, hpL, hpx'⟩ :=
    tail_prime_support_of_all_gcd (A := a i)
      (x := x + (i + 1) * L) (L := L) hai hall
  have hpKL : p ∣ (i + 1) * L := dvd_mul_of_dvd_right hpL (i + 1)
  have hsub : p ∣ (x + (i + 1) * L) - (i + 1) * L :=
    Nat.dvd_sub hpx' hpKL
  have hpx : p ∣ x := by
    simpa using hsub
  exact ⟨k0, x, p, hp, hpa, hpL, hpx, hx⟩

private lemma boundary_defect_prime_support_research
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hshift : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    ∀ i, i ≤ n → ∃ p, Nat.Prime p ∧ p ∣ a i ∧ p ∣ L ∧
      p ∣ (a (n + T) - L) := by
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  have hiter : ∀ k, a (n + T + k * T) = a (n + T) + k * L := by
    intro k
    have hh := eventual_affine_iterate_from_threshold
      (a := a) (N := n + 1) (T := T) (L := L) hT hshift
      (n + T) (by omega) k
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  intro i hi
  have hall : ∀ k, 1 < Nat.gcd (a (n + T) + k * L) (a i) := by
    intro k
    have hidx : i < n + T + k * T := by
      have hpos : 0 < T := hT
      omega
    have hp := hpair i (n + T + k * T) hidx
    rw [hiter k] at hp
    exact hp
  obtain ⟨p, hp, hpi, hpL, hpb⟩ := tail_prime_support_of_all_gcd
    (A := a i) (x := a (n + T)) (L := L)
    (by have hi' := one_lt i; omega) hall
  have hpd : p ∣ a (n + T) - L := by
    exact Nat.dvd_sub hpb hpL
  exact ⟨p, hp, hpi, hpL, hpd⟩

private lemma greedy_common_gcd_value_or_small
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n d : ℕ}
    (hdle : d ≤ a n)
    (hall : ∀ i, i ≤ n → 1 < Nat.gcd d (a i)) :
    d ≤ a 0 ∨ ∃ j, j ≤ n ∧ d = a j := by
  induction n with
  | zero =>
      left
      exact hdle
  | succ n ih =>
      by_cases hdn : d ≤ a n
      · rcases ih hdn (fun i hi => hall i (by omega)) with hsmall | ⟨j, hj, hjeq⟩
        · exact Or.inl hsmall
        · exact Or.inr ⟨j, le_trans hj (Nat.le_succ n), hjeq⟩
      · right
        have hlt : a n < d := by omega
        have hmem : d ∈
            {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} := by
          constructor
          · exact hlt
          · intro i hi
            exact hall i (by omega)
        have hle := (one_lt_gcd n).2 hmem
        have heq : d = a (n + 1) := by omega
        exact ⟨n + 1, le_rfl, heq⟩

private lemma affine_boundary_iff_increment_period
    {a : ℕ → ℕ} {n T L : ℕ}
    (hstrict : ∀ i, a i < a (i + 1))
    (hnext : a (n + T + 1) = a (n + 1) + L) :
    a (n + T) = a n + L ↔
      a (n + T + 1) - a (n + T) = a (n + 1) - a n := by
  have hleft : a n ≤ a (n + 1) := Nat.le_of_lt (hstrict n)
  have hright : a (n + T) ≤ a (n + T + 1) := by
    exact Nat.le_of_lt (hstrict (n + T))
  constructor
  · intro h
    rw [hnext, h]
    omega
  · intro h
    rw [hnext] at h
    omega

private lemma globalize_from_global_increment_period
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (hinc : ∀ n,
      a (n + T + 1) - a (n + T) = a (n + 1) - a n) :
    ∀ n, a (n + T) = a n + L := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hmono : ∀ i d, a i ≤ a (i + d) := by
    intro i d
    induction d with
    | zero => simp
    | succ d ih =>
        have hs := hstrict (i + d)
        have harg : i + Nat.succ d = (i + d) + 1 := by omega
        rw [harg]
        omega
  have hstep : ∀ n,
      a (n + T) - a n = a (n + T + 1) - a (n + 1) := by
    intro n
    have hh := hinc n
    have h0 := hstrict n
    have h1 := hstrict (n + T)
    have h2 := hmono n T
    omega
  have hQ : ∀ q, q ≤ N → a (q + T) - a q = L := by
    intro q hq
    exact Nat.decreasingInduction' (P := fun q => a (q + T) - a q = L)
      (m := q) (n := N)
      (fun k hk hkn ih => by
        rw [hstep k]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih)
      hq (by
        have hN := hevent N (le_rfl)
        have hmonoN := hmono N T
        omega)
  intro n
  by_cases hn : N ≤ n
  · exact hevent n hn
  · have hqn : n ≤ N := by omega
    have hd := hQ n hqn
    have hmono_n := hmono n T
    omega

private lemma eventual_increment_period_of_eventual_affine
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ}
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ n, N ≤ n →
      a (n + T + 1) - a (n + T) = a (n + 1) - a n := by
  intro n hn
  have h0 := hevent n hn
  have h1 := hevent (n + 1) (by omega)
  have h1' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
  have hs0 := (one_lt_gcd n).1.1
  calc
    a (n + T + 1) - a (n + T) =
        (a (n + 1) + L) - (a n + L) := by rw [h0, h1']
    _ = a (n + 1) - a n := by omega

private lemma affine_boundary_defect_eq_increment_gap
    {a : ℕ → ℕ} {n T L : ℕ}
    (hstrict : ∀ i, a i < a (i + 1))
    (hnext : a (n + T + 1) = a (n + 1) + L)
    (hupper : a (n + T) ≤ a n + L) :
    a n + L - a (n + T) =
      (a (n + T + 1) - a (n + T)) - (a (n + 1) - a n) := by
  have h0 := hstrict n
  have h1 := hstrict (n + T)
  have hnext' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  omega

private lemma boundary_defect_small_or_prefix
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    a (n + T) - L ≤ a 0 ∨
      ∃ j, j ≤ n ∧ a (n + T) - L = a j := by
  have hupper := greedy_tail_upper_bound one_lt one_lt_gcd hT hL htail
  have hdn : a (n + T) - L ≤ a n := by omega
  have hall : ∀ i, i ≤ n →
      1 < Nat.gcd (a (n + T) - L) (a i) := by
    intro i hi
    obtain ⟨p, hp, hpi, hpL, hpd⟩ :=
      boundary_defect_prime_support_research one_lt one_lt_gcd
        hT hL htail hdef i hi
    have hpg : p ∣ Nat.gcd (a (n + T) - L) (a i) :=
      Nat.dvd_gcd hpd hpi
    have hgpos' : 0 < Nat.gcd (a i) (a (n + T) - L) := by
      apply Nat.gcd_pos_of_pos_left
      have hi' := one_lt i
      omega
    have hgpos : 0 < Nat.gcd (a (n + T) - L) (a i) := by
      simpa [Nat.gcd_comm] using hgpos'
    exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)
  exact greedy_common_gcd_value_or_small one_lt_gcd hdn hall

private lemma research_prefix_increment_transport
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (hprefix : ∀ n, n < N →
      a (n + T + 1) - a (n + T) = a (n + 1) - a n) :
    ∀ n, a (n + T + 1) - a (n + T) = a (n + 1) - a n := by
  intro n
  by_cases hn : N ≤ n
  · have h0 := hevent n hn
    have h1 := hevent (n + 1) (by omega)
    have h1' : a (n + T + 1) = a (n + 1) + L := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
    omega
  · exact hprefix n (by omega)

private lemma research_globalize_from_prefix_increment
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (hprefix : ∀ n, n < N →
      a (n + T + 1) - a (n + T) = a (n + 1) - a n) :
    ∀ n, a (n + T) = a n + L := by
  apply globalize_from_global_increment_period one_lt_gcd hT hevent
  intro n
  by_cases hn : N ≤ n
  · have h0 := hevent n hn
    have h1 := hevent (n + 1) (by omega)
    have h1' : a (n + T + 1) = a (n + 1) + L := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1
    omega
  · exact hprefix n (by omega)

private lemma research_eventual_affine_common_shift_gcd
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i, 1 < Nat.gcd L (a i) := by
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  intro i
  have hi : 0 < a i := by
    have h := one_lt i
    omega
  obtain ⟨k0, x, hx⟩ := eventual_affine_residue_offset hT hevent i
  by_contra hnot
  have hDpos : 0 < Nat.gcd L (a i) := by
    apply Nat.gcd_pos_of_pos_left
    exact hL
  have hD : Nat.gcd L (a i) = 1 := by omega
  have hcop : Nat.gcd (x + L) (Nat.gcd L (a i)) = 1 := by
    simp [hD]
  obtain ⟨q, hq⟩ := positive_coprime_translate
    (x := x + L) (L := L) (A := a i) hi hcop
  have hprog : ∀ q, a (i + (k0 + 1 + q) * T) = (x + L) + q * L := by
    intro q
    have h := hx (k0 + 1 + q) (by omega)
    have hsub : k0 + 1 + q - k0 = 1 + q := by omega
    rw [hsub] at h
    calc
      a (i + (k0 + 1 + q) * T) = x + (1 + q) * L := by simpa using h
      _ = (x + L) + q * L := by
        rw [Nat.add_mul]
        simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hidx : i < i + (k0 + 1 + q) * T := by
    have hkpos : 0 < k0 + 1 + q := by omega
    have hmul : 0 < (k0 + 1 + q) * T := Nat.mul_pos hkpos hT
    omega
  have hp := hpair i (i + (k0 + 1 + q) * T) hidx
  rw [hprog q] at hp
  omega

private lemma tail_affine_iterate_from_boundary
    {a : ℕ → ℕ} {n T L : ℕ}
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ∀ q, a (n + 1 + q * T) = a (n + 1) + q * L := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
      have hq := htail (n + 1 + q * T) (by omega)
      rw [ih] at hq
      simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq

private lemma eventual_boundary_defect_pos
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    L ≤ a (n + T) := by
  have hcommon : ∀ i, 1 < Nat.gcd L (a i) :=
    research_eventual_affine_common_shift_gcd
      one_lt one_lt_gcd hT hL htail
  by_contra hbad
  have hmem : L ∈
      {m | a (n + T) < m ∧ ∀ i ≤ n + T, 1 < Nat.gcd m (a i)} := by
    constructor
    · omega
    · intro i hi
      exact hcommon i
  have hle := (one_lt_gcd (n + T)).2 hmem
  have hnext := htail (n + 1) (by omega)
  have hnext' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  have hpos := one_lt (n + 1)
  omega

private lemma boundary_defect_prefix_branch
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T)
    (hdef : L ≤ a (n + T))
    (hprefix : ∀ j, j < n → a (j + T) = a j + L)
    {j : ℕ} (hj : j ≤ n)
    (hjeq : a (n + T) - L = a j) :
    a (n + T) = a n + L := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hinc : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  have hend : a (n + T) = a j + L := by omega
  by_cases hjn : j = n
  · subst j
    exact hend
  · have hjlt : j < n := by omega
    have hp := hprefix j hjlt
    have hidx : j + T < n + T := by omega
    have hval : a (j + T) = a (n + T) := by omega
    have hgap : 0 < (n + T) - (j + T) := by omega
    have hinc' : a (j + T) < a ((j + T) + ((n + T) - (j + T))) :=
      hinc (j + T) ((n + T) - (j + T)) hgap
    have harg : (j + T) + ((n + T) - (j + T)) = n + T := by omega
    rw [harg] at hinc'
    omega

private lemma tail_value_common_prime
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    {i m : ℕ} (hi : i < m) (hm : n + 1 ≤ m) :
    ∃ p, Nat.Prime p ∧ p ∣ L ∧ p ∣ a i ∧ p ∣ a m := by
  have hcommon : ∀ r, 1 < Nat.gcd L (a r) :=
    research_eventual_affine_common_shift_gcd
      one_lt one_lt_gcd hT hL htail
  have hai : 0 < a i := by
    have h := one_lt i
    omega
  have ham : 0 < a m := by
    have h := one_lt m
    omega
  have hpair : ∀ r s, r < s → 1 < Nat.gcd (a s) (a r) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  have hGpos : 0 < Nat.gcd (a m) (Nat.gcd L (a i)) :=
    Nat.gcd_pos_of_pos_left _ ham
  have htriple : 1 < Nat.gcd (a m) (Nat.gcd L (a i)) := by
    by_cases hco : Nat.gcd (a m) (Nat.gcd L (a i)) = 1
    · obtain ⟨q, hq⟩ := positive_coprime_translate
        (x := a m) (L := L) (A := a i) hai hco
      have hprog : ∀ q, a (m + q * T) = a m + q * L := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
            have hh := htail (m + q * T) (by omega)
            rw [ih] at hh
            simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      have hqT : 0 ≤ q * T := Nat.zero_le _
      have hidx : i < m + q * T := by omega
      have hp := hpair i (m + q * T) hidx
      rw [hprog q] at hp
      have hq' := hq
      omega
    · omega
  let p := Nat.minFac (Nat.gcd (a m) (Nat.gcd L (a i)))
  have hp : Nat.Prime p := by
    dsimp [p]
    exact Nat.minFac_prime (by omega)
  have hpd : p ∣ Nat.gcd (a m) (Nat.gcd L (a i)) := by
    dsimp [p]
    exact Nat.minFac_dvd _
  have hpm : p ∣ a m := (Nat.dvd_gcd_iff.mp hpd).1
  have hpli : p ∣ Nat.gcd L (a i) := (Nat.dvd_gcd_iff.mp hpd).2
  have hpL : p ∣ L := (Nat.dvd_gcd_iff.mp hpli).1
  have hpi : p ∣ a i := (Nat.dvd_gcd_iff.mp hpli).2
  exact ⟨p, hp, hpL, hpi, hpm⟩

private lemma research_globalize_from_defect_transport
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (hdefect : ∀ n,
      (∀ k, n + 1 ≤ k → a (k + T) = a k + L) →
        a (n + T) - L = a n) :
    ∀ n, a (n + T) = a n + L := by
  apply globalize_from_tail_backstep hevent
  intro n htail
  have hD := hdefect n htail
  have hbound := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  omega

private lemma globalize_eventual_affine_period_of_affine_witness
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    (hwitness : ∀ n,
      (∀ k, n + 1 ≤ k → a (k + T) = a k + L) →
        ∃ j, j ≤ n ∧ a (n + T) - L = a j ∧
          (j = n ∨ a (j + T) = a j + L)) :
    ∀ n, a (n + T) = a n + L := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hinc : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  apply globalize_from_tail_backstep hevent
  intro n htail
  have hdef : L ≤ a (n + T) := by
    exact eventual_boundary_defect_pos one_lt one_lt_gcd hT hL htail
  obtain ⟨j, hj, hjeq, hjaff⟩ := hwitness n htail
  have hend : a (n + T) = a j + L := by omega
  by_cases hjn : j = n
  · subst j
    exact hend
  · have hjlt : j < n := by omega
    have hp : a (j + T) = a j + L := hjaff.resolve_left hjn
    have hidx : j + T < n + T := by omega
    have hval : a (j + T) = a (n + T) := by omega
    have hgap : 0 < (n + T) - (j + T) := by omega
    have hinc' : a (j + T) <
        a ((j + T) + ((n + T) - (j + T))) :=
      hinc (j + T) ((n + T) - (j + T)) hgap
    have harg : (j + T) + ((n + T) - (j + T)) = n + T := by omega
    rw [harg] at hinc'
    omega

private lemma research_tail_boundary_increment_gap
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    a (n + T + 1) - a (n + T) - (a (n + 1) - a n) =
      a n + L - a (n + T) := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hnext := htail (n + 1) (by omega)
  have hnext' : a (n + T + 1) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  have hupper : a (n + T) ≤ a n + L := by
    exact greedy_tail_upper_bound one_lt one_lt_gcd hT hL htail
  have hgap := affine_boundary_defect_eq_increment_gap
    (a := a) (n := n) (T := T) (L := L) hstrict hnext' hupper
  omega

private lemma parametric_admissible_shift_family
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {L : ℕ} (hL : 0 < L) :
    let P : Finset ℕ := (a 0).primeFactors
    let Q : ℕ := ∏ p ∈ P.filter (fun p => ¬ p ∣ L), p
    ∀ q i, ∃ p, Nat.Prime p ∧ p ∣ a i ∧ p ∣ (a 0 + (Q * q) * L) := by
  classical
  have hcanon : ∀ i, ∃ p ∈ (a 0).primeFactors, p ∣ a i :=
    canonical_initial_prime_support one_lt one_lt_gcd
  dsimp
  let Q : ℕ := ∏ p ∈ (a 0).primeFactors.filter (fun p => ¬ p ∣ L), p
  change ∀ q i, ∃ p, Nat.Prime p ∧ p ∣ a i ∧ p ∣ (a 0 + (Q * q) * L)
  intro q i
  obtain ⟨p, hpP, hpi⟩ := hcanon i
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpP
  have hp0 : p ∣ a 0 := Nat.dvd_of_mem_primeFactors hpP
  by_cases hpL : p ∣ L
  · refine ⟨p, hp, hpi, ?_⟩
    apply dvd_add hp0
    exact dvd_mul_of_dvd_right hpL (Q * q)
  · have hpQ : p ∣ Q := by
      dsimp [Q]
      apply Finset.dvd_prod_of_mem (fun r : ℕ => r)
      exact Finset.mem_filter.mpr ⟨hpP, hpL⟩
    refine ⟨p, hp, hpi, ?_⟩
    apply dvd_add hp0
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpQ q) L

private lemma parametric_shift_greedy_bound
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {L : ℕ} (hL : 0 < L) :
    let P : Finset ℕ := (a 0).primeFactors
    let Q : ℕ := ∏ p ∈ P.filter (fun p => ¬ p ∣ L), p
    ∀ q n, a n < a 0 + (Q * q) * L →
      a (n + 1) ≤ a 0 + (Q * q) * L := by
  classical
  have hcanon : ∀ i, ∃ p ∈ (a 0).primeFactors, p ∣ a i :=
    canonical_initial_prime_support one_lt one_lt_gcd
  dsimp
  let Q : ℕ := ∏ p ∈ (a 0).primeFactors.filter (fun p => ¬ p ∣ L), p
  change ∀ q n, a n < a 0 + (Q * q) * L →
    a (n + 1) ≤ a 0 + (Q * q) * L
  intro q n hlt
  apply (one_lt_gcd n).2
  constructor
  · exact hlt
  · intro i hi
    obtain ⟨p, hpP, hpi⟩ := hcanon i
    have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpP
    have hp0 : p ∣ a 0 := Nat.dvd_of_mem_primeFactors hpP
    by_cases hpL : p ∣ L
    · have hpc : p ∣ a 0 + (Q * q) * L := by
        apply dvd_add hp0
        exact dvd_mul_of_dvd_right hpL (Q * q)
      have hpg : p ∣ Nat.gcd (a 0 + (Q * q) * L) (a i) :=
        Nat.dvd_gcd hpc hpi
      have hgpos : 0 < Nat.gcd (a 0 + (Q * q) * L) (a i) := by
        apply Nat.gcd_pos_of_pos_right
        have hi' := one_lt i
        omega
      exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)
    · have hpQ : p ∣ Q := by
        dsimp [Q]
        apply Finset.dvd_prod_of_mem (fun r : ℕ => r)
        exact Finset.mem_filter.mpr ⟨hpP, hpL⟩
      have hpc : p ∣ a 0 + (Q * q) * L := by
        apply dvd_add hp0
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpQ q) L
      have hpg : p ∣ Nat.gcd (a 0 + (Q * q) * L) (a i) :=
        Nat.dvd_gcd hpc hpi
      have hgpos : 0 < Nat.gcd (a 0 + (Q * q) * L) (a i) := by
        apply Nat.gcd_pos_of_pos_right
        have hi' := one_lt i
        omega
      exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)

private lemma greedy_global_step_of_common_prime
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {p : ℕ} (hp : Nat.Prime p)
    (hall : ∀ i, p ∣ a i) :
    ∀ n, a (n + 1) = a n + p := by
  intro n
  have hpos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  simpa using greedy_step_eq_add_of_common_divisor
    hp.one_lt hpos hall one_lt_gcd n

private lemma pairwise_tail_shift_gcd
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i j, i ≤ j → N ≤ i → N ≤ j →
      1 < Nat.gcd L (Nat.gcd (a j) (a i)) := by
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  intro i j hijorder hi hj
  by_cases hij : i = j
  · subst j
    have hg := eventual_affine_common_shift_gcd
      (a := a) one_lt one_lt_gcd hT hL hevent i
    simpa using hg
  · have hijlt : i < j := by omega
    by_contra hbad
    have hDpos : 0 < Nat.gcd L (Nat.gcd (a j) (a i)) := by
      apply Nat.gcd_pos_of_pos_right
      apply Nat.gcd_pos_of_pos_right
      have hi' := one_lt i
      omega
    have hD : Nat.gcd L (Nat.gcd (a j) (a i)) = 1 := by omega
    have hcop : Nat.gcd (a j) (Nat.gcd L (a i)) = 1 := by
      apply Nat.dvd_one.mp
      have hd : Nat.gcd (a j) (Nat.gcd L (a i)) ∣
          Nat.gcd L (Nat.gcd (a j) (a i)) := by
        apply Nat.dvd_gcd
        · exact dvd_trans (Nat.gcd_dvd_right (a j) (Nat.gcd L (a i)))
            (Nat.gcd_dvd_left L (a i))
        · apply Nat.dvd_gcd
          · exact Nat.gcd_dvd_left (a j) (Nat.gcd L (a i))
          · exact dvd_trans (Nat.gcd_dvd_right (a j) (Nat.gcd L (a i)))
              (Nat.gcd_dvd_right L (a i))
      rw [hD] at hd
      exact hd
    obtain ⟨q, hq⟩ := positive_coprime_translate
      (x := a j) (L := L) (A := a i)
      (by have hi' := one_lt i; omega) hcop
    have hiter : ∀ k, a (j + k * T) = a j + k * L := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          have he := hevent (j + k * T) (by omega)
          have harg : j + (k + 1) * T = (j + k * T) + T := by
            simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          rw [harg, he, ih]
          simp [Nat.succ_mul, Nat.add_assoc]
    have hp := hpair i (j + q * T) (by omega)
    rw [hiter q, hq] at hp
    omega

private lemma boundary_defect_common_gcd_all
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    ∀ i, 1 < Nat.gcd (a (n + T) - L) (a i) := by
  intro i
  by_cases hi : i ≤ n
  · obtain ⟨p, hp, hpi, hpL, hpd⟩ :=
      boundary_defect_prime_support_research one_lt one_lt_gcd
        hT hL htail hdef i hi
    have hpg : p ∣ Nat.gcd (a (n + T) - L) (a i) :=
      Nat.dvd_gcd hpd hpi
    have hgpos : 0 < Nat.gcd (a (n + T) - L) (a i) := by
      apply Nat.gcd_pos_of_pos_right
      have hi' := one_lt i
      omega
    exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)
  · have hi' : n + 1 ≤ i := by omega
    have hit : i ≤ n + T ∨ n + T ≤ i := by omega
    rcases hit with hit | hit
    · have hpair := pairwise_tail_shift_gcd
        (a := a) one_lt one_lt_gcd hT hL
        (N := n + 1) (hevent := htail) i (n + T)
        hit (by omega) (by omega)
      have hG : Nat.gcd L (Nat.gcd (a (n + T)) (a i)) ∣
          Nat.gcd (a (n + T) - L) (a i) := by
        apply Nat.dvd_gcd
        · apply Nat.dvd_sub
          · exact dvd_trans
              (Nat.gcd_dvd_right L (Nat.gcd (a (n + T)) (a i)))
              (Nat.gcd_dvd_left (a (n + T)) (a i))
          · exact Nat.gcd_dvd_left L (Nat.gcd (a (n + T)) (a i))
        · exact dvd_trans
            (Nat.gcd_dvd_right L (Nat.gcd (a (n + T)) (a i)))
            (Nat.gcd_dvd_right (a (n + T)) (a i))
      have hgpos : 0 < Nat.gcd (a (n + T) - L) (a i) := by
        apply Nat.gcd_pos_of_pos_right
        have hi' := one_lt i
        omega
      exact lt_of_lt_of_le hpair (Nat.le_of_dvd hgpos hG)
    · have hpair := pairwise_tail_shift_gcd
        (a := a) one_lt one_lt_gcd hT hL
        (N := n + 1) (hevent := htail) (n + T) i
        (by omega) (by omega) (by omega)
      have hG : Nat.gcd L (Nat.gcd (a i) (a (n + T))) ∣
          Nat.gcd (a (n + T) - L) (a i) := by
        apply Nat.dvd_gcd
        · apply Nat.dvd_sub
          · exact dvd_trans
              (Nat.gcd_dvd_right L (Nat.gcd (a i) (a (n + T))))
              (Nat.gcd_dvd_right (a i) (a (n + T)))
          · exact Nat.gcd_dvd_left L (Nat.gcd (a i) (a (n + T)))
        · exact dvd_trans
            (Nat.gcd_dvd_right L (Nat.gcd (a i) (a (n + T))))
            (Nat.gcd_dvd_left (a i) (a (n + T)))
      have hgpos : 0 < Nat.gcd (a (n + T) - L) (a i) := by
        apply Nat.gcd_pos_of_pos_right
        have hi' := one_lt i
        omega
      exact lt_of_lt_of_le hpair (Nat.le_of_dvd hgpos hG)

private lemma boundary_backstep_of_positive
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hn : 0 < n)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hprefix : ∀ j, j < n → a (j + T) = a j + L) :
    a (n + T) = a n + L := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hmono : ∀ i j, i ≤ j → a i ≤ a j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step j hij ih =>
        exact le_trans ih (Nat.le_of_lt (hstrict j))
  have hdef : L ≤ a (n + T) := by
    have h := eventual_boundary_defect_pos
      (a := a) one_lt one_lt_gcd hT hL htail
    omega
  have hupper : a (n + T) ≤ a n + L := by
    have h := eventual_boundary_upper_bound_candidate
      (a := a) one_lt one_lt_gcd
      (N := n + 1) (T := T) (L := L)
      (by omega) hT hL htail
    simpa [Nat.succ_eq_add_one] using h
  by_contra hbad
  have hlt : a (n + T) < a n + L := by omega
  rcases boundary_defect_small_or_prefix
      (a := a) one_lt one_lt_gcd hT hL htail hdef with
    hsmall | ⟨j, hj, hjeq⟩
  · have hP0 := hprefix 0 (by omega)
    have hP0' : a T = a 0 + L := by simpa using hP0
    have hinc : a T < a (n + T) := by
      exact lt_of_lt_of_le (hstrict T) (hmono (T + 1) (n + T) (by omega))
    omega
  · by_cases hjn : j = n
    · subst j
      omega
    · have hjlt : j < n := by omega
      have hPj := hprefix j hjlt
      have hPj' : a (j + T) = a j + L := by simpa using hPj
      have hxn : a (n + T) = a j + L := by omega
      have hval : a (j + T) = a (n + T) := hPj'.trans hxn.symm
      have hinc : a (j + T) < a (n + T) := by
        exact lt_of_lt_of_le (hstrict (j + T))
          (hmono (j + T + 1) (n + T) (by omega))
      omega

private lemma parametric_shift_admissible_prefix_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {L : ℕ} (hL : 0 < L) :
    let P : Finset ℕ := (a 0).primeFactors
    let Q : ℕ := ∏ p ∈ P.filter (fun p => ¬ p ∣ L), p
    ∀ q n, ∀ i ≤ n,
      1 < Nat.gcd (a 0 + (Q * q) * L) (a i) := by
  classical
  dsimp
  let Q : ℕ := ∏ p ∈ (a 0).primeFactors.filter (fun p => ¬ p ∣ L), p
  change ∀ q n, ∀ i ≤ n,
    1 < Nat.gcd (a 0 + (Q * q) * L) (a i)
  intro q n i hi
  obtain ⟨p, hp, hpi, hpc⟩ :=
    parametric_admissible_shift_family one_lt one_lt_gcd hL q i
  have hpg : p ∣ Nat.gcd (a 0 + (Q * q) * L) (a i) :=
    Nat.dvd_gcd hpc hpi
  have hgpos : 0 < Nat.gcd (a 0 + (Q * q) * L) (a i) := by
    apply Nat.gcd_pos_of_pos_right
    have hi' := one_lt i
    omega
  exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)

private lemma boundary_defect_dichotomy_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    L ≤ a (n + T) ∧
      (a (n + T) - L ≤ a 0 ∨
        ∃ j, j ≤ n ∧ a (n + T) - L = a j) := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hsplit := boundary_defect_small_or_prefix
    (a := a) one_lt one_lt_gcd hT hL htail hdef
  exact ⟨hdef, hsplit⟩

private lemma large_boundary_defect_prefix_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hprefix : ∀ j, j < n → a (j + T) = a j + L)
    (hlarge : a 0 < a (n + T) - L) :
    a (n + T) = a n + L := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hsplit := boundary_defect_small_or_prefix
    (a := a) one_lt one_lt_gcd hT hL htail hdef
  rcases hsplit with hsmall | ⟨j, hj, hjeq⟩
  · omega
  · exact boundary_defect_prefix_branch
      (a := a) one_lt_gcd hT hdef hprefix hj hjeq

private lemma boundary_defect_parametric_prime_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    let P : Finset ℕ := (a 0).primeFactors
    let Q : ℕ := ∏ p ∈ P.filter (fun p => ¬ p ∣ L), p
    ∀ q, ∃ p, Nat.Prime p ∧ p ∣ (a (n + T) - L) ∧
      p ∣ (a 0 + (Q * q) * L) := by
  classical
  have hs := boundary_defect_prime_support_research
    (a := a) one_lt one_lt_gcd hT hL htail hdef 0 (Nat.zero_le n)
  obtain ⟨p, hp, hp0, hpL, hpd⟩ := hs
  dsimp
  let Q : ℕ := ∏ p ∈ (a 0).primeFactors.filter (fun p => ¬ p ∣ L), p
  change ∀ q, ∃ p, Nat.Prime p ∧ p ∣ (a (n + T) - L) ∧
    p ∣ (a 0 + (Q * q) * L)
  intro q
  refine ⟨p, hp, hpd, ?_⟩
  apply dvd_add hp0
  exact dvd_mul_of_dvd_right hpL (Q * q)

private lemma parametric_boundary_defect_upper
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    a (n + T) - L ≤ a n := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hcommon := boundary_defect_common_gcd_all
    (a := a) one_lt one_lt_gcd hT hL htail hdef
  have hs : a (n + T) < a ((n + 1) + T) := by
    have hs0 := (one_lt_gcd (n + T)).1.1
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs0
  have hnext := htail (n + 1) (by omega)
  have hnext' : a ((n + 1) + T) = a (n + 1) + L := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnext
  by_contra hbad
  have hlt : a n < a (n + T) - L := by omega
  have hmem : a (n + T) - L ∈
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} := by
    constructor
    · exact hlt
    · intro i hi
      exact hcommon i
  have hle := (one_lt_gcd n).2 hmem
  omega

private lemma parametric_boundary_defect_orbit
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ∀ q, a (n + T + q * T) - (q + 1) * L = a (n + T) - L := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hiter : ∀ q, a (n + T + q * T) = a (n + T) + q * L := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have hh := htail (n + T + q * T) (by omega)
        rw [ih] at hh
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  intro q
  have hqL : (q + 1) * L = q * L + L := by
    simp [Nat.add_mul]
  rw [hqL, hiter q]
  omega

private lemma research_boundary_defect_shift_admissible_prefix
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ∀ q i, i ≤ n →
      1 < Nat.gcd (a (n + T) - L + q * L) (a i) := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  intro q i hi
  obtain ⟨p, hp, hpi, hpL, hpd⟩ :=
    boundary_defect_prime_support_research
      (a := a) one_lt one_lt_gcd hT hL htail hdef i hi
  have hpdq : p ∣ a (n + T) - L + q * L := by
    apply Nat.dvd_add hpd
    exact dvd_mul_of_dvd_right hpL q
  have hpg : p ∣ Nat.gcd (a (n + T) - L + q * L) (a i) :=
    Nat.dvd_gcd hpdq hpi
  have hgpos : 0 < Nat.gcd (a (n + T) - L + q * L) (a i) := by
    apply Nat.gcd_pos_of_pos_right
    have hi' := one_lt i
    omega
  exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)

private lemma boundary_defect_common_shift_gcd_all
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    ∀ i, 1 < Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
  intro i
  by_cases hi : i ≤ n
  · obtain ⟨p, hp, hpi, hpL, hpd⟩ :=
      boundary_defect_prime_support_research one_lt one_lt_gcd
        hT hL htail hdef i hi
    have hpg : p ∣ Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
      exact Nat.dvd_gcd hpL (Nat.dvd_gcd hpd hpi)
    have hgpos : 0 < Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
      apply Nat.gcd_pos_of_pos_right
      apply Nat.gcd_pos_of_pos_right
      have hi' := one_lt i
      omega
    exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hgpos hpg)
  · have hi' : n + 1 ≤ i := by omega
    have hit : i ≤ n + T ∨ n + T ≤ i := by omega
    rcases hit with hit | hit
    · have hpair := pairwise_tail_shift_gcd
        (a := a) one_lt one_lt_gcd hT hL
        (N := n + 1) (hevent := htail) i (n + T)
        hit (by omega) (by omega)
      have hG : Nat.gcd L (Nat.gcd (a (n + T)) (a i)) ∣
          Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
        apply Nat.dvd_gcd
        · exact Nat.gcd_dvd_left L (Nat.gcd (a (n + T)) (a i))
        · apply Nat.dvd_gcd
          · apply Nat.dvd_sub
            · exact dvd_trans
                (Nat.gcd_dvd_right L (Nat.gcd (a (n + T)) (a i)))
                (Nat.gcd_dvd_left (a (n + T)) (a i))
            · exact Nat.gcd_dvd_left L (Nat.gcd (a (n + T)) (a i))
          · exact dvd_trans
              (Nat.gcd_dvd_right L (Nat.gcd (a (n + T)) (a i)))
              (Nat.gcd_dvd_right (a (n + T)) (a i))
      have hgpos : 0 < Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
        apply Nat.gcd_pos_of_pos_left
        exact hL
      exact lt_of_lt_of_le hpair (Nat.le_of_dvd hgpos hG)
    · have hpair := pairwise_tail_shift_gcd
        (a := a) one_lt one_lt_gcd hT hL
        (N := n + 1) (hevent := htail) (n + T) i
        (by omega) (by omega) (by omega)
      have hG : Nat.gcd L (Nat.gcd (a i) (a (n + T))) ∣
          Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
        apply Nat.dvd_gcd
        · exact Nat.gcd_dvd_left L (Nat.gcd (a i) (a (n + T)))
        · apply Nat.dvd_gcd
          · apply Nat.dvd_sub
            · exact dvd_trans
                (Nat.gcd_dvd_right L (Nat.gcd (a i) (a (n + T))))
                (Nat.gcd_dvd_right (a i) (a (n + T)))
            · exact Nat.gcd_dvd_left L (Nat.gcd (a i) (a (n + T)))
          · exact dvd_trans
              (Nat.gcd_dvd_right L (Nat.gcd (a i) (a (n + T))))
              (Nat.gcd_dvd_left (a i) (a (n + T)))
      have hgpos : 0 < Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) := by
        apply Nat.gcd_pos_of_pos_left
        exact hL
      exact lt_of_lt_of_le hpair (Nat.le_of_dvd hgpos hG)

private lemma affine_tail_orbit_from_boundary_defect
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : a (n + T) - L = a n) :
    ∀ q, a (n + T + q * T) = a n + (q + 1) * L := by
  have hbound : L ≤ a (n + T) :=
    eventual_boundary_defect_pos
      (a := a) one_lt one_lt_gcd hT hL htail
  have hiter : ∀ q, a (n + T + q * T) = a (n + T) + q * L := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        have hh := htail (n + T + q * T) (by omega)
        rw [ih] at hh
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  intro q
  have hqL : (q + 1) * L = q * L + L := by simp [Nat.add_mul]
  rw [hiter q, hqL]
  omega

private lemma eventual_tail_hits_boundary_multiples
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ∀ m, a 0 < m → a (n + T) - L ∣ m → ∃ r, a r = m := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hcommon := boundary_defect_common_gcd_all
    (a := a) one_lt one_lt_gcd hT hL htail hdef
  intro m hm hmdiv
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hunbounded : ∀ x, ∃ r, x ≤ a r := by
    intro x
    refine ⟨x, ?_⟩
    induction x with
    | zero => omega
    | succ x ih =>
        have hs := hstrict x
        omega
  have hex : ∃ r, m ≤ a r := hunbounded m
  let r : ℕ := Nat.find hex
  have hr : m ≤ a r := by
    dsimp [r]
    exact Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra hr0
    have hrz : r = 0 := by omega
    have hr' : m ≤ a 0 := by simpa [hrz] using hr
    omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hsmin : ¬ m ≤ a s := by
    intro hps
    have hmin := Nat.find_min' hex hps
    dsimp [r] at hs
    omega
  have hprev : a s < m := by omega
  have hmem : m ∈
      {u | a s < u ∧ ∀ i ≤ s, 1 < Nat.gcd m (a i)} := by
    constructor
    · exact hprev
    · intro i hi
      have hgi := hcommon i
      have hgm : Nat.gcd (a (n + T) - L) (a i) ∣ m :=
        dvd_trans (Nat.gcd_dvd_left (a (n + T) - L) (a i)) hmdiv
      have hga : Nat.gcd (a (n + T) - L) (a i) ∣ a i :=
        Nat.gcd_dvd_right (a (n + T) - L) (a i)
      have hgg := Nat.dvd_gcd hgm hga
      have hpos_i : 0 < a i := by
        have hi' := one_lt i
        omega
      have hmg_pos : 0 < Nat.gcd m (a i) :=
        Nat.gcd_pos_of_pos_right m hpos_i
      exact lt_of_lt_of_le hgi (Nat.le_of_dvd hmg_pos hgg)
  have hle := (one_lt_gcd s).2 hmem
  have hnext : a (s + 1) ≤ m := hle
  have hr' : m ≤ a (s + 1) := by
    simpa [hs] using hr
  refine ⟨s + 1, ?_⟩
  omega

private lemma positive_failure_descends_to_zero_or_lower
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    {n : ℕ}
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ¬ a (n + T) = a n + L →
      n = 0 ∨ ∃ j, j < n ∧ ¬ a (j + T) = a j + L := by
  intro hne
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  · right
    by_contra hno
    have hprefix : ∀ j, j < n → a (j + T) = a j + L := by
      intro j hj
      by_contra hjbad
      exact hno ⟨j, hj, hjbad⟩
    have hnpos : 0 < n := by omega
    exact hne (boundary_backstep_of_positive
      (a := a) one_lt one_lt_gcd hT hL hnpos htail hprefix)

private lemma globalization_zero_threshold_base
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ¬ (N = 0 ∧ ∃ n, ¬ a (n + T) = a n + L) := by
  rintro ⟨rfl, n, hn⟩
  exact hn (audit_target_zero_threshold
    (a := a) one_lt one_lt_gcd hT hL hevent n)

private lemma zero_boundary_defect_support
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, 1 ≤ k → a (k + T) = a k + L) :
    L ≤ a T ∧ ∀ i, 1 < Nat.gcd (a T - L) (a i) := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd (n := 0) hT hL htail
  constructor
  · simpa using hdef
  · have hG := boundary_defect_common_gcd_all
      (a := a) one_lt one_lt_gcd (n := 0) hT hL htail hdef
    simpa [Nat.zero_add] using hG

private lemma base_bridge_prime_support
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, 1 ≤ k → a (k + T) = a k + L) :
    ∀ i, 1 ≤ i → ∃ p, Nat.Prime p ∧ p ∣ a 0 ∧ p ∣ L ∧ p ∣ a i := by
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  have hiter : ∀ i q, 1 ≤ i →
      a (i + q * T) = a i + q * L := by
    intro i q hi
    induction q with
    | zero => simp
    | succ q ih =>
        have hh := htail (i + q * T) (by omega)
        rw [ih] at hh
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  intro i hi
  have hall : ∀ q, 1 < Nat.gcd (a i + q * L) (a 0) := by
    intro q
    have hp := hpair 0 (i + q * T) (by omega)
    rw [hiter i q hi] at hp
    exact hp
  obtain ⟨p, hp, hpA, hpL, hpi⟩ := tail_prime_support_of_all_gcd
    (A := a 0) (x := a i) (L := L)
    (by have h0 := one_lt 0; omega) hall
  exact ⟨p, hp, hpA, hpL, hpi⟩

private lemma research_failure_descends
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hn : 0 < n)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hbad : a (n + T) ≠ a n + L) :
    ∃ j, j < n ∧ a (j + T) ≠ a j + L := by
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  have hsplit := boundary_defect_small_or_prefix
    (a := a) one_lt one_lt_gcd hT hL htail hdef
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hinc : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  rcases hsplit with hsmall | ⟨j, hj, hjeq⟩
  · refine ⟨0, by omega, ?_⟩
    intro h0
    have h0' : a (0 + T) = a 0 + L := h0
    have hinc' : a (0 + T) < a (n + T) := by
      have hi := hinc T n hn
      simpa [Nat.add_comm] using hi
    omega
  · by_cases hjn : j = n
    · subst j
      exfalso
      apply hbad
      omega
    · have hjlt : j < n := by omega
      refine ⟨j, hjlt, ?_⟩
      intro hp
      have hinc' : a (j + T) < a (n + T) := by
        have hi := hinc (j + T) (n - j) (by omega)
        have harg : (j + T) + (n - j) = n + T := by omega
        rw [harg] at hi
        exact hi
      omega

private lemma research_largest_bad_index_boundary
    {a : ℕ → ℕ}
    {N T L : ℕ}
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    (∃ n, ¬ a (n + T) = a n + L) →
      ∃ m, ¬ a (m + T) = a m + L ∧
        ∀ k, m < k → a (k + T) = a k + L := by
  classical
  rintro ⟨n, hn⟩
  have hnN : n < N := by
    by_contra h
    have hNn : N ≤ n := by omega
    exact hn (hevent n hNn)
  let B : Finset ℕ := (Finset.range N).filter
    (fun k => ¬ a (k + T) = a k + L)
  have hB : B.Nonempty := by
    refine ⟨n, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnN, hn⟩
  let m : ℕ := B.max' hB
  have hmB : m ∈ B := by
    exact Finset.max'_mem B hB
  have hm : ¬ a (m + T) = a m + L :=
    (Finset.mem_filter.mp hmB).2
  refine ⟨m, hm, ?_⟩
  intro k hmk
  by_cases hkN : k < N
  · by_contra hbad
    have hkB : k ∈ B := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hbad⟩
    have hkm : k ≤ m := Finset.le_max' B k hkB
    omega
  · have hNk : N ≤ k := by omega
    exact hevent k hNk

private lemma boundary_defect_global_shift_admissible
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    ∀ q i, 1 < Nat.gcd (a (n + T) - L + q * L) (a i) := by
  intro q i
  have hcommon := boundary_defect_common_shift_gcd_all
    (a := a) one_lt one_lt_gcd hT hL htail hdef i
  have hgd : Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) ∣
      a (n + T) - L := by
    exact dvd_trans
      (Nat.gcd_dvd_right L (Nat.gcd (a (n + T) - L) (a i)))
      (Nat.gcd_dvd_left (a (n + T) - L) (a i))
  have hgL : Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) ∣ L :=
    Nat.gcd_dvd_left L (Nat.gcd (a (n + T) - L) (a i))
  have hgcand : Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) ∣
      a (n + T) - L + q * L := by
    apply dvd_add hgd
    exact dvd_mul_of_dvd_right hgL q
  have hgai : Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) ∣ a i := by
    exact dvd_trans
      (Nat.gcd_dvd_right L (Nat.gcd (a (n + T) - L) (a i)))
      (Nat.gcd_dvd_right (a (n + T) - L) (a i))
  have hgcd : Nat.gcd L (Nat.gcd (a (n + T) - L) (a i)) ∣
      Nat.gcd (a (n + T) - L + q * L) (a i) :=
    Nat.dvd_gcd hgcand hgai
  have hpos : 0 < Nat.gcd (a (n + T) - L + q * L) (a i) := by
    apply Nat.gcd_pos_of_pos_right
    have hi := one_lt i
    omega
  exact lt_of_lt_of_le hcommon (Nat.le_of_dvd hpos hgcd)

private lemma parametric_admissible_value_hits
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {m : ℕ} (hm : a 0 < m)
    (hcommon : ∀ i, 1 < Nat.gcd m (a i)) :
    ∃ r, a r = m := by
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hunbounded : ∀ x, ∃ r, x ≤ a r := by
    intro x
    refine ⟨x, ?_⟩
    induction x with
    | zero => omega
    | succ x ih =>
        have hs := hstrict x
        omega
  have hex : ∃ r, m ≤ a r := hunbounded m
  let r : ℕ := Nat.find hex
  have hr : m ≤ a r := by
    dsimp [r]
    exact Nat.find_spec hex
  have hrpos : 0 < r := by
    by_contra hr0
    have hrz : r = 0 := by omega
    have hr' : m ≤ a 0 := by simpa [hrz] using hr
    omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hsmin : ¬ m ≤ a s := by
    intro hps
    have hmin := Nat.find_min' hex hps
    dsimp [r] at hs
    omega
  have hprev : a s < m := by omega
  have hmem : m ∈
      {u | a s < u ∧ ∀ i ≤ s, 1 < Nat.gcd u (a i)} := by
    constructor
    · exact hprev
    · intro i hi
      exact hcommon i
  have hle := (one_lt_gcd s).2 hmem
  have hnext : a (s + 1) ≤ m := hle
  have hr' : m ≤ a (s + 1) := by
    simpa [hs] using hr
  refine ⟨s + 1, ?_⟩
  omega

private lemma globalize_from_positive_tail
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, 1 ≤ k → a (k + T) = a k + L) :
    ∀ n, a (n + T) = a n + L := by
  apply greedy_backward_shift_propagation one_lt one_lt_gcd
  intro n
  exact htail (n + 1) (by omega)

private lemma parametric_tail_to_global
    {P : ℕ → Prop} {N : ℕ}
    (htail : ∀ n, N ≤ n → P n)
    (hback : ∀ n,
      (∀ k, n + 1 ≤ k → P k) → P n) :
    ∀ n, P n := by
  have hQ : ∀ q, q ≤ N →
      (∀ r, q ≤ r → P r) := by
    intro q hq
    exact Nat.decreasingInduction' (P := fun q =>
      ∀ r, q ≤ r → P r) (m := q) (n := N)
      (fun k hk hkn ih => by
        intro r hr
        by_cases hkr : r = k
        · subst r
          apply hback k
          exact ih
        · have hk1 : k + 1 ≤ r := by omega
          exact ih r hk1)
      hq (by
        intro r hr
        exact htail r (by omega))
  intro n
  exact hQ 0 (Nat.zero_le N) n (Nat.zero_le n)

private lemma maximal_failure_boundary_defect_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    (∃ n, ¬ a (n + T) = a n + L) →
      ∃ m, ¬ a (m + T) = a m + L ∧
        (∀ k, m < k → a (k + T) = a k + L) ∧
        (L ≤ a (m + T) ∧
          (a (m + T) - L ≤ a 0 ∨
            ∃ j, j ≤ m ∧ a (m + T) - L = a j)) := by
  intro hbad
  obtain ⟨m, hm_bad, hm_tail⟩ :=
    research_largest_bad_index_boundary (a := a) (N := N) (T := T) (L := L) hevent hbad
  have hm_tail' : ∀ k, m + 1 ≤ k → a (k + T) = a k + L := by
    intro k hk
    exact hm_tail k (by omega)
  have hcut := boundary_defect_dichotomy_cut
    (a := a) one_lt one_lt_gcd hT hL hm_tail'
  exact ⟨m, hm_bad, hm_tail, hcut⟩

private lemma maximal_failure_parametric_boundary
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    (∃ n, ¬ a (n + T) = a n + L) →
      ∃ m, ¬ a (m + T) = a m + L ∧
        (∀ k, m < k → a (k + T) = a k + L) ∧
        L ≤ a (m + T) ∧
        (a (m + T) - L ≤ a 0 ∨
          ∃ j, j ≤ m ∧ a (m + T) - L = a j) ∧
        (∀ q, a (m + T + q * T) - (q + 1) * L = a (m + T) - L) ∧
        (∀ q i, 1 < Nat.gcd (a (m + T) - L + q * L) (a i)) := by
  intro hbad
  obtain ⟨m, hm_bad, hm_tail⟩ :=
    research_largest_bad_index_boundary (a := a) (N := N) (T := T) (L := L) hevent hbad
  have hm_tail' : ∀ k, m + 1 ≤ k → a (k + T) = a k + L := by
    intro k hk
    exact hm_tail k (by omega)
  have hcut := boundary_defect_dichotomy_cut
    (a := a) one_lt one_lt_gcd hT hL hm_tail'
  have horbit := parametric_boundary_defect_orbit
    (a := a) one_lt one_lt_gcd hT hL hm_tail'
  have hadm := boundary_defect_global_shift_admissible
    (a := a) one_lt one_lt_gcd hT hL hm_tail' hcut.1
  exact ⟨m, hm_bad, hm_tail, hcut.1, hcut.2, horbit, hadm⟩

private lemma affine_residue_pair_gcd
    {L r s q r' : ℕ}
    (hpos : 0 < s + r' * L)
    (h : 1 < Nat.gcd L (Nat.gcd r s)) :
    1 < Nat.gcd (r + q * L) (s + r' * L) := by
  have hdiv : Nat.gcd L (Nat.gcd r s) ∣
      Nat.gcd (r + q * L) (s + r' * L) := by
    apply Nat.dvd_gcd
    · apply dvd_add
      · exact dvd_trans
          (Nat.gcd_dvd_right L (Nat.gcd r s))
          (Nat.gcd_dvd_left r s)
      · exact dvd_mul_of_dvd_right
          (Nat.gcd_dvd_left L (Nat.gcd r s)) q
    · apply dvd_add
      · exact dvd_trans
          (Nat.gcd_dvd_right L (Nat.gcd r s))
          (Nat.gcd_dvd_right r s)
      · exact dvd_mul_of_dvd_right
          (Nat.gcd_dvd_left L (Nat.gcd r s)) r'
  have hgpos : 0 < Nat.gcd (r + q * L) (s + r' * L) :=
    Nat.gcd_pos_of_pos_right _ hpos
  exact lt_of_lt_of_le h (Nat.le_of_dvd hgpos hdiv)

private lemma boundary_defect_is_sequence_value_research
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T))
    (hlarge : a 0 < a (n + T) - L) :
    ∃ r, a r = a (n + T) - L := by
  apply parametric_admissible_value_hits one_lt one_lt_gcd hlarge
  intro i
  have h := boundary_defect_global_shift_admissible
    (a := a) one_lt one_lt_gcd hT hL htail hdef 0 i
  simpa using h

private lemma positive_boundary_defect_descends_research
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hn : 0 < n)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T))
    (hbad : a (n + T) ≠ a n + L)
    (hlarge : a 0 < a (n + T) - L) :
    ∃ r, r < n ∧ a r = a (n + T) - L := by
  have hupper := eventual_boundary_upper_bound_candidate
    (a := a) one_lt one_lt_gcd
    (N := n + 1) (T := T) (L := L) (by omega) hT hL htail
  have hupper' : a (n + T) ≤ a n + L := by
    simpa [Nat.succ_eq_add_one] using hupper
  have hdlt : a (n + T) - L < a n := by omega
  have hcommon : ∀ i, 1 < Nat.gcd (a (n + T) - L) (a i) := by
    intro i
    have h := boundary_defect_global_shift_admissible
      (a := a) one_lt one_lt_gcd hT hL htail hdef 0 i
    simpa using h
  obtain ⟨r, hr⟩ := parametric_admissible_value_hits
    (a := a) one_lt one_lt_gcd hlarge hcommon
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hmono : ∀ i j, i ≤ j → a i ≤ a j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step j hij ih =>
        exact le_trans ih (Nat.le_of_lt (hstrict j))
  refine ⟨r, ?_, hr⟩
  by_contra hnot
  have hnr : n ≤ r := by omega
  have hle := hmono n r hnr
  rw [hr] at hle
  omega

private lemma boundary_defect_arithmetic_progression_hits_research
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T)) :
    ∀ q, a 0 < a (n + T) - L + q * L →
      ∃ r, a r = a (n + T) - L + q * L := by
  intro q hlarge
  apply parametric_admissible_value_hits one_lt one_lt_gcd hlarge
  intro i
  have h := boundary_defect_global_shift_admissible
    (a := a) one_lt one_lt_gcd hT hL htail hdef q i
  simpa using h

private lemma tail_pairwise_common_L_support
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i j, N ≤ i → N ≤ j →
      1 < Nat.gcd L (Nat.gcd (a i) (a j)) := by
  have hordered : ∀ i j, N ≤ i → N ≤ j → i ≤ j →
      1 < Nat.gcd L (Nat.gcd (a i) (a j)) := by
    intro i j hi hj hij
    have hiter : ∀ q, a (i + q * T) = a i + q * L := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
          have hh := hevent (i + q * T) (le_trans hi (by omega))
          rw [ih] at hh
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    have hall : ∀ q, 1 < Nat.gcd (a i + q * L) (a j) := by
      intro q
      have hidx : i ≤ i + q * T := by omega
      by_cases hq : q = 0
      · subst q
        by_cases heq : i = j
        · subst j
          have hi' := one_lt i
          simpa using hi'
        · have hlt : i < j := by omega
          have hp := pairwise_gcd_of_greedy_step one_lt_gcd i j hlt
          simpa [Nat.gcd_comm] using hp
      · have hposq : 0 < q := by omega
        have hqT : 0 < q * T := Nat.mul_pos hposq hT
        have hinc : i < i + q * T := by omega
        by_cases hlt : i + q * T < j
        · have hp := pairwise_gcd_of_greedy_step one_lt_gcd (i + q * T) j hlt
          rw [hiter q] at hp
          simpa [Nat.gcd_comm] using hp
        · by_cases heq : i + q * T = j
          · have hp : 1 < Nat.gcd (a (i + q * T)) (a j) := by
              rw [heq]
              have hj' := one_lt j
              simpa using hj'
            rw [hiter q] at hp
            exact hp
          · have hjlt : j < i + q * T := by omega
            have hp := pairwise_gcd_of_greedy_step one_lt_gcd j (i + q * T) hjlt
            rw [hiter q] at hp
            exact hp
    obtain ⟨p, hp, hpj, hpL, hpi⟩ := tail_prime_support_of_all_gcd
      (A := a j) (x := a i) (L := L)
      (by have hj' := one_lt j; omega) hall
    have hdiv : p ∣ Nat.gcd L (Nat.gcd (a i) (a j)) := by
      apply Nat.dvd_gcd hpL
      apply Nat.dvd_gcd hpi hpj
    have hpos : 0 < Nat.gcd L (Nat.gcd (a i) (a j)) := by
      apply Nat.gcd_pos_of_pos_right
      apply Nat.gcd_pos_of_pos_right
      have hj' := one_lt j
      omega
    exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hpos hdiv)
  intro i j hi hj
  by_cases hij : i ≤ j
  · exact hordered i j hi hj hij
  · have hji : j ≤ i := by omega
    have hh := hordered j i hj hi hji
    simpa [Nat.gcd_comm] using hh

private lemma parametric_defect_prime_support_research
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    {D L : ℕ} (hL : 0 < L)
    (hall : ∀ q i, 1 < Nat.gcd (D + q * L) (a i)) :
    ∀ i, ∃ p, Nat.Prime p ∧ p ∣ D ∧ p ∣ L ∧ p ∣ a i := by
  intro i
  obtain ⟨p, hp, hpai, hpL, hpD⟩ :=
    tail_prime_support_of_all_gcd
      (A := a i) (x := D) (L := L)
      (by have hi := one_lt i; omega)
      (fun q => hall q i)
  exact ⟨p, hp, hpD, hpL, hpai⟩

private lemma universal_shift_finite_prime_cover_research
    {a : ℕ → ℕ}
    (ha : ∀ i, 0 < a i)
    {D L : ℕ} (hL : 0 < L)
    (hall : ∀ q i, 1 < Nat.gcd (D + q * L) (a i)) :
    ∀ i, ∃ p ∈ (Nat.gcd D L).primeFactors, p ∣ a i := by
  intro i
  obtain ⟨p, hp, hpai, hpL, hpD⟩ :=
    tail_prime_support_of_all_gcd
      (A := a i) (x := D) (L := L)
      (ha i)
      (fun q => hall q i)
  have hpG : p ∣ Nat.gcd D L := Nat.dvd_gcd hpD hpL
  have hG0 : Nat.gcd D L ≠ 0 := by
    have hG : 0 < Nat.gcd D L := Nat.gcd_pos_of_pos_right D hL
    omega
  have hp_mem : p ∈ (Nat.gcd D L).primeFactors := by
    exact (Nat.mem_primeFactors).2 ⟨hp, hpG, hG0⟩
  exact ⟨p, hp_mem, hpai⟩

private lemma greedy_backward_shift_succ_index_bridge {a : ℕ → ℕ} {T L : ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    (hshift_succ : ∀ k, a (k + 1 + T) = a (k + 1) + L)
    {n : ℕ} (hn : 0 < n) :
    a (n + T) = a n + L := by
  exact greedy_backward_shift_succ_index hshift_succ n hn

private lemma large_boundary_defect_strict_index_descent
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T))
    (hbad : a (n + T) ≠ a n + L)
    (hlarge : a 0 < a (n + T) - L) :
    ∃ r, r < n ∧ a r = a (n + T) - L := by
  obtain ⟨r, hr⟩ := boundary_defect_is_sequence_value_research
    (a := a) one_lt one_lt_gcd hT hL htail hdef hlarge
  have hupper := parametric_boundary_defect_upper
    (a := a) one_lt one_lt_gcd hT hL htail
  have hle : a r ≤ a n := by
    rw [hr]
    exact hupper
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hinc : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  have hrle : r ≤ n := by
    by_contra hnr
    have hnr' : n < r := by omega
    have hi := hinc n (r - n) (by omega)
    have harg : n + (r - n) = r := by omega
    rw [harg] at hi
    omega
  have hrne : r ≠ n := by
    intro hre
    subst r
    apply hbad
    omega
  exact ⟨r, by omega, hr⟩

private lemma small_boundary_defect_forces_failure
    {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hn : 0 < n)
    (hsmall : a (n + T) - L ≤ a 0) :
    ¬ a (n + T) = a n + L := by
  intro heq
  have hinc : ∀ i, 0 < i → a 0 < a i := by
    intro i hi
    induction i with
    | zero => omega
    | succ i ih =>
        by_cases hi0 : i = 0
        · subst i
          exact (one_lt_gcd 0).1.1
        · have hipos : 0 < i := by omega
          have hprev := ih hipos
          have hstep := (one_lt_gcd i).1.1
          omega
  have h0n := hinc n hn
  omega

private lemma eventual_affine_cross_residue_transport
    {a : ℕ → ℕ} {N T L : ℕ}
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ i j q, N ≤ i → N ≤ j →
      a (i + q * T) + a j = a i + a (j + q * T) := by
  intro i j q hi hj
  have hi_iter : ∀ r, a (i + r * T) = a i + r * L := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
        have hh := hevent (i + r * T) (by omega)
        rw [ihr] at hh
        simpa [Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
  have hj_iter : ∀ r, a (j + r * T) = a j + r * L := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
        have hh := hevent (j + r * T) (by omega)
        rw [ihr] at hh
        simpa [Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
  have hiq := hi_iter q
  have hjq := hj_iter q
  rw [hiq, hjq]
  omega

private lemma bad_index_strict_descent_cut
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T))
    (hbad : a (n + T) ≠ a n + L)
    (hlarge : a 0 < a (n + T) - L) :
    ∃ r, r < n ∧ ¬ a (r + T) = a r + L := by
  obtain ⟨r, hr, hval⟩ := large_boundary_defect_strict_index_descent
    (a := a) one_lt one_lt_gcd hT hL htail hdef hbad hlarge
  refine ⟨r, hr, ?_⟩
  intro hgood
  have hstrict : ∀ i, a i < a (i + 1) := by
    intro i
    exact (one_lt_gcd i).1.1
  have hinc : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  have hlt : a (r + T) < a (n + T) := by
    have hi := hinc (r + T) (n - r) (by omega)
    have harg : r + T + (n - r) = n + T := by omega
    rw [harg] at hi
    exact hi
  have hsum := Nat.sub_add_cancel hdef
  rw [← hval] at hsum
  omega

private lemma small_bad_parametric_prime_cover
    {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hdef : L ≤ a (n + T))
    (hsmall : a (n + T) - L ≤ a 0) :
    ∀ i, ∃ p ∈ (Nat.gcd (a (n + T) - L) L).primeFactors, p ∣ a i := by
  have hall : ∀ q i, 1 < Nat.gcd (a (n + T) - L + q * L) (a i) := by
    intro q i
    exact boundary_defect_global_shift_admissible
      (a := a) one_lt one_lt_gcd hT hL htail hdef q i
  apply universal_shift_finite_prime_cover_research
    (a := a) (D := a (n + T) - L) (L := L)
  · intro i
    have hi := one_lt i
    omega
  · exact hL
  · exact hall

private lemma affine_tail_index_lock_research
    {a : ℕ → ℕ} {N T L : ℕ}
    (hstrict : ∀ i, a i < a (i + 1))
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L)
    {i j : ℕ} (hi : N ≤ i)
    (hval : a j = a i + L) :
    j = i + T := by
  have hbase := hevent i hi
  have hEq : a j = a (i + T) := by
    calc
      a j = a i + L := hval
      _ = a (i + T) := by symm; exact hbase
  have hmono : ∀ x d, 0 < d → a x < a (x + d) := by
    intro x d hd
    induction d with
    | zero => omega
    | succ d ih =>
        by_cases hd0 : d = 0
        · subst d
          simpa using hstrict x
        · have hi' := ih (by omega)
          have hs := hstrict (x + d)
          have harg : x + Nat.succ d = (x + d) + 1 := by omega
          rw [harg]
          omega
  by_cases hle : j ≤ i + T
  · by_contra hne
    have hlt : j < i + T := by omega
    have hinc := hmono j ((i + T) - j) (by omega)
    have harg : j + ((i + T) - j) = i + T := by omega
    rw [harg] at hinc
    omega
  · have hgt : i + T < j := by omega
    have hinc := hmono (i + T) (j - (i + T)) (by omega)
    have harg : (i + T) + (j - (i + T)) = j := by omega
    rw [harg] at hinc
    omega

private lemma backward_affine_rigidity_tail_at_succ_local {a : ℕ → ℕ} {T L n : ℕ}
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    {k : ℕ} (hk : n ≤ k) : a (k + 1 + T) = a (k + 1) + L := by
  apply htail
  omega

private lemma event_from_tail_threshold {a : ℕ → ℕ} {N T L n : ℕ}
    (hn : n < N)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    ∀ k, N ≤ k → a (k + T) = a k + L := by
  intro k hk
  apply htail k
  omega

private lemma backward_affine_rigidity_zero_index_candidate {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, 1 ≤ k → a (k + T) = a k + L) :
    a T = a 0 + L := by
  have hupper := eventual_boundary_upper_bound_candidate
    (a := a) one_lt one_lt_gcd (N := 1) (T := T) (L := L)
    (by norm_num) hT hL htail
  have hupper' : a T ≤ a 0 + L := by
    simpa using hupper
  have hdef := eventual_boundary_defect_pos
    (a := a) one_lt one_lt_gcd hT hL htail
  by_contra hbad
  have hlt : a T < a 0 + L := by omega
  have hiter : ∀ i, 0 < i → ∀ q,
      a (i + q * T) = a i + q * L := by
    intro i hi q
    induction q with
    | zero => simp
    | succ q ih =>
        have hh := htail (i + q * T) (by omega)
        rw [ih] at hh
        simpa [Nat.succ_mul, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
  have hcover : ∀ i, 0 < i →
      ∃ p, Nat.Prime p ∧ p ∣ a 0 ∧ p ∣ L ∧ p ∣ a i := by
    intro i hi
    apply tail_prime_support_of_all_gcd (A := a 0) (x := a i) (L := L)
    · have h0 := one_lt 0
      omega
    · intro q
      have hp := pairwise_gcd_of_greedy_step
        one_lt_gcd 0 (i + q * T) (by omega)
      have hiq := hiter i hi q
      simpa [hiq, Nat.gcd_comm] using hp
  obtain ⟨p0, hp0, hp0a, hp0L, hp01⟩ := hcover 1 (by omega)
  have hcommon : ∀ i, 1 < Nat.gcd (a 0 + L) (a i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hdiv : p0 ∣ Nat.gcd (a 0 + L) (a 0) :=
        Nat.dvd_gcd (dvd_add hp0a hp0L) hp0a
      have hpos : 0 < Nat.gcd (a 0 + L) (a 0) := by
        apply Nat.gcd_pos_of_pos_right
        have h0 := one_lt 0
        omega
      exact lt_of_lt_of_le hp0.two_le (Nat.le_of_dvd hpos hdiv)
    · obtain ⟨p, hp, hpa0, hpL, hpai⟩ := hcover i (by omega)
      have hdiv : p ∣ Nat.gcd (a 0 + L) (a i) :=
        Nat.dvd_gcd (dvd_add hpa0 hpL) hpai
      have hpos : 0 < Nat.gcd (a 0 + L) (a i) := by
        apply Nat.gcd_pos_of_pos_right
        have hi' := one_lt i
        omega
      exact lt_of_lt_of_le hp.two_le (Nat.le_of_dvd hpos hdiv)
  have hmem : a 0 + L ∈
      {m | a T < m ∧ ∀ i ≤ T, 1 < Nat.gcd m (a i)} := by
    constructor
    · exact hlt
    · intro i hi
      exact hcommon i
  have hle := (one_lt_gcd T).2 hmem
  have hnext := htail 1 (by omega)
  have hnext' : a (T + 1) = a 1 + L := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnext
  rw [hnext'] at hle
  have hstep : a 0 < a 1 := by
    simpa using (one_lt_gcd 0).1.1
  omega

private lemma backward_affine_rigidity_zero_index {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, 1 ≤ k → a (k + T) = a k + L) :
    a T = a 0 + L := by
  exact backward_affine_rigidity_zero_index_candidate
    one_lt one_lt_gcd hT hL htail

private lemma backward_affine_rigidity_strict_mono {a : ℕ → ℕ}
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    ∀ i, a i < a (i + 1) := by
  intro i
  exact (one_lt_gcd i).1.1

private lemma backward_affine_rigidity_boundary_bounds {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {T L n : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    L ≤ a (n + T) ∧ a (n + T) ≤ a n + L := by
  constructor
  · exact eventual_boundary_defect_pos
      (a := a) one_lt one_lt_gcd hT hL htail
  · have h := eventual_boundary_upper_bound_candidate
      (a := a) one_lt one_lt_gcd (N := n + 1) (T := T) (L := L)
      (by omega) hT hL htail
    simpa using h

private lemma backward_affine_rigidity_defect_cut {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    a (n + T) = a n + L ∨
      a (n + T) - L ≤ a 0 ∨
      ∃ r, r < n ∧ a r = a (n + T) - L := by
  by_cases heq : a (n + T) = a n + L
  · exact Or.inl heq
  · have hdef := (backward_affine_rigidity_boundary_bounds
      (a := a) one_lt one_lt_gcd hT hL htail).1
    by_cases hsmall : a (n + T) - L ≤ a 0
    · exact Or.inr (Or.inl hsmall)
    · exact Or.inr (Or.inr (large_boundary_defect_strict_index_descent
        (a := a) one_lt one_lt_gcd hT hL htail hdef heq (by omega)))

private lemma backward_affine_rigidity_bad_case_cut {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {n T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L)
    (hbad : a (n + T) ≠ a n + L) :
    a (n + T) - L ≤ a 0 ∨
      ∃ r, r < n ∧ a r = a (n + T) - L := by
  have hdef := (backward_affine_rigidity_boundary_bounds
      (a := a) one_lt one_lt_gcd hT hL htail).1
  by_cases hsmall : a (n + T) - L ≤ a 0
  · exact Or.inl hsmall
  · exact Or.inr (large_boundary_defect_strict_index_descent
      (a := a) one_lt one_lt_gcd hT hL htail hdef hbad (by omega))

private lemma backward_affine_rigidity {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L n : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hn : n < N)
    (htail : ∀ k, n + 1 ≤ k → a (k + T) = a k + L) :
    a (n + T) = a n + L := by
  sorry

private lemma globalize_eventual_affine_period {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1)))
    {N T L : ℕ} (hT : 0 < T) (hL : 0 < L)
    (hevent : ∀ n, N ≤ n → a (n + T) = a n + L) :
    ∀ n, a (n + T) = a n + L := by
  sorry

theorem result {a : ℕ → ℕ} (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)} (a (n + 1))) :
    ∃ (T L : ℕ), 0 < T ∧ 0 < L ∧ ∀ n, a (n + T) = a n + L := by
  classical
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have hi := one_lt i
    omega
  have hstep : ∀ n, a n < a (n + 1) :=
    strict_increase_of_greedy_step one_lt_gcd
  have hdouble : ∀ n, a (n + 1) ≤ 2 * a n :=
    greedy_step_le_double one_lt one_lt_gcd
  have hpair : ∀ i j, i < j → 1 < Nat.gcd (a j) (a i) :=
    pairwise_gcd_of_greedy_step one_lt_gcd
  have hbound : ∀ n, a (n + 1) ≤ a n + a 0 := by
    intro n
    obtain ⟨m, hmgt, hmad, hmle⟩ :=
      a0_admissible_bound one_lt one_lt_gcd n
    exact le_trans ((one_lt_gcd n).2 ⟨hmgt, hmad⟩) hmle
  have hleast (n : ℕ) :
      IsLeast {m | a n < m ∧ admissible (a := a) n m} (a (n + 1)) := by
    simpa [admissible] using one_lt_gcd n
  have hleast_support (n : ℕ) :
      IsLeast
        {m | a n < m ∧ ∀ i ≤ n,
          ∃ p, p ∈ m.primeFactors ∧ p ∈ (a i).primeFactors}
        (a (n + 1)) := by
    constructor
    · refine ⟨hstep n, ?_⟩
      intro i hi
      exact (one_lt_gcd_iff_prime_support_inter
        (u := a (n + 1)) (v := a i) (ha_pos (n + 1)) (ha_pos i)).1
        ((one_lt_gcd n).1.2 i hi)
    · intro m hm
      have hmpos : 0 < m := lt_trans (ha_pos n) hm.1
      refine (one_lt_gcd n).2 ⟨hm.1, ?_⟩
      intro i hi
      exact (one_lt_gcd_iff_prime_support_inter
        (u := m) (v := a i) hmpos (ha_pos i)).2 (hm.2 i hi)
  have hsmall : ∀ n, ∃ p, p.Prime ∧ p ≤ a 0 ∧ p ∣ a n ∧ p ∣ a (n + 1) :=
    small_prime_of_consecutive one_lt one_lt_gcd
  have hdiff : ∀ n, ∃ p, p.Prime ∧ p ≤ a 0 ∧
      p ∣ a (n + 1) - a n := by
    intro n
    obtain ⟨p, hp, hple, hpn, hpn1⟩ := hsmall n
    exact ⟨p, hp, hple, Nat.dvd_sub hpn1 hpn⟩
  have hmono_all : ∀ i j, i ≤ j → a i ≤ a j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | @step j hij ih =>
        exact le_trans ih (Nat.le_of_lt (hstep j))
  obtain ⟨K, D, hK, hchar0⟩ := finite_prefix_state_audit one_lt
  have hDnonzero : ∃ d ∈ D, d ≠ 0 := by
    have h1 : ∀ i ≤ 0, 1 < Nat.gcd (a 1) (a i) := by
      intro i hi
      have hmem := (one_lt_gcd 0).1
      exact hmem.2 i hi
    obtain ⟨d, hdD, hd⟩ := (hchar0 (a 1) (ha_pos 1)).1 h1
    refine ⟨d, hdD, ?_⟩
    intro hd0
    subst d
    have hz : a 1 = 0 := by simpa using hd
    have hlt : 1 < a 1 := one_lt 1
    omega
  let D' : Finset ℕ := D.erase 0
  have hchar0' : ∀ m, 0 < m →
      ((∀ i ≤ 0, 1 < Nat.gcd m (a i)) ↔ ∃ d ∈ D', d ∣ m) := by
    intro m hm
    constructor
    · intro hmad
      obtain ⟨d, hdD, hdm⟩ := (hchar0 m hm).1 hmad
      by_cases hd0 : d = 0
      · subst d
        have hz : m = 0 := by simpa using hdm
        omega
      · exact ⟨d, Finset.mem_erase.mpr ⟨hd0, hdD⟩, hdm⟩
    · rintro ⟨d, hdD, hdm⟩
      exact (hchar0 m hm).2 ⟨d, (Finset.mem_erase.mp hdD).2, hdm⟩
  let L : ℕ := ∏ d ∈ D', d
  have hLpos : 0 < L := by
    simpa [L, D'] using erased_product_pos hDnonzero
  have hDdiv : ∀ d ∈ D', d ∣ L := by
    intro d hd
    simpa [L] using (Finset.dvd_prod_of_mem (fun x : ℕ => x) hd)
  have hshift : ∀ m, (∃ d ∈ D', d ∣ m) ↔ ∃ d ∈ D', d ∣ m + L :=
    witness_family_shift_iff hDdiv
  have hfuture : ∀ i, ∃ d ∈ D', d ∣ a i :=
    future_initial_witness_of_pairwise_prefix one_lt hpair hchar0'
  let P : Finset ℕ := (a 0).primeFactors
  have hcanon : ∀ i, ∃ p ∈ P, p ∣ a i := by
    simpa [P] using (canonical_initial_prime_support one_lt one_lt_gcd)
  have hPnonempty : P.Nonempty := by
    obtain ⟨p, hpP, hp⟩ := hcanon 0
    exact ⟨p, hpP⟩
  -- consistency audit route: the exact premises admit the even affine model.
  sorry

end IMO2026P6
