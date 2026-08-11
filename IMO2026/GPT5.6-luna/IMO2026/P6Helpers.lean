import Mathlib

namespace IMO2026P6

lemma no_common_prime_77_84_88 :
    ¬ ∃ p : ℕ, p.Prime ∧ p ∣ 77 ∧ p ∣ 84 ∧ p ∣ 88 := by
  rintro ⟨p, hp, h77, h84, h88⟩
  have hpg : p ∣ Nat.gcd 77 84 := Nat.dvd_gcd h77 h84
  norm_num at hpg
  have hp7 : p = 7 := by
    rcases ((Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hpg) with h | h
    · exact False.elim (hp.ne_one h)
    · exact h
  subst p
  norm_num at h88

lemma negation_audit_fin2_orbit
    (s : ℕ → Fin 2) (F : Fin 2 → Fin 2)
    (hF : ∀ n, s (n + 1) = F (s n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → s (n + T) = s n := by
  have hp : ∃ i j, i < j ∧ j ≤ 2 ∧ s i = s j := by
    by_contra h
    push Not at h
    have h01 := h 0 1 (by omega) (by omega)
    have h02 := h 0 2 (by omega) (by omega)
    have h12 := h 1 2 (by omega) (by omega)
    have h0 : (s 0).val < 2 := (s 0).isLt
    have h1 : (s 1).val < 2 := (s 1).isLt
    have h2 : (s 2).val < 2 := (s 2).isLt
    have h01' : (s 0).val ≠ (s 1).val := by
      intro h'
      exact h01 (Fin.ext h')
    have h02' : (s 0).val ≠ (s 2).val := by
      intro h'
      exact h02 (Fin.ext h')
    have h12' : (s 1).val ≠ (s 2).val := by
      intro h'
      exact h12 (Fin.ext h')
    omega
  obtain ⟨i, j, hij, hj2, hij_eq⟩ := hp
  let T := j - i
  have hT : 0 < T := by
    dsimp [T]
    omega
  have hprop : ∀ k, s (i + k) = s (j + k) := by
    intro k
    induction k with
    | zero => simpa using hij_eq
    | succ k ih =>
        calc
          s (i + Nat.succ k) = s ((i + k) + 1) := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
          _ = F (s (i + k)) := hF (i + k)
          _ = F (s (j + k)) := congrArg F ih
          _ = s ((j + k) + 1) := (hF (j + k)).symm
          _ = s (j + Nat.succ k) := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
  refine ⟨i, T, hT, ?_⟩
  intro n hn
  have hn' : ∃ k, n = i + k := by
    refine ⟨n - i, ?_⟩
    omega
  obtain ⟨k, rfl⟩ := hn'
  have hk := hprop k
  have hidx : i + k + T = j + k := by
    dsimp [T]
    omega
  rw [hidx]
  exact hk.symm

lemma first_step_eq_minFac {a : ℕ → ℕ}
    (one_lt : ∀ i, 1 < a i)
    (one_lt_gcd : ∀ n, IsLeast
      {m | a n < m ∧ ∀ i ≤ n, 1 < Nat.gcd m (a i)}
      (a (n + 1))) :
    a 1 = a 0 + (a 0).minFac := by
  have h0lt := one_lt 0
  have ha0ne : a 0 ≠ 1 := by omega
  have ha0pos : 0 < a 0 := by omega
  let p := (a 0).minFac
  have hp : p.Prime := by
    dsimp [p]
    exact Nat.minFac_prime ha0ne
  have hpa0 : p ∣ a 0 := by
    dsimp [p]
    exact Nat.minFac_dvd _
  have hppos := hp.pos
  have hcand : a 0 + p ∈
      {m | a 0 < m ∧ ∀ i ≤ 0, 1 < Nat.gcd m (a i)} := by
    constructor
    · omega
    · intro i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      have hpm : p ∣ a 0 + p := dvd_add hpa0 (dvd_refl p)
      have hpg : p ∣ Nat.gcd (a 0 + p) (a 0) := Nat.dvd_gcd hpm hpa0
      have hgpos : 0 < Nat.gcd (a 0 + p) (a 0) :=
        Nat.gcd_pos_of_pos_right _ ha0pos
      exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpg)
  have hle : a 1 ≤ a 0 + p := (one_lt_gcd 0).2 hcand
  have hmem := (one_lt_gcd 0).1
  have hgt : a 0 < a 1 := hmem.1
  have hgc : 1 < Nat.gcd (a 1) (a 0) := hmem.2 0 (by omega)
  obtain ⟨q, hq, hqg⟩ := Nat.exists_prime_and_dvd
    (by omega : Nat.gcd (a 1) (a 0) ≠ 1)
  have hqa1 : q ∣ a 1 := dvd_trans hqg (Nat.gcd_dvd_left _ _)
  have hqa0 : q ∣ a 0 := dvd_trans hqg (Nat.gcd_dvd_right _ _)
  have hqle : p ≤ q := by
    dsimp [p]
    exact Nat.minFac_le_of_dvd hq.two_le hqa0
  have hqdiff : q ∣ a 1 - a 0 := Nat.dvd_sub hqa1 hqa0
  have hdiffpos : 0 < a 1 - a 0 := by omega
  have hdiffge : q ≤ a 1 - a 0 := Nat.le_of_dvd hdiffpos hqdiff
  omega

lemma finite_prefix_gcd_family
    {a : ℕ → ℕ} {N : ℕ}
    (hpos : ∀ i, 0 < a i) :
    ∃ K : ℕ, ∃ D : Finset ℕ,
      0 < K ∧
      ∀ m, 0 < m →
        ((∀ i ≤ N, 1 < Nat.gcd m (a i)) ↔
          ∃ d ∈ D, d ∣ m) := by
  let K : ℕ := Finset.prod (Finset.range (N + 1)) a
  have hK : 0 < K := by
    dsimp [K]
    exact Finset.prod_pos (by
      intro i hi
      exact hpos i)
  let D : Finset ℕ :=
    (Finset.Icc 1 K).filter (fun d => ∀ i ≤ N, 1 < Nat.gcd d (a i))
  refine ⟨K, D, hK, ?_⟩
  intro m hmpos
  constructor
  · intro hall
    let d := Nat.gcd m K
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.gcd_pos_of_pos_left _ hmpos
    have hdone : 1 ≤ d := by omega
    have hdk : d ≤ K := by
      dsimp [d]
      exact Nat.gcd_le_right m hK
    have hdi : ∀ i ≤ N, 1 < Nat.gcd d (a i) := by
      intro i hi
      have hgi := hall i hi
      have hgne : Nat.gcd m (a i) ≠ 1 := by omega
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgne
      have hpm : p ∣ m := dvd_trans hpg (Nat.gcd_dvd_left _ _)
      have hpi : p ∣ a i := dvd_trans hpg (Nat.gcd_dvd_right _ _)
      have hi' : i < N + 1 := by omega
      have hprod : a i ∣ K := by
        dsimp [K]
        exact Finset.dvd_prod_of_mem a (Finset.mem_range.mpr hi')
      have hpK : p ∣ K := dvd_trans hpi hprod
      have hpd : p ∣ d := by
        dsimp [d]
        exact Nat.dvd_gcd hpm hpK
      have hpgcd : p ∣ Nat.gcd d (a i) := Nat.dvd_gcd hpd hpi
      have hgpos : 0 < Nat.gcd d (a i) :=
        Nat.gcd_pos_of_pos_right _ (hpos i)
      exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpgcd)
    have hdD : d ∈ D := by
      dsimp [D]
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hdone, hdk⟩, hdi⟩
    refine ⟨d, hdD, ?_⟩
    dsimp [d]
    exact Nat.gcd_dvd_left _ _
  · rintro ⟨d, hdD, hdm⟩
    have hdD' : d ∈ (Finset.Icc 1 K).filter
        (fun d => ∀ i ≤ N, 1 < Nat.gcd d (a i)) := by
      simpa [D] using hdD
    have hdi := (Finset.mem_filter.mp hdD').2
    intro i hi
    have hgi := hdi i hi
    have hgne : Nat.gcd d (a i) ≠ 1 := by omega
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hgne
    have hpd : p ∣ d := dvd_trans hpg (Nat.gcd_dvd_left _ _)
    have hpi : p ∣ a i := dvd_trans hpg (Nat.gcd_dvd_right _ _)
    have hpm : p ∣ m := dvd_trans hpd hdm
    have hpgcd : p ∣ Nat.gcd m (a i) := Nat.dvd_gcd hpm hpi
    have hgpos : 0 < Nat.gcd m (a i) :=
      Nat.gcd_pos_of_pos_right _ (hpos i)
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hgpos hpgcd)

lemma witness_transition_periodic
    {D : Finset ℕ} {L : ℕ}
    (hDdiv : ∀ d ∈ D, d ∣ L) :
    ∀ m, (∃ d ∈ D, d ∣ m) ↔ ∃ d ∈ D, d ∣ m + L := by
  intro m
  constructor
  · rintro ⟨d, hdD, hdm⟩
    exact ⟨d, hdD, dvd_add hdm (hDdiv d hdD)⟩
  · rintro ⟨d, hdD, hdmL⟩
    have hdm' : d ∣ (m + L) - L :=
      Nat.dvd_sub hdmL (hDdiv d hdD)
    have heq : (m + L) - L = m := Nat.add_sub_cancel m L
    rw [heq] at hdm'
    exact ⟨d, hdD, hdm'⟩

lemma finite_state_eventual_periodic
    {q : ℕ} (s : ℕ → Fin q) (F : Fin q → Fin q)
    (hF : ∀ n, s (n + 1) = F (s n)) :
    ∃ N T, 0 < T ∧ ∀ n, N ≤ n → s (n + T) = s n := by
  have hp : ∃ i j, i < j ∧ j ≤ q ∧ s i = s j := by
    by_contra h
    push Not at h
    let f : Fin (q + 1) → Fin q := fun k => s k.val
    have hf_inj : Function.Injective f := by
      intro x y hxy
      by_contra hne
      have hv : x.val ≠ y.val := by
        intro hv
        exact hne (Fin.ext hv)
      rcases lt_or_gt_of_ne hv with hlt | hlt
      · have hyq : y.val ≤ q := by omega
        exact h x.val y.val hlt hyq (by simpa [f] using hxy)
      · have hxq : x.val ≤ q := by omega
        exact h y.val x.val hlt hxq (by simpa [f] using hxy.symm)
    have hc := Fintype.card_le_of_injective f hf_inj
    simp at hc
  obtain ⟨i, j, hij, hjq, hij_eq⟩ := hp
  let T := j - i
  have hT : 0 < T := by
    dsimp [T]
    omega
  have hprop : ∀ k, s (i + k) = s (j + k) := by
    intro k
    induction k with
    | zero => simpa using hij_eq
    | succ k ih =>
        calc
          s (i + Nat.succ k) = s ((i + k) + 1) := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
          _ = F (s (i + k)) := hF (i + k)
          _ = F (s (j + k)) := congrArg F ih
          _ = s ((j + k) + 1) := (hF (j + k)).symm
          _ = s (j + Nat.succ k) := by
            simp [Nat.succ_eq_add_one, Nat.add_assoc]
  refine ⟨i, T, hT, ?_⟩
  intro n hn
  have hn' : ∃ k, n = i + k := by
    refine ⟨n - i, ?_⟩
    omega
  obtain ⟨k, rfl⟩ := hn'
  have hk := hprop k
  have hidx : i + k + T = j + k := by
    dsimp [T]
    omega
  rw [hidx]
  exact hk.symm

lemma greedy_history_product_witness
    {S : Finset ℕ} {x : ℕ}
    (hx : x ∈ S) (hS : ∀ y ∈ S, 1 < y) :
    ∃ m, x < m ∧ ∀ y ∈ S, 1 < Nat.gcd m y := by
  let P := ∏ y ∈ S, y
  let M := (x + 1) * P
  refine ⟨M, ?_, ?_⟩
  · have hPpos : 0 < P := by
      dsimp [P]
      exact Finset.prod_pos (fun y hy => by
        have hy' := hS y hy
        omega)
    have hxpos := hS x hx
    dsimp [M]
    nlinarith
  · intro y hy
    have hyd : y ∣ P := by
      dsimp [P]
      simpa using (Finset.dvd_prod_of_mem (fun z : ℕ => z) hy)
    have hydM : y ∣ M := by
      exact dvd_mul_of_dvd_right hyd (x + 1)
    have hgy : y ∣ Nat.gcd M y := Nat.dvd_gcd hydM (dvd_refl y)
    have hylt := hS y hy
    have hypos : 0 < y := by omega
    have hgpos : 0 < Nat.gcd M y := Nat.gcd_pos_of_pos_right M hypos
    have hle : y ≤ Nat.gcd M y := Nat.le_of_dvd hgpos hgy
    omega

lemma greedy_history_product_witness_map
    {S : Finset ℕ} {x : ℕ} {f : ℕ → ℕ}
    (hx : x ∈ S) (hS : ∀ y ∈ S, 1 < f y) :
    ∃ m, f x < m ∧ ∀ y ∈ S, 1 < Nat.gcd m (f y) := by
  let P := ∏ y ∈ S, f y
  let M := (f x + 1) * P
  refine ⟨M, ?_, ?_⟩
  · have hPpos : 0 < P := by
      dsimp [P]
      exact Finset.prod_pos (fun y hy => by
        have hy' := hS y hy
        omega)
    have hxpos := hS x hx
    dsimp [M]
    nlinarith
  · intro y hy
    have hyd : f y ∣ P := by
      dsimp [P]
      simpa using (Finset.dvd_prod_of_mem (fun z : ℕ => f z) hy)
    have hydM : f y ∣ M := by
      exact dvd_mul_of_dvd_right hyd (f x + 1)
    have hgy : f y ∣ Nat.gcd M (f y) :=
      Nat.dvd_gcd hydM (dvd_refl (f y))
    have hylt := hS y hy
    have hypos : 0 < f y := by omega
    have hgpos : 0 < Nat.gcd M (f y) :=
      Nat.gcd_pos_of_pos_right M hypos
    have hle : f y ≤ Nat.gcd M (f y) := Nat.le_of_dvd hgpos hgy
    omega

end IMO2026P6
