import Mathlib

theorem LeanFlowProofs.PB018.parameters (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) (hbad : 3 * k + n + 2 * Nat.sqrt n + 3 < n ^ 2) (hregular : (n, k) ∉ ({(6, 7), (7, 7), (7, 9), (7, 10), (7, 11), (8, 13), (9, 9), (9, 11), (9, 12), (9, 15), (9, 16), (9, 17), (9, 18), (10, 20)} : Finset (ℕ × ℕ))) : let q : ℕ := n ^ 2 / k; let r : ℕ := n ^ 2 % k; ∃ u v : ℕ, 2 ≤ u ∧ 2 ≤ v ∧ u * v < n ∧ (if q % 2 = 0 then r else k - r) ≤ (n - 2 * ((n - 1) / u)) * (n - 2 * ((n - 1) / v)) ∧ ((n - 1) / u) * ((n - 1) / v) ≤ (k - r) * (q / 4) + r * ((q + 1) / 4) := by 
  dsimp only
  by_cases hn22 : n < 22
  · have finite : ∀ n : Fin 22, ∀ k : Fin (n.val ^ 2 / 3 + 1),
        5 ≤ n.val → 1 ≤ k.val →
        3 * k.val + n.val + 2 * Nat.sqrt n.val + 3 < n.val ^ 2 →
        (n.val, k.val) ∉ ({(6,7),(7,7),(7,9),(7,10),(7,11),(8,13),(9,9),(9,11),(9,12),(9,15),(9,16),(9,17),(9,18),(10,20)} : Finset (ℕ × ℕ)) →
        let u := Nat.sqrt (n.val - 1)
        let v := (n.val - 1) / u
        2 ≤ u ∧ 2 ≤ v ∧ u * v < n.val ∧
        (if (n.val ^ 2 / k.val) % 2 = 0 then n.val ^ 2 % k.val else k.val - n.val ^ 2 % k.val) ≤ (n.val - 2 * ((n.val - 1) / u)) * (n.val - 2 * ((n.val - 1) / v)) ∧
        ((n.val - 1) / u) * ((n.val - 1) / v) ≤ (k.val - n.val ^ 2 % k.val) * ((n.val ^ 2 / k.val) / 4) + (n.val ^ 2 % k.val) * (((n.val ^ 2 / k.val) + 1) / 4) := by
      decide +kernel
    refine ⟨Nat.sqrt (n - 1), (n - 1) / Nat.sqrt (n - 1), ?_⟩
    exact finite ⟨n, hn22⟩ ⟨k, by change k < n ^ 2 / 3 + 1; omega⟩ hn hk hbad hregular
  · have hnlarge : 22 ≤ n := by omega
    let t := Nat.sqrt (n - 1)
    let v := (n - 1) / t
    have ht : 4 ≤ t := Nat.le_sqrt.mpr (by omega)
    have htlo : t * t ≤ n - 1 := Nat.sqrt_le _
    have hthi : n - 1 < (t + 1) * (t + 1) := Nat.sqrt_lt.mp (by omega : Nat.sqrt (n - 1) < t + 1)
    have hvlo : t ≤ v := (Nat.le_div_iff_mul_le (by omega)).mpr htlo
    have hvhi : v ≤ t + 2 := by
      have : n - 1 < (t + 3) * t := by nlinarith only [hthi, ht]
      have := (Nat.div_lt_iff_lt_mul (by omega : 0 < t)).mpr this
      dsimp [v]
      omega
    have huv : t * v ≤ n - 1 := by simpa [v, Nat.mul_comm] using Nat.div_mul_le_self (n - 1) t
    have hnsub : n - 1 + 1 = n := by omega
    have hupper : n - 1 < t * (v + 1) := Nat.lt_mul_div_succ _ (by omega)
    have hj : (n - 1) / v = t := by
      apply Nat.div_eq_of_lt_le
      · exact huv
      · nlinarith only [hupper, hvlo]
    have hS : n ^ 2 ≤ 3 * ((n - 2 * v) * (n - 2 * t)) := by
      by_cases hn65 : n < 65
      · have finiteS : ∀ m : Fin 65, 22 ≤ m.val →
            m.val ^ 2 ≤ 3 * ((m.val - 2 * ((m.val - 1) / Nat.sqrt (m.val - 1))) * (m.val - 2 * Nat.sqrt (m.val - 1))) := by decide +kernel
        exact finiteS ⟨n, hn65⟩ hnlarge
      · have ht8 : 8 ≤ t := Nat.le_sqrt.mpr (by omega)
        have hscale : 6 * (t + 2) ≤ n := by nlinarith only [htlo, hnsub, ht8, Nat.mul_self_le_mul_self ht8]
        have ha : 2 * n ≤ 3 * (n - 2 * v) := by omega
        have hb : 2 * n ≤ 3 * (n - 2 * t) := by omega
        have hab := Nat.mul_le_mul ha hb
        nlinarith only [hab]
    refine ⟨t, v, by omega, by omega, by omega, ?_, ?_⟩
    · change (if (n ^ 2 / k) % 2 = 0 then n ^ 2 % k else k - n ^ 2 % k) ≤ (n - 2 * v) * (n - 2 * ((n - 1) / v))
      rw [hj]
      have hr := Nat.mod_lt (n ^ 2) (by omega : 0 < k)
      have hkrle : k - n ^ 2 % k ≤ k := Nat.sub_le _ _
      split_ifs <;> nlinarith only [hS, hbad, hr, hkrle]
    · change v * ((n - 1) / v) ≤ _
      rw [hj]
      let q := n ^ 2 / k
      let r := n ^ 2 % k
      have hr : r < k := Nat.mod_lt _ (by omega)
      have heq : r + k * q = n ^ 2 := Nat.mod_add_div _ _
      have hq : 3 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
      change v * t ≤ (k - r) * (q / 4) + r * ((q + 1) / 4)
      by_cases hq3 : q = 3
      · rw [hq3] at heq ⊢
        norm_num
        nlinarith only [heq, hbad, huv, hnsub]
      · have hq4 : 4 ≤ q := by omega
        have bound (c : ℕ) (hc : 4 ≤ c) : c ≤ 7 * (c / 4) := by omega
        have h1 := Nat.mul_le_mul_left (k - r) (bound q hq4)
        have h2 := Nat.mul_le_mul_left r (bound (q + 1) (by omega))
        have hkr : k - r + r = k := Nat.sub_add_cancel (by omega)
        have hsum : n ^ 2 ≤ 7 * ((k - r) * (q / 4) + r * ((q + 1) / 4)) := by nlinarith only [h1, h2, hkr, heq]
        nlinarith only [hsum, huv, hnlarge, hnsub]

