import LeanFlowProofs.PBAdvanced018.Confinement
import LeanFlowProofs.PBAdvanced018.Pack124
import LeanFlowProofs.PBAdvanced018.Parameters
import LeanFlowProofs.PBAdvanced018.RectangleAtoms
import LeanFlowProofs.PBAdvanced018.SmallCertificates
import Mathlib

theorem LeanFlowProofs.PB018.countercoloring (n k : ℕ) (hn : 5 ≤ n) (hk : 1 ≤ k) (hbad : 3 * k + n + 2 * Nat.sqrt n + 3 < n ^ 2) : ∃ M : Fin n → Fin n → Fin k, (∀ i : Fin k, (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k ∨ (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k + 1) ∧ (∀ c : List (Fin n × Fin n), c.Nodup → c.Chain' (fun x y => abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 ∧ M x.1 x.2 ≠ M y.1 y.2) → c.length < n) := by classical
  by_cases he : (n, k) ∈ ({(6, 7), (7, 7), (7, 9), (7, 10), (7, 11), (8, 13), (9, 9), (9, 11), (9, 12), (9, 15), (9, 16), (9, 17), (9, 18), (10, 20)} : Finset (ℕ × ℕ))
  · obtain ⟨M, p, hb, hs, ht⟩ := small_certificates n k he
    exact ⟨M, hb, fun c hc ht' => confinement n k (by omega) M p hs ht c hc ht'⟩
  obtain ⟨u, v, hu, hv, huv, hsingle, hfour⟩ := parameters n k hn hk hbad he
  obtain ⟨b, hw, htotal, hs, hf, hsize, hstep⟩ := rectangle_atoms n u v (by omega) hu hv
  let q := n ^ 2 / k
  let r := n ^ 2 % k
  have hr : r < k := Nat.mod_lt _ (by omega)
  have hdiv : r + k * q = n ^ 2 := Nat.mod_add_div _ _
  let c : Fin k → ℕ := fun i => if i.val < r then q + 1 else q
  have hcard : (Finset.univ.filter (fun i : Fin k => i.val < r)).card = r := by
    have heq : Finset.univ.filter (fun i : Fin k => i.val < r) = (Finset.univ : Finset (Fin r)).map ⟨fun i : Fin r => (⟨i.val, lt_trans i.isLt hr⟩ : Fin k), fun a b h => Fin.ext (congrArg (fun x : Fin k => x.val) h)⟩ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro hi
        exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.isLt
    rw [heq, Finset.card_map]
    simp
  have hcard' : (Finset.univ.filter (fun i : Fin k => ¬i.val < r)).card = k - r := by
    have h := (Finset.univ : Finset (Fin k)).card_filter_add_card_filter_not (fun i => i.val < r)
    rw [hcard, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hsum (a d : ℕ) : (∑ i : Fin k, if i.val < r then a else d) = r * a + (k - r) * d := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, smul_eq_mul, hcard, hcard']
  have hcTotal : (∑ i, c i) = n ^ 2 := by
    dsimp [c]
    rw [hsum]
    have : k - r + r = k := Nat.sub_add_cancel (by omega)
    nlinarith
  have hcOdd : (Finset.univ.filter (fun i => c i % 2 = 1)).card = if q % 2 = 0 then r else k - r := by
    by_cases hq : q % 2 = 0
    · have hq' : (q + 1) % 2 = 1 := by omega
      rw [if_pos hq, ← hcard]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, c]
      split_ifs with hi <;> simp [hi, hq, hq']
    · have hq' : q % 2 = 1 := by omega
      have hq'' : (q + 1) % 2 = 0 := by omega
      rw [if_neg hq, ← hcard']
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, c]
      split_ifs with hi <;> simp [hi, hq', hq'']
  have hcFour : (∑ i, c i / 4) = (k - r) * (q / 4) + r * ((q + 1) / 4) := by
    simp only [c, ite_div]
    rw [hsum, Nat.add_comm]
  let w := fun a => (Finset.univ.filter (fun x : Fin n × Fin n => b x = a)).card
  obtain ⟨f, hpack⟩ := pack124 _ k hk w c hw (htotal.trans hcTotal.symm)
    (by rw [hcOdd, hs]; exact hsingle) (by rw [hf, hcFour]; exact hfour)
  refine ⟨fun y x => f (b (y, x)), ?_, ?_⟩
  · intro i
    have hcount : (Finset.univ.filter (fun x : Fin n × Fin n => f (b x) = i)).card = c i := by
      rw [← hpack i]
      symm
      simpa [w] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n × Fin n)) (Finset.univ.filter (fun a => f a = i)) b
    change _ = q ∨ _ = q + 1
    rw [hcount]
    dsimp [c]
    split_ifs <;> simp
  · apply confinement n k (by omega) (fun y x => f (b (y, x))) (fun x => (x.1.val / u, x.2.val / v))
    · rintro ⟨a, d⟩
      have hh := hsize a d
      simpa only [Prod.mk.injEq] using lt_of_le_of_lt hh huv
    · intro x y hxy hne
      by_contra h
      exact hne (congrArg f (hstep x y hxy h))
