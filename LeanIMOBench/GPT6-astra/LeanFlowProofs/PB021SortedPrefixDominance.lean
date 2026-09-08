import Mathlib

theorem LeanFlow.pb021_sorted_prefix_dominance {d : ℕ} (v s : Fin d → ℕ) (hperm : ∃ e : Equiv.Perm (Fin d), ∀ i : Fin d, s i = v (e i)) (hs : Antitone s) (K : ℕ) (hK : K ≤ d) : ((Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => v i) ≤ (Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => s i)) ∧ (((Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => v i) = (Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => s i)) ↔ ∀ i j : Fin d, i.val < K → K ≤ j.val → v j ≤ v i) := by classical
  have maximal (f : Fin d → ℕ) (P Q : Finset (Fin d))
      (hc : Q.card = P.card)
      (ht : ∀ i ∈ P, ∀ j, j ∉ P → f j ≤ f i) : Q.sum f ≤ P.sum f := by
    have hd : (Q \ P).card = (P \ Q).card := Finset.card_sdiff_comm hc
    have hh : (P \ Q).card * (Q \ P).sum f ≤ (Q \ P).card * (P \ Q).sum f := by
      calc
        _ = (Q \ P).sum (fun j => (P \ Q).sum (fun _ => f j)) := by simp [Finset.mul_sum]
        _ ≤ (Q \ P).sum (fun _ => (P \ Q).sum f) := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro i hi
          exact ht i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
        _ = _ := by simp
    have hdiff : (Q \ P).sum f ≤ (P \ Q).sum f := by
      by_cases hz : (P \ Q).card = 0
      · have : Q \ P = ∅ := Finset.card_eq_zero.mp (hd.trans hz)
        simp [this]
      · rw [hd] at hh
        exact (mul_le_mul_iff_right₀ (Nat.pos_of_ne_zero hz)).mp (by simpa [Nat.mul_comm] using hh)
    have h1 := Finset.sum_inter_add_sum_sdiff Q P f
    have h2 := Finset.sum_inter_add_sum_sdiff P Q f
    change (Q ∩ P).sum f + (Q \ P).sum f = Q.sum f at h1
    change (P ∩ Q).sum f + (P \ Q).sum f = P.sum f at h2
    rw [Finset.inter_comm Q P] at h1
    omega
  let P := Finset.univ.filter (fun i : Fin d => i.val < K)
  have memP (i : Fin d) : i ∈ P ↔ i.val < K := by simp [P]
  obtain ⟨e, he⟩ := hperm
  have top : ∀ i ∈ P, ∀ j, j ∉ P → s j ≤ s i := by
    intro i hi j hj
    apply hs
    have := (memP i).mp hi
    have : ¬j.val < K := fun h => hj ((memP j).mpr h)
    exact Fin.le_iff_val_le_val.mpr (by omega)
  have bound (Q : Finset (Fin d)) (hc : Q.card = P.card) : Q.sum v ≤ P.sum s := by
    let R := Q.image e.symm
    have hR : R.card = P.card := by simpa [R, Finset.card_image_of_injective, e.symm.injective] using hc
    have hsum : R.sum s = Q.sum v := by
      dsimp [R]
      rw [Finset.sum_image (by intro a ha b hb h; exact e.symm.injective h)]
      simp only [he, e.apply_symm_apply]
    rw [← hsum]
    exact maximal s P R hR top
  have hb := bound P rfl
  change P.sum v ≤ P.sum s ∧ (P.sum v = P.sum s ↔ _)
  refine ⟨hb, ?_⟩
  constructor
  · intro heq i j hi hj
    have hiP := (memP i).mpr hi
    have hjP : j ∉ P := by rw [memP]; omega
    let Q := insert j (P.erase i)
    have hjE : j ∉ P.erase i := fun h => hjP (Finset.mem_of_mem_erase h)
    have hc : Q.card = P.card := by
      simp only [Q, Finset.card_insert_of_notMem hjE, Finset.card_erase_of_mem hiP]
      have := Finset.card_pos.mpr ⟨i, hiP⟩
      omega
    have h := bound Q hc
    have hsum : Q.sum v = v j + (P.erase i).sum v := Finset.sum_insert hjE
    have hiSum := Finset.sum_erase_add P v hiP
    change (P.erase i).sum v + v i = P.sum v at hiSum
    rw [hsum, ← heq] at h
    omega
  · intro ht
    apply Nat.le_antisymm hb
    have ht' : ∀ i ∈ P, ∀ j, j ∉ P → v j ≤ v i := by
      intro i hi j hj
      apply ht i j ((memP i).mp hi)
      have : ¬j.val < K := fun h => hj ((memP j).mpr h)
      omega
    have h := maximal v P (P.image e) (Finset.card_image_of_injective _ e.injective) ht'
    have hsum : (P.image e).sum v = P.sum s := by
      rw [Finset.sum_image (by intro a ha b hb h; exact e.injective h)]
      simp only [he]
    rwa [hsum] at h
