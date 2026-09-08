import Mathlib

theorem LeanFlow.PBBasic029.pair_count
    (p n : ℕ) (hpn : p + 2 ≤ n) :
    {ij : Fin n × Fin n |
      ij.1.val < ij.2.val ∧
      ij.1.val + (n - 1 - ij.2.val) ≤ p}.encard =
      (((p + 1) * (p + 2) / 2 : ℕ) : ENat) := by classical
  let S := {ij : Fin n × Fin n | ij.1.val < ij.2.val ∧ ij.1.val + (n - 1 - ij.2.val) ≤ p}
  let e : S ≃ (d : Fin (p+1)) × Fin (d.val+1) :=
    { toFun := fun x => ⟨⟨x.val.1.val + (n-1-x.val.2.val), by have := x.property; dsimp [S] at this; omega⟩, ⟨x.val.1.val, by dsimp; omega⟩⟩
      invFun := fun x => ⟨(⟨x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩, ⟨n-1-x.1.val+x.2.val, by have := x.1.isLt; have := x.2.isLt; omega⟩), by
        have := x.1.isLt; have := x.2.isLt
        dsimp [S]
        constructor <;> omega⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp
        have := x.val.2.isLt; have := x.property; dsimp [S] at this; omega
      right_inv := by
        intro x
        apply Sigma.ext
        · apply Fin.ext
          dsimp
          have := x.1.isLt; have := x.2.isLt
          omega
        · have hh : ∀ {a b : ℕ} (h : a = b) (i : Fin a) (j : Fin b), i.val = j.val → HEq i j := by
            intro a b h i j hij
            subst b
            exact heq_of_eq (Fin.ext hij)
          apply hh
          · dsimp
            have := x.1.isLt; have := x.2.isLt
            omega
          · rfl }
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma, Fintype.card_fin] at hc
  have hs : ∀ m : ℕ, 2 * (∑ i : Fin m, (i.val + 1)) = m * (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      nlinarith
  have ht : (∑ i : Fin (p+1), (i.val+1)) = (p+1)*(p+2)/2 := by
    have h := hs (p+1)
    change 2 * (∑ i : Fin (p+1), (i.val+1)) = (p+1)*(p+2) at h
    rw [← h]
    omega
  rw [Set.encard_eq_coe_toFinset_card]
  have hf : S.toFinset.card = Fintype.card S := by simp
  change (S.toFinset.card : ENat) = _
  rw [hf, hc, ht]
