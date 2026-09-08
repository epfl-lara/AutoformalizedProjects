import Mathlib

theorem LeanFlowProofs.PB018.confinement (n k : ℕ) (hn : 1 ≤ n) {β : Type*} [DecidableEq β] (M : Fin n → Fin n → Fin k) (p : Fin n × Fin n → β) (hsize : ∀ b : β, (Finset.univ.filter (fun x : Fin n × Fin n => p x = b)).card < n) (hstep : ∀ x y : Fin n × Fin n, abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 → M x.1 x.2 ≠ M y.1 y.2 → p x = p y) (c : List (Fin n × Fin n)) (hc : c.Nodup) (hchain : c.Chain' (fun x y => abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 ∧ M x.1 x.2 ≠ M y.1 y.2)) : c.length < n := by 
  let R := fun x y : Fin n × Fin n => p x = p y
  letI : Trans R R R := ⟨fun h₁ h₂ => h₁.trans h₂⟩
  have he : c.IsChain R := hchain.imp (fun {x y} h => hstep x y h.1 h.2)
  cases c with
  | nil => exact Nat.lt_of_succ_le hn
  | cons a l =>
    have hp := List.pairwise_cons.mp he.pairwise
    have hs : (a :: l).toFinset ⊆ Finset.univ.filter (fun x => p x = p a) := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ x, ?_⟩
      rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hx
      · rfl
      · exact (hp.1 x hx).symm
    have hh := Finset.card_le_card hs
    rw [List.toFinset_card_of_nodup hc] at hh
    exact hh.trans_lt (hsize (p a))
