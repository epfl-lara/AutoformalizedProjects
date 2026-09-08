import LeanFlowProofs.PB018GridCover
import Mathlib

theorem LeanFlowProofs.PB018.no_mono_path (n k : ℕ) (hn : 2 ≤ n) (M : Fin n → Fin n → Fin k) (hmono : ∀ y₀ y₁ x₀ x₁ : Fin n, y₁.val = y₀.val + 1 → x₁.val = x₀.val + 1 → ¬ (M y₀ x₀ = M y₀ x₁ ∧ M y₀ x₀ = M y₁ x₀ ∧ M y₀ x₀ = M y₁ x₁)) : ∃ c : List (Fin n × Fin n), c.Nodup ∧ c.length = n ∧ c.Chain' (fun a b => abs ((a.2 : ℤ) - (b.2 : ℤ)) + abs ((a.1 : ℤ) - (b.1 : ℤ)) = 1 ∧ M a.1 a.2 ≠ M b.1 b.2) := by classical
  let G : SimpleGraph (Fin n × Fin n) := {
    Adj := fun a b => abs ((a.2 : ℤ) - (b.2 : ℤ)) + abs ((a.1 : ℤ) - (b.1 : ℤ)) = 1 ∧ M a.1 a.2 ≠ M b.1 b.2
    symm := ⟨by intro a b h; exact ⟨by simpa only [abs_sub_comm] using h.1, Ne.symm h.2⟩⟩
    loopless := ⟨by intro a h; exact h.2 rfl⟩ }
  let p := G.connectedComponentMk
  set_option maxHeartbeats 2000000 in
  have hsquare : ∀ y₀ y₁ x₀ x₁ : Fin n, y₁.val = y₀.val + 1 → x₁.val = x₀.val + 1 → ({p (y₀, x₀), p (y₀, x₁), p (y₁, x₀), p (y₁, x₁)} : Finset G.ConnectedComponent).card ≤ 2 := by
    intro y₀ y₁ x₀ x₁ hy hx
    have hy' : (y₁ : ℤ) = (y₀ : ℤ) + 1 := by exact_mod_cast hy
    have hx' : (x₁ : ℤ) = (x₀ : ℤ) + 1 := by exact_mod_cast hx
    have edge (a b : Fin n × Fin n) (h : abs ((a.2 : ℤ) - (b.2 : ℤ)) + abs ((a.1 : ℤ) - (b.1 : ℤ)) = 1) : p a ≠ p b → M a.1 a.2 = M b.1 b.2 := by
      intro hp
      by_contra hc
      exact hp (SimpleGraph.ConnectedComponent.sound (show G.Adj a b from ⟨h, hc⟩).reachable)
    have e₁ := edge (y₀,x₀) (y₀,x₁) (by dsimp; rw [hx']; ring_nf; simp)
    have e₂ := edge (y₀,x₀) (y₁,x₀) (by dsimp; rw [hy']; ring_nf; simp)
    have e₃ := edge (y₀,x₁) (y₁,x₁) (by dsimp; rw [hy']; ring_nf; simp)
    have e₄ := edge (y₁,x₀) (y₁,x₁) (by dsimp; rw [hx']; ring_nf; simp)
    have hm := hmono y₀ y₁ x₀ x₁ hy hx
    clear hmono edge hy' hx' hy hx hn
    by_cases h₁ : p (y₀,x₀) = p (y₀,x₁) <;>
      by_cases h₂ : p (y₀,x₀) = p (y₁,x₀) <;>
      by_cases h₃ : p (y₀,x₀) = p (y₁,x₁) <;>
      by_cases h₄ : p (y₀,x₁) = p (y₁,x₀) <;>
      by_cases h₅ : p (y₀,x₁) = p (y₁,x₁) <;>
      by_cases h₆ : p (y₁,x₀) = p (y₁,x₁) <;>
      simp_all only [Finset.card_insert_of_notMem, Finset.mem_insert, Finset.mem_singleton, Finset.insert_eq_of_mem, Finset.mem_singleton_self, Finset.card_singleton, not_false_eq_true, not_true_eq_false, or_self, or_false, false_or, implies_true, false_implies, true_implies, Nat.reduceAdd, Nat.reduceLeDiff] <;> aesop
  have bound (f : Fin n × Fin n → ℤ) (hf : ∀ a b, G.Adj a b → f b - f a ≤ 1) {a b} (w : G.Walk a b) : f b - f a ≤ w.length := by
    induction w with
    | nil => simp
    | @cons a d b h w ih =>
      have hh := hf a d h
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      omega
  have finish (a b : Fin n × Fin n) (hab : p a = p b) (f : Fin n × Fin n → ℤ) (hf : ∀ a b, G.Adj a b → f b - f a ≤ 1) (ha : f a = 0) (hb : f b + 1 = n) : ∃ c : List (Fin n × Fin n), c.Nodup ∧ c.length = n ∧ c.IsChain G.Adj := by
    obtain ⟨w, hw⟩ := (SimpleGraph.ConnectedComponent.exact hab).exists_isPath
    have hh := bound f hf w
    have hl : n ≤ w.support.length := by
      rw [SimpleGraph.Walk.length_support]
      omega
    exact ⟨w.support.take n, hw.support_nodup.take, by rw [List.length_take, Nat.min_eq_left hl], w.isChain_adj_support.take n⟩
  have hf₁ : ∀ a b, G.Adj a b → (b.1 : ℤ) - (a.1 : ℤ) ≤ 1 := by
    intro a b h
    have h₀ := h.1
    have h₁ := abs_nonneg ((a.2 : ℤ) - (b.2 : ℤ))
    have h₂ := neg_le_abs ((a.1 : ℤ) - (b.1 : ℤ))
    omega
  have hf₂ : ∀ a b, G.Adj a b → (b.2 : ℤ) - (a.2 : ℤ) ≤ 1 := by
    intro a b h
    have h₀ := h.1
    have h₁ := abs_nonneg ((a.1 : ℤ) - (b.1 : ℤ))
    have h₂ := neg_le_abs ((a.2 : ℤ) - (b.2 : ℤ))
    omega
  rcases LeanFlowProofs.PB018.grid_cover n hn p hsquare with ⟨a,b,hab,ha,hb⟩ | ⟨a,b,hab,ha,hb⟩
  · exact finish a b hab (fun a => (a.1 : ℤ)) hf₁ (by exact_mod_cast ha) (by exact_mod_cast hb)
  · exact finish a b hab (fun a => (a.2 : ℤ)) hf₂ (by exact_mod_cast ha) (by exact_mod_cast hb)
