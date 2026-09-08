import LeanFlowProofs.PBAdvanced004.EdgeSideBranches
import LeanFlowProofs.PBAdvanced004.EdgeSides
import Mathlib

theorem LeanFlowProofs.PB004_threshold_separator
    {V : Type*} [Finite V]
    (g : SimpleGraph V) (is_tree : g.IsTree)
    (degree_bound : ∀ x : V, Nat.card (g.neighborSet x) ≤ 3)
    (k : ℕ) (k_pos : 0 < k) (card_bound : 3 * k ≤ Nat.card V) :
    let S : V → V → Set V := fun a b =>
      {x : V | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable b x}
    ∃ u v : V, g.Adj u v ∧
      k ≤ Nat.card (S u v) ∧
      Nat.card (S u v) ≤ 2 * k - 1 ∧
      k ≤ Nat.card (S v u) := by   classical
  intro S
  have hsum (a b : V) (h : g.Adj a b) :
      Nat.card (S a b) + Nat.card (S b a) = Nat.card V := by
    have hh := (LeanFlowProofs.PB004_edge_side_structure g is_tree a b h).2.2.1
    simpa only [S, Sym2.eq_swap, Nat.add_comm] using hh
  letI : Fintype V := Fintype.ofFinite V
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  obtain ⟨c, hac⟩ := (is_tree.connected.preconnected a b).nonempty_neighborSet_left hab
  have hex : ∃ m : ℕ, ∃ u v : V, g.Adj u v ∧ k ≤ Nat.card (S u v) ∧ Nat.card (S u v) = m := by
    have hs := hsum a c hac
    by_cases h : k ≤ Nat.card (S a c)
    · exact ⟨_, a, c, hac, h, rfl⟩
    · exact ⟨_, c, a, hac.symm, by omega, rfl⟩
  obtain ⟨u, v, huv, hlow, heq⟩ := Nat.find_spec hex
  have hbranches := LeanFlowProofs.PB004_edge_side_branches g is_tree degree_bound u v huv
  have hupper : Nat.card (S u v) ≤ 2 * k - 1 := by
    apply hbranches.2 k k_pos
    intro w hvw hwu
    change Nat.card (S v w) < k
    have hlt : Nat.card (S v w) < Nat.card (S u v) := by
      exact Set.ncard_lt_ncard (hbranches.1 w hvw hwu) (Set.toFinite _)
    by_contra hn
    have hm := Nat.find_min' hex (show ∃ a b : V, g.Adj a b ∧ k ≤ Nat.card (S a b) ∧ Nat.card (S a b) = Nat.card (S v w) from ⟨v, w, hvw, by omega, rfl⟩)
    omega
  exact ⟨u, v, huv, hlow, hupper, by have := hsum u v huv; omega⟩
