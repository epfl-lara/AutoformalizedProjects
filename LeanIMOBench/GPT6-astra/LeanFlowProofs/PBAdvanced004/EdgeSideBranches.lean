import LeanFlowProofs.PBAdvanced004.EdgeSides
import Mathlib

theorem LeanFlowProofs.PB004_edge_side_branches
    {V : Type*} [Finite V]
    (g : SimpleGraph V) (is_tree : g.IsTree)
    (degree_bound : ∀ x : V, Nat.card (g.neighborSet x) ≤ 3)
    (u v : V) (huv : g.Adj u v) :
    let S : V → V → Set V := fun a b =>
      {x : V | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable b x}
    (∀ w : V, g.Adj v w → w ≠ u → S v w ⊂ S u v) ∧
      (∀ k : ℕ, 0 < k →
        (∀ w : V, g.Adj v w → w ≠ u → Nat.card (S v w) < k) →
        Nat.card (S u v) ≤ 2 * k - 1) := by classical
  letI := Fintype.ofFinite V
  dsimp only
  let S : V → V → Set V := fun a b =>
    {x | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable b x}
  change (∀ w, g.Adj v w → w ≠ u → S v w ⊂ S u v) ∧ _
  have reflS (a b : V) : b ∈ S a b := SimpleGraph.Reachable.rfl
  have notS (a b : V) (hab : g.Adj a b) : a ∉ S a b := by
    have h := (PB004_edge_side_structure g is_tree a b hab).1
    exact fun ha => Set.disjoint_left.mp h SimpleGraph.Reachable.rfl ha
  have exit (a b : V) (hab : g.Adj a b) (x y : V)
      (hx : x ∈ S a b) (hy : y ∉ S a b) (hxy : g.Adj x y) : x = b ∧ y = a := by
    obtain ⟨hd, hp, hc, ht, ht', hb⟩ := PB004_edge_side_structure g is_tree a b hab
    have hy' : (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable a y := by
      have : y ∈ ({z | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable a z} ∪ S a b) := by
        rw [show {z | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 V))).Reachable a z} ∪ S a b = Set.univ from hp]
        trivial
      exact this.resolve_right hy
    exact (hb y x hy' hx hxy.symm).symm
  have closed {G : SimpleGraph V} (T : Set V)
      (hc : ∀ x ∈ T, ∀ y, G.Adj x y → y ∈ T)
      {a b : V} (ha : a ∈ T) (hr : G.Reachable a b) : b ∈ T := by
    obtain ⟨p⟩ := hr
    induction p with
    | nil => exact ha
    | cons h p ih => exact ih (hc _ ha _ h)
  have sub (w : V) (hw : g.Adj v w) (hwu : w ≠ u) : S v w ⊆ S u v := by
    have hv : v ∉ S v w := notS v w hw
    have hu : u ∉ S v w := by
      intro hu
      have := exit v w hw u v hu hv huv
      exact hwu this.1.symm
    intro x hx
    have hstart : w ∈ S u v := by
      apply SimpleGraph.Adj.reachable
      simp [SimpleGraph.deleteEdges, hw, hwu, huv.ne.symm, hw.ne.symm]
    have hh : x ∈ S v w ∩ S u v := by
      apply closed (S v w ∩ S u v) _ ⟨reflS v w, hstart⟩ hx
      intro a ha b hab
      refine ⟨ha.1.trans hab.reachable, ?_⟩
      by_cases hb : b ∈ S u v
      · exact hb
      have he := exit u v huv a b ha.2 hb hab.1
      exact (hv (he.1 ▸ ha.1)).elim
    exact hh.2
  constructor
  · intro w hw hwu
    exact Set.ssubset_iff_subset_ne.mpr ⟨sub w hw hwu, by
      intro he
      exact notS v w hw (he ▸ reflS u v)⟩
  · intro k hk hsmall
    change Nat.card (S u v) ≤ 2 * k - 1
    change ∀ w, g.Adj v w → w ≠ u → Nat.card (S v w) < k at hsmall
    let N : Finset V := (g.neighborSet v).toFinset.erase u
    have memN (w : V) : w ∈ N ↔ g.Adj v w ∧ w ≠ u := by
      simp [N, and_comm]
    have cover : S u v ⊆ {v} ∪ ⋃ w ∈ (N : Set V), S v w := by
      intro x hx
      apply closed ({v} ∪ ⋃ w ∈ (N : Set V), S v w) _ (Or.inl rfl) hx
      intro a ha b hab
      rcases ha with ha | ha
      · have hav : a = v := ha
        subst a
        by_cases hb : b = u
        · subst b
          have : ¬ (g.deleteEdges ({Sym2.mk u v} : Set (Sym2 V))).Adj v u := by
            simp [SimpleGraph.deleteEdges, huv.ne.symm]
          exact (this hab).elim
        · exact Or.inr (Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨(memN b).mpr ⟨hab.1, hb⟩, reflS v b⟩⟩)
      · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp ha
        obtain ⟨hwN, haw⟩ := Set.mem_iUnion.mp hw
        by_cases hb : b ∈ S v w
        · exact Or.inr (Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hwN, hb⟩⟩)
        · have he := exit v w ((memN w).mp hwN).1 a b haw hb hab.1
          exact Or.inl he.2
    have ncard : N.card ≤ 2 := by
      have huN : u ∈ (g.neighborSet v).toFinset := by simpa using huv.symm
      have hn : (g.neighborSet v).toFinset.card = Nat.card (g.neighborSet v) := by simp [Nat.card_eq_fintype_card]
      have hd := degree_bound v
      dsimp [N]
      rw [Finset.card_erase_of_mem huN, hn]
      omega
    have hc : Nat.card (S u v) ≤ 1 + ∑ w ∈ N, Nat.card (S v w) := by
      have hc1 := Set.ncard_le_ncard cover
      have hc2 := Set.ncard_union_le ({v} : Set V) (⋃ w ∈ (N : Set V), S v w)
      have hc3 : (⋃ w ∈ (N : Set V), S v w).ncard ≤ ∑ w ∈ N, Nat.card (S v w) := by
        induction N using Finset.induction_on with
        | empty => simp
        | @insert a t ha ih =>
          simp only [Finset.coe_insert, Set.biUnion_insert, Finset.sum_insert ha]
          exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
      have hc4 : ({v} : Set V).ncard = 1 := Set.ncard_singleton v
      change Nat.card (S u v) ≤ _ at hc1
      change _ ≤ ({v} : Set V).ncard + _ at hc2
      omega
    have hs : (∑ w ∈ N, Nat.card (S v w)) ≤ N.card * (k - 1) := by
      calc
        _ ≤ ∑ w ∈ N, (k - 1) := Finset.sum_le_sum fun w hw => by
          have := hsmall w ((memN w).mp hw).1 ((memN w).mp hw).2
          omega
        _ = _ := by simp
    have hm := Nat.mul_le_mul_right (k - 1) ncard
    omega
