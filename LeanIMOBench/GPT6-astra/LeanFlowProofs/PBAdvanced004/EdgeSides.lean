import Mathlib

theorem LeanFlowProofs.PB004_edge_side_structure
    {V : Type*} [Finite V]
    (g : SimpleGraph V) (is_tree : g.IsTree)
    (u v : V) (huv : g.Adj u v) :
    let d := g.deleteEdges ({Sym2.mk u v} : Set (Sym2 V))
    let A : Set V := {x : V | d.Reachable u x}
    let B : Set V := {x : V | d.Reachable v x}
    Disjoint A B ∧
      A ∪ B = Set.univ ∧
      Nat.card A + Nat.card B = Nat.card V ∧
      (g.induce A).IsTree ∧
      (g.induce B).IsTree ∧
      (∀ x y : V, x ∈ A → y ∈ B → g.Adj x y → x = u ∧ y = v) := by classical
  dsimp only
  let d := g.deleteEdges ({Sym2.mk u v} : Set (Sym2 V))
  let A : Set V := {x | d.Reachable u x}
  let B : Set V := {x | d.Reachable v x}
  change Disjoint A B ∧ A ∪ B = Set.univ ∧ _
  have hsep : ¬ d.Reachable u v :=
    SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp is_tree.isAcyclic huv
  have hd : Disjoint A B := Set.disjoint_left.mpr (fun x hx hy => hsep (hx.trans hy.symm))
  have hstep : ∀ x y, g.Adj x y → x ∈ A ∪ B → y ∈ A ∪ B := by
    intro x y hxy hx
    by_cases he : Sym2.mk x y = Sym2.mk u v
    · rcases Sym2.eq_iff.mp he with h | h
      · rcases h with ⟨rfl, rfl⟩
        exact Or.inr SimpleGraph.Reachable.rfl
      · rcases h with ⟨rfl, rfl⟩
        exact Or.inl SimpleGraph.Reachable.rfl
    · have hxy' : d.Adj x y := by simpa [d, SimpleGraph.deleteEdges_adj] using And.intro hxy he
      exact hx.elim (fun h => Or.inl (h.trans hxy'.reachable)) (fun h => Or.inr (h.trans hxy'.reachable))
  have hu : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hr := (SimpleGraph.reachable_iff_reflTransGen u x).mp (is_tree.connected.preconnected u x)
    induction hr with
    | refl => exact Or.inl SimpleGraph.Reachable.rfl
    | @tail y z hr hyz ih => exact hstep y z hyz ih
  have hc : Nat.card A + Nat.card B = Nat.card V := by
    have hh := Set.ncard_union_eq hd
    simpa only [hu, Set.ncard_univ, Nat.card_coe_set_eq] using hh.symm
  have ht : ∀ a : V, (g.induce {x | d.Reachable a x}).IsTree := by
    intro a
    have hs : {x | d.Reachable a x} = (d.connectedComponentMk a).supp := by
      ext x
      simp only [Set.mem_setOf_eq, SimpleGraph.ConnectedComponent.mem_supp_iff,
        SimpleGraph.ConnectedComponent.eq, SimpleGraph.reachable_comm]
    refine ⟨?_, is_tree.isAcyclic.induce _⟩
    rw [hs]
    exact (d.connectedComponentMk a).connected_toSimpleGraph.mono (by
      intro x y hxy
      exact (SimpleGraph.deleteEdges_le (G := g) _) (show d.Adj x.val y.val from hxy))
  refine ⟨hd, hu, hc, ht u, ht v, ?_⟩
  intro x y hx hy hxy
  have he : Sym2.mk x y = Sym2.mk u v := by
    by_contra he
    have hxy' : d.Adj x y := by simpa [d, SimpleGraph.deleteEdges_adj] using And.intro hxy he
    exact hsep ((hx.trans hxy'.reachable).trans hy.symm)
  rcases Sym2.eq_iff.mp he with h | h
  · exact h
  · rcases h with ⟨rfl, rfl⟩
    exact (hsep hx).elim
