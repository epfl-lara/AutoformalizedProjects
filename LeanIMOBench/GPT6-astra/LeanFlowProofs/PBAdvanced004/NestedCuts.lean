import LeanFlowProofs.PBAdvanced004.EdgeSides
import Mathlib

theorem LeanFlowProofs.PB004_nested_edge_cuts
    {V : Type*} [Finite V]
    (g : SimpleGraph V) (is_tree : g.IsTree)
    (u v : V) (huv : g.Adj u v) :
    let d := g.deleteEdges ({Sym2.mk u v} : Set (Sym2 V))
    let A : Set V := {x : V | d.Reachable u x}
    let B : Set V := {x : V | d.Reachable v x}
    ∀ (p q : B), (g.induce B).Adj p q →
      let dB := (g.induce B).deleteEdges ({Sym2.mk p q} : Set (Sym2 B))
      let B₁ : Set B := {x : B | dB.Reachable p x}
      let B₂ : Set B := {x : B | dB.Reachable q x}
      let cut : Set (Sym2 V) := {Sym2.mk u v, Sym2.mk (p : V) (q : V)}
      cut ⊆ g.edgeSet ∧ cut.ncard = 2 ∧
        ∀ comp : (g.deleteEdges cut).ConnectedComponent,
          Nat.card comp = Nat.card A ∨
            Nat.card comp = Nat.card B₁ ∨ Nat.card comp = Nat.card B₂ := by   classical
  have card_lift (G : SimpleGraph V) (S : Set V) (H : SimpleGraph S)
      (ha : ∀ a b : S, H.Adj a b ↔ G.Adj a.val b.val)
      (hc : ∀ a b : V, a ∈ S → G.Adj a b → b ∈ S) (x : S) :
      Nat.card (G.connectedComponentMk x.val) =
        Nat.card {y : S | H.Reachable x y} := by
    have liftReach : ∀ a b : V, G.Reachable a b → ∀ h : a ∈ S,
        ∃ h' : b ∈ S, H.Reachable ⟨a, h⟩ ⟨b, h'⟩ := by
      rintro a b ⟨w⟩
      induction w with
      | nil => intro h; exact ⟨h, .rfl⟩
      | @cons a b c hab w ih =>
        intro h
        obtain ⟨h', hr⟩ := ih (hc a b h hab)
        exact ⟨h', ((ha ⟨a, h⟩ ⟨b, hc a b h hab⟩).2 hab).reachable.trans hr⟩
    let f : {y : S | H.Reachable x y} → (G.connectedComponentMk x.val) :=
      fun y => ⟨y.val.val, SimpleGraph.ConnectedComponent.sound
        ((y.property.map (show H →g G from
          { toFun := Subtype.val, map_rel' := fun h => (ha _ _).1 h })).symm)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : (G.connectedComponentMk x.val) => z.val) h
      · intro y
        have hr : G.Reachable x.val y.val :=
          (SimpleGraph.ConnectedComponent.exact y.property).symm
        obtain ⟨hy, hr⟩ := liftReach _ _ hr x.property
        exact ⟨⟨⟨y.val, hy⟩, hr⟩, rfl⟩
    exact (Nat.card_congr (Equiv.ofBijective f hf)).symm
  intro d A B p q hpq dB B₁ B₂ cut
  have hs := LeanFlowProofs.PB004_edge_side_structure g is_tree u v huv
  change Disjoint A B ∧ A ∪ B = Set.univ ∧ _ at hs
  have ht := LeanFlowProofs.PB004_edge_side_structure (g.induce B) hs.2.2.2.2.1 p q hpq
  change Disjoint B₁ B₂ ∧ B₁ ∪ B₂ = Set.univ ∧ _ at ht
  have huA : u ∈ A := SimpleGraph.Reachable.rfl
  have hvB : v ∈ B := SimpleGraph.Reachable.rfl
  have hnAB : ∀ {x : V}, x ∈ A → x ∈ B → False := by
    intro x ha hb
    exact Set.disjoint_left.mp hs.1 ha hb
  have huB : u ∉ B := hnAB huA
  have hvA : v ∉ A := fun h => hnAB h hvB
  have hpart (x : V) : x ∈ A ∨ x ∈ B := by
    have : x ∈ A ∪ B := by rw [hs.2.1]; trivial
    exact this
  have hne : Sym2.mk u v ≠ Sym2.mk (p : V) (q : V) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact huB (h.1 ▸ p.property)
    · exact huB (h.1 ▸ q.property)
  refine ⟨?_, Set.ncard_pair hne, ?_⟩
  · intro e he
    rcases he with rfl | he
    · exact huv
    · have : e = Sym2.mk (p : V) (q : V) := he
      subst e
      exact hpq
  let G := g.deleteEdges cut
  have hGA : ∀ a b : A, (g.induce A).Adj a b ↔ G.Adj a.val b.val := by
    intro a b
    simp only [G, SimpleGraph.deleteEdges_adj, SimpleGraph.induce_adj]
    refine ⟨fun h => ⟨h, ?_⟩, And.left⟩
    simp only [cut, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff]
    rintro (h | h)
    · rcases h with h | h
      · exact hvA (h.2 ▸ b.property)
      · exact hvA (h.1 ▸ a.property)
    · rcases h with h | h
      · exact hnAB a.property (h.1.symm ▸ p.property)
      · exact hnAB a.property (h.1.symm ▸ q.property)
  have hGB : ∀ a b : B, dB.Adj a b ↔ G.Adj a.val b.val := by
    intro a b
    simp only [dB, G, SimpleGraph.deleteEdges_adj, SimpleGraph.induce_adj,
      cut, Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, Subtype.ext_iff]
    have hau : a.val ≠ u := fun h => huB (h ▸ a.property)
    have hbu : b.val ≠ u := fun h => huB (h ▸ b.property)
    tauto
  have hclosedA : ∀ a b : V, a ∈ A → G.Adj a b → b ∈ A := by
    intro a b ha hab
    rcases hpart b with hb | hb
    · exact hb
    · have hh := hs.2.2.2.2.2 a b ha hb (SimpleGraph.deleteEdges_adj.mp hab).1
      have hn := (SimpleGraph.deleteEdges_adj.mp hab).2
      exact False.elim (hn (by simp [cut, hh.1, hh.2]))
  have hclosedB : ∀ a b : V, a ∈ B → G.Adj a b → b ∈ B := by
    intro a b ha hab
    rcases hpart b with hb | hb
    · have hh := hs.2.2.2.2.2 b a hb ha (SimpleGraph.deleteEdges_adj.mp hab).1.symm
      have hn := (SimpleGraph.deleteEdges_adj.mp hab).2
      exact False.elim (hn (by simp [cut, hh.1, hh.2, Sym2.eq_swap]))
    · exact hb
  intro comp
  obtain ⟨x, rfl⟩ := comp.exists_rep
  change Nat.card (G.connectedComponentMk x) = Nat.card A ∨
    Nat.card (G.connectedComponentMk x) = Nat.card B₁ ∨
    Nat.card (G.connectedComponentMk x) = Nat.card B₂
  rcases hpart x with hx | hx
  · left
    rw [card_lift G A (g.induce A) hGA hclosedA ⟨x, hx⟩]
    have he : {y : A | (g.induce A).Reachable ⟨x, hx⟩ y} = Set.univ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hs.2.2.2.1.connected.preconnected _ _
    rw [he]
    exact Nat.card_congr (Equiv.Set.univ A)
  · right
    rw [card_lift G B dB hGB hclosedB ⟨x, hx⟩]
    have hpartB : (⟨x, hx⟩ : B) ∈ B₁ ∨ (⟨x, hx⟩ : B) ∈ B₂ := by
      change (⟨x, hx⟩ : B) ∈ B₁ ∪ B₂
      rw [ht.2.1]
      trivial
    rcases hpartB with h | h
    · left
      have he : {y : B | dB.Reachable ⟨x, hx⟩ y} = B₁ := by
        ext y
        exact ⟨fun hy => h.trans hy, fun hy => h.symm.trans hy⟩
      rw [he]
    · right
      have he : {y : B | dB.Reachable ⟨x, hx⟩ y} = B₂ := by
        ext y
        exact ⟨fun hy => h.trans hy, fun hy => h.symm.trans hy⟩
      rw [he]
