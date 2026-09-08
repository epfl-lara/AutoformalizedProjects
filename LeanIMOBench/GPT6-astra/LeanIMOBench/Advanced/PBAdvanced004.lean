import LeanFlowProofs.PB004EdgeSides
import LeanFlowProofs.PB004NestedCuts
import LeanFlowProofs.PB004ThresholdSeparator
import Mathlib

/-
For a positive integer $n$, a convex $18n+2$-gon $P$ is divided into $18n$ triangles by drawing $18n-1$ diagonals. Prove that we can choose two of these diagonals such that the three parts of $P$ divided by these two diagonals each contain at least $3n$ and at most $9n$ triangles.
-/



theorem PBAdvanced004 (n : ℕ) (n_pos : n > 0)
    /-
    We will represent a triangulation with a tree of triangles. This captures enough
    data for the problem statement, even if it doesn't tell the order of the triangles.
    -/
    (Tri : Type) -- all the triangles
    [finTri : Fintype Tri]
    (g : SimpleGraph Tri) -- the adjacency of triangles
    (is_tree : g.IsTree)
    -- every triangle can be adjacent with at most three other triangles
    (degree_bound : ∀ tri : Tri, Nat.card (g.neighborSet tri) ≤ 3)
    -- There are 18n triangles in the triangulation
    (num_triangles : Fintype.card Tri = 18*n) :
    -- We can choose two of the diagonals
    ∃ cut ⊆ g.edgeSet, cut.ncard = 2 ∧
    -- such that every component
    ∀ comp : (g.deleteEdges cut).ConnectedComponent,
    -- contain at least $3n$ and at most $9n$ triangles
    3*n ≤ Nat.card comp ∧ Nat.card comp ≤ 9*n
    := by classical
  let S : Tri → Tri → Set Tri := fun a b =>
    {x | (g.deleteEdges ({Sym2.mk a b} : Set (Sym2 Tri))).Reachable b x}
  have hcard : Nat.card Tri = 18 * n := by simpa using num_triangles
  have swap (a b : Tri) : Sym2.mk a b = Sym2.mk b a := Sym2.eq_swap
  obtain ⟨a, b, hab, hb, _, ha⟩ :=
    LeanFlowProofs.PB004_threshold_separator g is_tree degree_bound (6*n)
      (by omega) (by omega)
  change 6*n ≤ Nat.card (S a b) at hb
  change 6*n ≤ Nat.card (S b a) at ha
  have sum (u v : Tri) (h : g.Adj u v) :
      Nat.card (S v u) + Nat.card (S u v) = 18*n := by
    have hs := (LeanFlowProofs.PB004_edge_side_structure g is_tree u v h).2.2.1
    simpa only [S, swap v u, hcard] using hs
  have orient : ∃ u v : Tri, g.Adj u v ∧
      6*n ≤ Nat.card (S v u) ∧ Nat.card (S v u) ≤ 9*n ∧
      9*n ≤ Nat.card (S u v) ∧ Nat.card (S u v) ≤ 12*n := by
    have hs := sum a b hab
    by_cases h : Nat.card (S b a) ≤ Nat.card (S a b)
    · exact ⟨a, b, hab, ha, by omega, by omega, by omega⟩
    · exact ⟨b, a, hab.symm, hb, by omega, by omega, by omega⟩
  obtain ⟨u, v, huv, hAlo, hAhi, hBlo, hBhi⟩ := orient
  let A : Set Tri := {x | (g.deleteEdges ({Sym2.mk u v} : Set (Sym2 Tri))).Reachable u x}
  let B : Set Tri := S u v
  have hA : A = S v u := by simp only [A, S, swap v u]
  have hstructure := LeanFlowProofs.PB004_edge_side_structure g is_tree u v huv
  have treeB : (g.induce B).IsTree := hstructure.2.2.2.2.1
  have degB : ∀ x : B, Nat.card ((g.induce B).neighborSet x) ≤ 3 := by
    intro x
    let f : (g.induce B).neighborSet x → g.neighborSet x.val :=
      fun y => ⟨y.val.val, y.property⟩
    have hf : Function.Injective f := by
      intro y z h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t : g.neighborSet x.val => t.val) h
    exact (Nat.card_le_card_of_injective f hf).trans (degree_bound x.val)
  obtain ⟨p, q, hpq, hq, _, hp⟩ :=
    LeanFlowProofs.PB004_threshold_separator (g.induce B) treeB degB (3*n)
      (by omega) (by change 3*(3*n) ≤ Nat.card (S u v); omega)
  let B₁ : Set B := {x | ((g.induce B).deleteEdges ({Sym2.mk p q} : Set (Sym2 B))).Reachable p x}
  let B₂ : Set B := {x | ((g.induce B).deleteEdges ({Sym2.mk p q} : Set (Sym2 B))).Reachable q x}
  have hp' : 3*n ≤ Nat.card B₁ := by
    simpa only [B₁, (show Sym2.mk q p = Sym2.mk p q from Sym2.eq_swap)] using hp
  have hq' : 3*n ≤ Nat.card B₂ := hq
  have hsum : Nat.card B₁ + Nat.card B₂ = Nat.card B :=
    (LeanFlowProofs.PB004_edge_side_structure (g.induce B) treeB p q hpq).2.2.1
  have hBhi' : Nat.card B ≤ 12*n := hBhi
  obtain ⟨hc, hn, hcomp⟩ := LeanFlowProofs.PB004_nested_edge_cuts g is_tree u v huv p q hpq
  refine ⟨_, hc, hn, ?_⟩
  intro comp
  rcases hcomp comp with h | h | h
  · change Nat.card comp = Nat.card A at h
    rw [h, hA]
    constructor <;> omega
  · change Nat.card comp = Nat.card B₁ at h
    rw [h]
    constructor <;> omega
  · change Nat.card comp = Nat.card B₂ at h
    rw [h]
    constructor <;> omega
