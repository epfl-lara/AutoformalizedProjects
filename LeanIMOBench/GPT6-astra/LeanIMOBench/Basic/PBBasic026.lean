import LeanFlowProofs.PBBasic026.OneSide
import Mathlib

/-
Let $\triangle ABC$ be an inscribed triangle in $(O)$ and circumscribed
around $(I)$. The incircle $(I)$ touches $BC,CA,AB$ at $D,E,F$,
respectively. Construct the circle $(W_{a})$ passing through $B,C$
and tangent to $(I)$ at $X$, and let $D'$ be the reflection of
$D$ across $AI$. Define $Y,Z,E',F'$ similarly. Prove that the lines
$D'X,E'Y,F'Z$ are concurrent on the line $OI$.
-/
open Real Affine Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- We start by defining the auxiliary construction.
-- Given points A, B, C, we define a predicate that a given line
-- was constructed as the line `D'X`.
def isLineDX (A B C : ℝ²) (dx : AffineSubspace ℝ ℝ²) : Prop :=
  ∃ (tri : AffineIndependent ℝ ![A, B, C]) (W : Sphere ℝ²) (X : ℝ²),
  B ∈ W ∧ C ∈ W ∧
  let I := incenter ⟨![A, B, C], tri⟩
  let D := touchpoint ⟨![A, B, C], tri⟩ ∅ 0
  (insphere ⟨![A, B, C], tri⟩).IsIntTangentAt W X ∧
  let D' := reflection (affineSpan ℝ {A, I}) D
  dx = affineSpan ℝ {D', X}

-- The main problem does this construction 3-times, and claims the result
-- is on the line O I
theorem PBBasic026
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    (l1 l2 l3 : AffineSubspace ℝ ℝ²) :
    isLineDX A B C l1 →
    isLineDX B C A l2 →
    isLineDX C A B l3 →
    let O := circumcenter ⟨![A, B, C], tri⟩
    let I := incenter ⟨![A, B, C], tri⟩
    ∃ p : ℝ², p ∈ l1 ∧ p ∈ l2 ∧ p ∈ l3 ∧ p ∈ affineSpan ℝ {O, I} := by 
  classical
  let P : Simplex ℝ ℝ² 2 → ℝ² := fun s =>
    s.incenter - (s.inradius / (3 * s.circumradius)) • (s.circumcenter - s.incenter)
  have cyclic (a b c : ℝ²) (h : AffineIndependent ℝ ![a,b,c])
      (h' : AffineIndependent ℝ ![b,c,a]) :
      P ⟨![b,c,a], h'⟩ = P ⟨![a,b,c], h⟩ := by
    let e : Fin 3 ≃ Fin 3 :=
      { toFun := ![2,0,1]
        invFun := ![1,2,0]
        left_inv := by intro i; fin_cases i <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }
    have he : (Simplex.mk ![a,b,c] h).reindex e = Simplex.mk ![b,c,a] h' := by
      ext i
      fin_cases i <;> rfl
    rw [← he]
    simp [P]
  have side (a b c : ℝ²) (h : AffineIndependent ℝ ![a,b,c])
      (l : AffineSubspace ℝ ℝ²) (hl : isLineDX a b c l) :
      P ⟨![a,b,c], h⟩ ∈ l := by
    rcases hl with ⟨h', W, X, hB, hC, ht, rfl⟩
    have hh := LeanFlowProofs.PBBasic026_one_side ⟨![a,b,c], h⟩ W X hB hC ht
    dsimp at hh
    have hd : dist (circumcenter (Simplex.mk ![a,b,c] h)) a =
        (Simplex.mk ![a,b,c] h).circumradius := by
      rw [dist_comm]
      exact (Simplex.mk ![a,b,c] h).dist_circumcenter_eq_circumradius 0
    rw [hd] at hh
    exact hh
  intro h1 h2 h3
  have tri2 := h2.choose
  have tri3 := h3.choose
  dsimp only
  refine ⟨P ⟨![A,B,C], tri⟩, side A B C tri l1 h1, ?_, ?_, ?_⟩
  · rw [← cyclic A B C tri tri2]
    exact side B C A tri2 l2 h2
  · rw [← cyclic A B C tri tri2, ← cyclic B C A tri2 tri3]
    exact side C A B tri3 l3 h3
  · let s : Simplex ℝ ℝ² 2 := ⟨![A,B,C], tri⟩
    have hO : s.circumcenter ∈ affineSpan ℝ {s.circumcenter, s.incenter} :=
      subset_affineSpan ℝ _ (by simp)
    have hI : s.incenter ∈ affineSpan ℝ {s.circumcenter, s.incenter} :=
      subset_affineSpan ℝ _ (by simp)
    have hh := (affineSpan ℝ {s.circumcenter, s.incenter}).smul_vsub_vadd_mem
      (-(s.inradius / (3 * s.circumradius))) hO hI hI
    simpa [P, s, vsub_eq_sub, vadd_eq_add, neg_smul, sub_eq_add_neg, add_comm] using hh

