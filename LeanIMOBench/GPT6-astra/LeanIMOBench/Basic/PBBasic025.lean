import LeanFlowProofs.PBBasic025.AngleOfOrthogonalSpans
import LeanFlowProofs.PBBasic025.IncenterDisplacement
import LeanFlowProofs.PBBasic025.InnerProductCancellation
import LeanFlowProofs.PBBasic025.SegmentPlacement
import Mathlib

/-
Given a triangle $XYZ$ with circumcenter $O$, the incircle of triangle
$XYZ$ has center $I$. Let $M,N$ on the sides $XY,XZ$
respectively such that $YM=ZN=YZ$. If $\gamma$ is the angle created
by two lines $MN,OI$, what is $\frac{\gamma}{2}$ in terms of degree?
-/
open Real Affine Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation degrees "ᵒ" => (degrees * π / 180)

theorem PBBasic025
    -- Given a triangle $XYZ$
    (X Y Z : ℝ²) (tri : AffineIndependent ℝ ![X, Y, Z]) :
    -- with circumcenter $O$,
    let O := circumcenter ⟨![X, Y, Z], tri⟩
    -- the incircle of triangle $XYZ$ has center $I$.
    let I := incenter ⟨![X, Y, Z], tri⟩
    -- Let $M,N$ on the sides $XY,XZ$ respectively such that $YM=ZN=YZ$.
    ∀ M N : ℝ², Sbtw ℝ X M Y → Sbtw ℝ X N Z →
    dist Y M = dist Y Z → dist Z N = dist Y Z →
    -- take an auxiliary point `p` at the intersection of `MN` and `OI`
    -- and two helper points `p₁ p₂` on the lines to define the angle `gamma`
    ∀ (p p₁ p₂ : ℝ²), p ∈ affineSpan ℝ {M, N} → p ∈ affineSpan ℝ {O, I} →
    p₁ ∈ affineSpan ℝ {M, N} → p₂ ∈ affineSpan ℝ {O, I} →
    let γ := ∠ p₁ p p₂
    -- it is true that once we know `γ / 2` is supposed to equal `45ᵒ`, we don't
    -- need the condition γ ≤ 90ᵒ but in general, we probably mean to take
    -- the non-obtuse angle when measuring an angle between lines
    γ ≤ 90ᵒ → γ / 2 = 45ᵒ
      := by exact (by
  intro O I M N hM hN hYM hZN p p₁ p₂ hpMN hpOI hp₁ hp₂ γ hγ
  obtain ⟨hc, hm⟩ := LeanFlowProofs.pbbasic025_segmentPlacement X Y M (dist Y Z) hM hYM
  obtain ⟨hb, hn⟩ := LeanFlowProofs.pbbasic025_segmentPlacement X Z N (dist Y Z) hN hZN
  have hi := LeanFlowProofs.pbbasic025_incenterDisplacement (⟨![X,Y,Z], tri⟩ : Simplex ℝ ℝ² 2)
  change I - X = (dist X Z / (dist Y Z + dist X Z + dist X Y)) • (Y-X) +
    (dist X Y / (dist Y Z + dist X Z + dist X Y)) • (Z-X) at hi
  have sq (A B : ℝ²) : inner ℝ (A-B) (A-B) = dist A B ^ 2 := by
    rw [real_inner_self_eq_norm_sq, dist_eq_norm]
  have cosine (A B C : ℝ²) :
      2 * inner ℝ (A-C) (B-C) = dist A C ^ 2 + dist B C ^ 2 - dist A B ^ 2 := by
    have h := sq A B
    have he : A-B = (A-C) - (B-C) := by abel
    rw [he, inner_sub_left, inner_sub_right _ (A-C) (B-C),
      inner_sub_right _ (A-C) (B-C),
      real_inner_comm (B-C) (A-C), sq A C, sq B C] at h
    linarith [real_inner_comm (A-C) (B-C)]
  let s : Simplex ℝ ℝ² 2 := ⟨![X,Y,Z], tri⟩
  have hoY : dist O Y = dist O X := by
    have h := (s.dist_circumcenter_eq_circumradius 1).trans
      (s.dist_circumcenter_eq_circumradius 0).symm
    simpa [s, dist_comm] using h
  have hoZ : dist O Z = dist O X := by
    have h := (s.dist_circumcenter_eq_circumradius 2).trans
      (s.dist_circumcenter_eq_circumradius 0).symm
    simpa [s, dist_comm] using h
  have hu : inner ℝ (Y-X) (Y-X) = dist X Y ^ 2 := by simpa [dist_comm] using sq Y X
  have hv : inner ℝ (Z-X) (Z-X) = dist X Z ^ 2 := by simpa [dist_comm] using sq Z X
  have huv : 2 * inner ℝ (Y-X) (Z-X) = dist X Z ^ 2 + dist X Y ^ 2 - dist Y Z ^ 2 := by
    have h := cosine Y Z X
    simpa only [dist_comm Y X, dist_comm Z X, add_comm] using h
  have hqu : 2 * inner ℝ (O-X) (Y-X) = dist X Y ^ 2 := by
    have h := cosine O Y X
    rw [hoY, dist_comm Y X] at h
    linarith
  have hqv : 2 * inner ℝ (O-X) (Z-X) = dist X Z ^ 2 := by
    have h := cosine O Z X
    rw [hoZ, dist_comm Z X] at h
    linarith
  have hS : dist Y Z + dist X Z + dist X Y ≠ 0 := by
    have := dist_nonneg (x := Y) (y := Z)
    linarith
  have halg := LeanFlowProofs.pbbasic025_innerProductCancellation
    (dist Y Z) (dist X Z) (dist X Y) (Y-X) (Z-X) (O-X)
    (ne_of_gt hb) (ne_of_gt hc) hS hu hv huv hqu hqv
  rw [← hi, ← hn, ← hm] at halg
  have he₁ : O-X-(I-X) = -(I-O) := by abel
  have he₂ : N-X-(M-X) = N-M := by abel
  rw [he₁, he₂, inner_neg_left, neg_eq_zero, real_inner_comm] at halg
  have ha := LeanFlowProofs.pbbasic025_angleOfOrthogonalSpans M N O I p p₁ p₂
    halg hpMN hp₁ hpOI hp₂
  change (∠ p₁ p p₂) / 2 = 45 * π / 180
  rw [ha]
  ring)
