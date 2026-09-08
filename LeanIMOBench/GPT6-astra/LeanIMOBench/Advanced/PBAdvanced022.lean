import LeanFlowProofs.PBAdvanced022.CartesianFrame
import LeanFlowProofs.PBAdvanced022.DotDetAlgebra
import LeanFlowProofs.PBAdvanced022.IncenterCoordinates
import LeanFlowProofs.PBAdvanced022.NegativeArcPoint
import LeanFlowProofs.PBAdvanced022.SideParameters
import LeanFlowProofs.PBAdvanced022.SupplementCriterion
import LeanFlowProofs.PBAdvanced022.TangentNormalSquare
import Mathlib

/-
Given a triangle $ABC$ with $AB < AC < BC$, let $I$ be the incenter
of triangle $ABC$, and let $M$ and $N$ be the midpoints of sides
$CA$ and $AB$, respectively. Let $K$ be the midpoint of the arc
$BC$ of the circumcircle of triangle $ABC$ which does not contain
$A$. Let $B' \neq C$ be the point where the line parallel to $AC$
and tangent to the incircle of triangle $ABC$ intersects side $BC$,
and similarly, let $C' \neq B$ be the point where the line parallel
to $AB$ and tangent to the incircle of triangle $ABC$ intersects
side $BC$. Find the value of $\angle NIM+\angle B'KC'$ in terms
of degree.

Answer: 180
-/
open Real EuclideanGeometry Affine.Simplex

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation degrees "ᵒ" => (degrees * π / 180)

/--
Auxiliary definition for constructing the points B' & C'.
Assuming ω is the incircle of ABC, then `IsParaTangentFoot A B C B' ω` is true
if `B'` is the point where the line parallel to AC and tangent to ω intersects side BC, and not C.
-/
def IsParaTangentFoot (A B C B' : ℝ²) (ω : Sphere ℝ²) : Prop :=
  B' ≠ C ∧ Collinear ℝ {B', B, C} ∧
  ∃ t : AffineSubspace ℝ ℝ², t.Parallel (affineSpan ℝ {A, C}) ∧ ω.IsTangent t ∧ B' ∈ t

theorem PBAdvanced022
    -- a triangle ABC
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    -- ABC satisfies the given side inequalities
    (h_side_len : dist A B < dist A C ∧ dist A C < dist B C)
    (I : ℝ²) (hI : I = incenter ⟨![A, B, C], tri⟩) -- I is the incenter
    -- M and N are the midpoints of sides CA and AB
    (M : ℝ²) (hM : M = midpoint ℝ C A)
    (N : ℝ²) (hN : N = midpoint ℝ A B)
    -- We will denote the incircle ω, and circumcircle Ω
    (ω : Sphere ℝ²) (hω : ω = insphere ⟨![A, B, C], tri⟩)
    (Ω : Sphere ℝ²) (hΩ : Ω = circumsphere ⟨![A, B, C], tri⟩)
    -- K is the midpoint of the arc BC of the circumcircle of triangle ABC which does not contain A
    (K : ℝ²) (hK : K ∈ Ω ∧ dist K B = dist K C ∧ (affineSpan ℝ {B, C}).SOppSide A K)
    -- B' ≠ B is the point where the line parallel to AC and tangent to the incircle of triangle ABC intersects side BC
    (B' : ℝ²) (hB : IsParaTangentFoot A B C B' ω)
    -- C' ≠ C be the point where the line parallel to AB and tangent to the incircle of triangle ABC intersects side BC
    (C' : ℝ²) (hC : IsParaTangentFoot A C B C' ω) :
    --  The value of $\angle NIM+\angle B'KC'$ in terms of degree is 180
    ∠ N I M + ∠ B' K C' = 180ᵒ := by set_option maxHeartbeats 2000000 in
  obtain ⟨F, hB0, hB1, hC0, hC1, hv⟩ := LeanFlowProofs.PB022.cartesianFrame A B C tri
  let a := dist B C
  let b := dist A C
  let c := dist A B
  let u := (F A) 0
  let v := (F A) 1
  have hc_sq : c ^ 2 = u ^ 2 + v ^ 2 := by
    change dist A B ^ 2 = _
    rw [← F.dist_map A B, EuclideanSpace.dist_sq_eq]
    simp only [Fin.sum_univ_two, hB0, hB1, Real.dist_eq, sub_zero, sq_abs]
    rfl
  have hb_sq : b ^ 2 = (a - u) ^ 2 + v ^ 2 := by
    change dist A C ^ 2 = _
    rw [← F.dist_map A C, EuclideanSpace.dist_sq_eq]
    simp only [Fin.sum_univ_two, hC0, hC1, Real.dist_eq, sq_abs, sub_zero]
    dsimp [a, u, v]
    ring
  have hc : 0 < c := by
    have := dist_nonneg (x := A) (y := B)
    dsimp [v] at *
    nlinarith [sq_pos_of_pos hv]
  have hb : 0 < b := lt_trans hc h_side_len.1
  have ha : 0 < a := lt_trans hb h_side_len.2
  let s := (a + b + c) / 2
  let x := s - a
  let y := s - b
  let z := s - c
  let r := a * v / (2 * s)
  obtain ⟨hx, hy, hz, hr, ha_eq, hb_eq, hc_eq, hs_eq, hrad, hu, hv_eq, hi0⟩ :=
    LeanFlowProofs.PB022.sideParameters a b c u v ha hb hc hv hc_sq hb_sq
  change 0 < x at hx
  change 0 < y at hy
  change 0 < z at hz
  change 0 < r at hr
  change a = y + z at ha_eq
  change b = x + z at hb_eq
  change c = x + y at hc_eq
  change s = x + y + z at hs_eq
  change s * r ^ 2 = x * y * z at hrad
  change u = y + x * (y - z) / a at hu
  change v = 2 * s * r / a at hv_eq
  change (a * u + a * c) / (2 * s) = y at hi0
  have hi := LeanFlowProofs.PB022.incenterCoordinates A B C tri F a u v ha hv
    ⟨hB0, hB1⟩ ⟨hC0, hC1⟩ ⟨rfl, rfl⟩
  have hp : a + dist A C + dist A B = 2 * s := by dsimp [s, b, c]; ring
  simp only [hp] at hi
  have hI0 : (F I) 0 = y := by rw [hI]; exact hi.1.trans hi0
  have hI1 : (F I) 1 = r := by rw [hI]; exact hi.2.1
  have hωr : ω.radius = r := by rw [hω]; exact hi.2.2
  have hωI : ω.center = I := by rw [hω, hI]; rfl
  have hBC : B ≠ C := dist_pos.mp ha
  have hAC : A ≠ C := dist_pos.mp hb
  have hAB : A ≠ B := dist_pos.mp hc
  have baseline (X : ℝ²) (hX : Collinear ℝ {X, B, C}) : (F X) 1 = 0 := by
    have hm : X ∈ affineSpan ℝ {B, C} :=
      hX.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBC
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hm
    rw [← ht]
    change (F.toAffineEquiv (AffineMap.lineMap B C t)) 1 = 0
    rw [F.toAffineEquiv.apply_lineMap]
    simp [AffineMap.lineMap_apply, hB1, hC1]
  have hB'1 := baseline B' hB.2.1
  have hC'1 : (F C') 1 = 0 := baseline C' (by
    simpa only [Set.pair_comm B C] using hC.2.1)
  have hs : 0 < s := by rw [hs_eq]; positivity
  have hav : a ≠ 0 := ne_of_gt ha
  have hsv : s ≠ 0 := ne_of_gt hs
  have hvv : v ≠ 0 := ne_of_gt hv
  have hcenterAC : v * y + (a - u) * r = a * v - b * r := by
    rw [hu, hv_eq, hb_eq, hs_eq, ha_eq]
    field_simp
    <;> ring
  have hcenterAB : v * y - u * r = c * r := by
    rw [hu, hv_eq, hc_eq, hs_eq, ha_eq]
    field_simp
    <;> ring
  have hBsquare : (v * (F B') 0 - a * v + b * r) ^ 2 = r ^ 2 * b ^ 2 := by
    obtain ⟨t, hpar, htan, hmem⟩ := hB.2.2
    have hh := LeanFlowProofs.PB022.tangentNormalSquare A C B' ω t F v (a-u)
      hAC (by nlinarith only [sq_nonneg (a-u), sq_pos_of_pos hv])
      (by simp only [hC0, hC1]; change v * (a-u) + (a-u) * (0-v) = 0; ring)
      hpar htan hmem
    rw [hωI, hI0, hI1, hB'1, hωr] at hh
    have hn : v ^ 2 + (a-u) ^ 2 = b ^ 2 := by nlinarith only [hb_sq]
    rw [hn] at hh
    have he : v * (F B') 0 - a * v + b * r = v * ((F B') 0 - y) + (a-u) * (0-r) := by
      nlinarith only [hcenterAC]
    rw [he]
    exact hh
  have hCsquare : (v * (F C') 0 - c * r) ^ 2 = r ^ 2 * c ^ 2 := by
    obtain ⟨t, hpar, htan, hmem⟩ := hC.2.2
    have hh := LeanFlowProofs.PB022.tangentNormalSquare A B C' ω t F v (-u)
      hAB (by nlinarith only [sq_nonneg u, sq_pos_of_pos hv])
      (by simp only [hB0, hB1]; change v * (0-u) + (-u) * (0-v) = 0; ring)
      hpar htan hmem
    rw [hωI, hI0, hI1, hC'1, hωr] at hh
    have hn : v ^ 2 + (-u) ^ 2 = c ^ 2 := by nlinarith only [hc_sq]
    rw [hn] at hh
    have he : v * (F C') 0 - c * r = v * ((F C') 0 - y) + (-u) * (0-r) := by
      nlinarith only [hcenterAB]
    rw [he]
    exact hh
  have coord_inj (X Y : ℝ²) (h0 : (F X) 0 = (F Y) 0) (h1 : (F X) 1 = (F Y) 1) : X = Y := by
    apply F.injective
    ext i
    fin_cases i <;> assumption
  have hB'ne : (F B') 0 ≠ a := by
    intro hh
    exact hB.1 (coord_inj B' C (hh.trans hC0.symm) (hB'1.trans hC1.symm))
  have hC'ne : (F C') 0 ≠ 0 := by
    intro hh
    exact hC.1 (coord_inj C' B (hh.trans hB0.symm) (hC'1.trans hB1.symm))
  have hBroot : v * (F B') 0 - a * v + 2 * b * r = 0 := by
    have hf : (v * (F B') 0 - a * v) * (v * (F B') 0 - a * v + 2 * b * r) = 0 := by
      nlinarith only [hBsquare]
    apply (mul_eq_zero.mp hf).resolve_left
    intro hh
    apply hB'ne
    apply (mul_left_cancel₀ hvv)
    nlinarith only [hh]
  have hCroot : v * (F C') 0 = 2 * c * r := by
    have hf : (v * (F C') 0) * (v * (F C') 0 - 2 * c * r) = 0 := by
      nlinarith only [hCsquare]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left (mul_ne_zero hvv hC'ne))
  have hB'0 : (F B') 0 = a * y / s := by
    apply mul_left_cancel₀ hvv
    have he : v * (a * y / s) - a * v + 2 * b * r = 0 := by
      rw [hv_eq, hb_eq, hs_eq, ha_eq]
      field_simp
      <;> ring
    linarith only [hBroot, he]
  have hC'0 : (F C') 0 = a * (x+y) / s := by
    apply mul_left_cancel₀ hvv
    rw [hCroot, hv_eq, hc_eq]
    field_simp
    <;> ring
  let k := a * r / (2 * x)
  have hk : 0 < k := by dsimp [k]; positivity
  have hxe : x ≠ 0 := ne_of_gt hx
  have hre : r ≠ 0 := ne_of_gt hr
  have hcircle : u ^ 2 + v ^ 2 - a * u + (k - a ^ 2 / (4*k)) * v = 0 := by
    rw [← hc_sq, hc_eq, hu, hv_eq]
    dsimp only [k]
    field_simp
    rw [hs_eq, ha_eq] at *
    nlinarith only [hrad]
  have hAmem : A ∈ Ω := by
    rw [hΩ]
    exact (⟨![A,B,C], tri⟩ : Affine.Simplex ℝ ℝ² 2).mem_circumsphere 0
  have hBmem : B ∈ Ω := by
    rw [hΩ]
    exact (⟨![A,B,C], tri⟩ : Affine.Simplex ℝ ℝ² 2).mem_circumsphere 1
  have hCmem : C ∈ Ω := by
    rw [hΩ]
    exact (⟨![A,B,C], tri⟩ : Affine.Simplex ℝ ℝ² 2).mem_circumsphere 2
  obtain ⟨hK0, hK1⟩ := LeanFlowProofs.PB022.negativeArcPoint A B C K Ω F a k ha hk
    ⟨hB0,hB1⟩ ⟨hC0,hC1⟩ hv hcircle hAmem hBmem hCmem hK.1 hK.2.1 hK.2.2
  have hNmap : F N = midpoint ℝ (F A) (F B) := by
    rw [hN]; exact F.toAffineEquiv.map_midpoint A B
  have hMmap : F M = midpoint ℝ (F C) (F A) := by
    rw [hM]; exact F.toAffineEquiv.map_midpoint C A
  have hN0 : (F N) 0 = u / 2 := by
    rw [hNmap]
    simp [midpoint, AffineMap.lineMap_apply, hB0, u]
    <;> ring
  have hN1 : (F N) 1 = v / 2 := by
    rw [hNmap]
    simp [midpoint, AffineMap.lineMap_apply, hB1, v]
    <;> ring
  have hM0 : (F M) 0 = (a + u) / 2 := by
    rw [hMmap]
    simp [midpoint, AffineMap.lineMap_apply, hC0, a, u]
    <;> ring
  have hM1 : (F M) 1 = v / 2 := by
    rw [hMmap]
    simp [midpoint, AffineMap.lineMap_apply, hC1, v]
    <;> ring
  let U := F N - F I
  let V := F M - F I
  let P := F B' - F K
  let Q := F C' - F K
  have hU0 : U 0 = (x*(y-z)-a*y)/(2*a) := by
    change (F N) 0 - (F I) 0 = _
    rw [hN0, hI0, hu]
    field_simp
    <;> ring
  have hV0 : V 0 = (x*(y-z)+a*z)/(2*a) := by
    change (F M) 0 - (F I) 0 = _
    rw [hM0, hI0, hu, ha_eq]
    field_simp
    <;> ring
  have hU1 : U 1 = x*r/a := by
    change (F N) 1 - (F I) 1 = _
    rw [hN1, hI1, hv_eq, hs_eq, ha_eq]
    field_simp
    <;> ring
  have hV1 : V 1 = x*r/a := by
    change (F M) 1 - (F I) 1 = _
    rw [hM1, hI1, hv_eq, hs_eq, ha_eq]
    field_simp
    <;> ring
  have hP0 : P 0 = a*(y-z-x)/(2*s) := by
    change (F B') 0 - (F K) 0 = _
    rw [hB'0, hK0, hs_eq]
    field_simp
    <;> ring
  have hQ0 : Q 0 = a*(y-z+x)/(2*s) := by
    change (F C') 0 - (F K) 0 = _
    rw [hC'0, hK0, hs_eq]
    field_simp
    <;> ring
  have hP1 : P 1 = a*r/(2*x) := by
    change (F B') 1 - (F K) 1 = _
    rw [hB'1, hK1]; dsimp [k]; ring
  have hQ1 : Q 1 = a*r/(2*x) := by
    change (F C') 1 - (F K) 1 = _
    rw [hC'1, hK1]; dsimp [k]; ring
  obtain ⟨hl, hn, hd, he⟩ := LeanFlowProofs.PB022.dotDetAlgebra x y z r hx hy hz hr (by rw [← hs_eq]; exact hrad)
  simp only [← ha_eq, ← hs_eq] at hl hn hd he
  have hsupp := LeanFlowProofs.PB022.supplementCriterion U V P Q (x*s/a^2) hl
    (by simpa only [hP0,hQ0,hP1,hQ1] using hn)
    (by simpa only [hU0,hV0,hU1,hV1,hP0,hQ0,hP1,hQ1] using hd)
    (by simpa only [hU0,hV0,hU1,hV1,hP0,hQ0,hP1,hQ1, ← sq] using he)
  have ht (X Y Z : ℝ²) : ∠ (F X - F Y) (0 : ℝ²) (F Z - F Y) = ∠ X Y Z := by
    rw [← F.toAffineIsometry.angle_map X Y Z]
    simp only [EuclideanGeometry.angle, vsub_eq_sub, sub_zero]
    rfl
  rw [show ∠ U (0 : ℝ²) V = ∠ N I M from ht N I M,
    show ∠ P (0 : ℝ²) Q = ∠ B' K C' from ht B' K C'] at hsupp
  convert hsupp using 1 <;> ring
