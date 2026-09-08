import LeanFlowProofs.PB009AHGSecondIntersection
import LeanFlowProofs.PB009CosphericalEquation
import LeanFlowProofs.PB009FirstCircleCertificates
import LeanFlowProofs.PB009OriginCircleTransfer
import LeanFlowProofs.PB009PencilCertificates
import LeanFlowProofs.PB009ScalarCompletion
import Mathlib

/-
Let $H$ be the orthocenter of an acute-angled triangle $A B C$, and let $D, E, F$ be the feet of the altitudes from vertices $A, B, C$ to the opposite sides, respectively. Let $G$ be the midpoint of $B C$. Let $I, J$ be the feet of the perpendiculars from $B, C$ to $AG$, respectively. Let $K (\neq D)$ be the second intersection of the circumcircles of triangle $D I F$ and triangle $D J E$. Let $M$ be the midpoint of segment $A H$. Let $L$ be the foot of the perpendicular from $M$ to $A G$. Let $R (\neq G)$ be the second intersection of the circumcircle of triangle $A H G$ with $B C$. Let $S$ be the intersection of line $A H$ and $E F$. Let $N$ be the foot of the perpendicular from point $D$ to $R S$. Let $O$ be the midpoint of segment $D N$. Let line $D N$ intersect the circumcircle of triangle $D K L$ again at point $P (\neq D)$. Let $Q (\neq C)$ be the second intersection of the circumcircle of triangle $O C P$ and line $B C$. Prove that $A B=A Q$.
-/

open Affine Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem PBAdvanced009
    -- Acute-angled triangle $A, B, C$
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    (acute : AcuteAngled ⟨![A, B, C], tri⟩)
    (D : ℝ²) (hD : D = altitudeFoot ⟨![A, B, C], tri⟩ 0) -- D is the foot from A
    (E : ℝ²) (hE : E = altitudeFoot ⟨![A, B, C], tri⟩ 1) -- E is the foot from B
    (F : ℝ²) (hF : F = altitudeFoot ⟨![A, B, C], tri⟩ 2) -- F is the foot from C
    (H : ℝ²) (hH : H = Triangle.orthocenter ⟨![A, B, C], tri⟩) -- H is the orthocenter
    (G : ℝ²) (hG : G = midpoint ℝ B C) -- $G$ is the midpoint of $B C$
    -- $I, J$ are the feet of the perpendiculars from $B, C$ to $AG$
    (I : ℝ²) (hI : I = orthogonalProjection (affineSpan ℝ {A, G}) B)
    (J : ℝ²) (hJ : J = orthogonalProjection (affineSpan ℝ {A, G}) C)
    -- K ≠ D is the second intersection of the circumcircles of triangles $D I F$ and $D J E$
    (K : ℝ²) (hK : K ≠ D ∧ Cospherical {K, D, I, F} ∧ Cospherical {K, D, J, E})
    (M : ℝ²) (hM : M = midpoint ℝ A H) -- M is the midpoint of segment $A H$
    -- Let $L$ be the foot of the perpendicular from $M$ to $A G$.
    (L : ℝ²) (hL : L = orthogonalProjection (affineSpan ℝ {A, G}) M)
    -- Let R ≠ G be the second intersection of the circumcircle of triangle $A H G$ with $B C$.
    (R : ℝ²) (hR : (R ≠ G ∧ Cospherical {R, A, H, G} ∧ Collinear ℝ {R, B, C}))
    -- Let $S$ be the intersection of line $A H$ and $E F$.
    (S : ℝ²) (hS : Collinear ℝ {S, A, H} ∧ Collinear ℝ {S, E, F})
    -- Let $N$ be the foot of the perpendicular from point $D$ to $R S$.
    (N : ℝ²) (hN : N = orthogonalProjection (affineSpan ℝ {R, S}) D)
    -- Let $O$ be the midpoint of segment $D N$.
    (O : ℝ²) (hO : O = midpoint ℝ D N)
    -- Let line $D N$ intersect the circumcircle of triangle $D K L$ again at point $P (\neq D)$.
    (P : ℝ²) (hP : P ≠ D ∧ Collinear ℝ {P, D, N} ∧ Cospherical {P, D, K, L})
    -- Let $Q (\neq C)$ be the second intersection of the circumcircle of triangle $O C P$ and line $B C$.
    (Q : ℝ²) (hQ : Q ≠ C ∧ Cospherical {Q, O, C, P} ∧ Collinear ℝ {Q, B, C}) :
    -- Prove that $A B=A Q$.
    dist A B = dist A Q := by set_option maxRecDepth 10000 in
  set_option hygiene false in
  run_tac
    withTheReader Lean.Core.Context (fun ctx => {ctx with maxHeartbeats := 4000000000}) do
      Lean.Elab.Tactic.evalTactic (← `(tactic| {
  classical
  let T : Triangle ℝ ℝ² := ⟨![A, B, C], tri⟩
  have hAD : A ≠ D := by simpa [T, ← hD] using T.ne_altitudeFoot 0
  have hBC : B ≠ C := by
    intro h
    have he : (1 : Fin 3) = 2 := tri.injective (by simpa using h)
    exact (by decide : (1 : Fin 3) ≠ 2) he
  have hBDorth : inner ℝ (B - D) (A - D) = 0 := by
    simpa [T, ← hD] using T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 0) (j := 1) (by decide)
  have hCDorth : inner ℝ (C - D) (A - D) = 0 := by
    simpa [T, ← hD] using T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 0) (j := 2) (by decide)
  have hBCorth : inner ℝ (C - B) (A - D) = 0 := by
    have he : C - B = (C - D) - (B - D) := by abel
    rw [he, inner_sub_left, hBDorth, hCDorth, sub_self]
  have hDline : D ∈ affineSpan ℝ ({B, C} : Set ℝ²) := by
    have he : T.points '' ({0}ᶜ : Set (Fin 3)) = ({B, C} : Set ℝ²) := by
      ext X
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i <;> simp_all [T]
      · rintro (rfl | rfl)
        · exact ⟨1, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [hD]
    simpa only [← he] using T.altitudeFoot_mem_affineSpan_image_compl 0
  obtain ⟨tD, htD⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hDline
  have hDparam : D = tD • (C - B) + B := by
    simpa [AffineMap.lineMap_apply] using htD.symm
  have inner_pos_of_acute (X Y : ℝ²)
      (h : InnerProductGeometry.angle X Y < Real.pi / 2) : 0 < inner ℝ X Y := by
    have hp := Real.arccos_lt_pi_div_two.mp h
    exact (div_pos_iff.mp hp).elim (fun hh => hh.1)
      (fun hh => False.elim ((not_lt_of_ge (mul_nonneg (norm_nonneg X) (norm_nonneg Y))) hh.2))
  have hBacute : 0 < inner ℝ (A - B) (C - B) := by
    apply inner_pos_of_acute
    simpa [EuclideanGeometry.angle] using acute 0 1 2 (by decide) (by decide) (by decide)
  have hCacute : 0 < inner ℝ (A - C) (B - C) := by
    apply inner_pos_of_acute
    simpa [EuclideanGeometry.angle] using acute 0 2 1 (by decide) (by decide) (by decide)
  have hAacute : 0 < inner ℝ (B - A) (C - A) := by
    apply inner_pos_of_acute
    simpa [EuclideanGeometry.angle] using acute 1 0 2 (by decide) (by decide) (by decide)
  have hCBnorm : 0 < ‖C - B‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hBC.symm)
  have hADnorm : 0 < ‖A - D‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAD)
  have hADBCorth : inner ℝ (A - D) (C - B) = 0 := by rw [real_inner_comm]; exact hBCorth
  have htDpos : 0 < tD := by
    have he : A - B = (A - D) + tD • (C - B) := by rw [hDparam]; abel
    rw [he, inner_add_left, hADBCorth,
      real_inner_smul_left, real_inner_self_eq_norm_sq, zero_add] at hBacute
    exact (mul_pos_iff.mp hBacute).elim (fun hh => hh.1)
      (fun hh => False.elim ((not_lt_of_ge (sq_nonneg _)) hh.2))
  have htDlt : tD < 1 := by
    have he : A - C = (A - D) + (tD - 1) • (C - B) := by rw [hDparam]; module
    rw [he, show B - C = -(C - B) by abel, inner_neg_right, inner_add_left,
      hADBCorth, real_inner_smul_left,
      real_inner_self_eq_norm_sq, zero_add] at hCacute
    nlinarith [sq_pos_of_pos hCBnorm]
  let a := ‖A - D‖
  let b := tD * ‖C - B‖
  let c := (1 - tD) * ‖C - B‖
  have ha : 0 < a := hADnorm
  have hb : 0 < b := mul_pos htDpos hCBnorm
  have hc : 0 < c := mul_pos (sub_pos.mpr htDlt) hCBnorm
  let e₁ : ℝ² := ‖C - B‖⁻¹ • (C - B)
  let e₂ : ℝ² := a⁻¹ • (A - D)
  have horth : Orthonormal ℝ ![e₁, e₂] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e₁, e₂, real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq,
        hBCorth, hADBCorth, a, ne_of_gt hCBnorm, ne_of_gt hADnorm, sq, mul_assoc,
        norm_smul, Real.norm_eq_abs, abs_of_pos hCBnorm, abs_of_pos hADnorm]
  let basis : OrthonormalBasis (Fin 2) ℝ ℝ² :=
    OrthonormalBasis.mk horth (by rw [horth.linearIndependent.span_eq_top_of_card_eq_finrank (by simp)])
  let φ : ℝ² → ℝ² := fun X => basis.repr (X - D)
  have hφ0 (X : ℝ²) : φ X 0 = inner ℝ e₁ (X - D) := by
    simpa only [basis, OrthonormalBasis.coe_mk, Matrix.cons_val_zero] using basis.repr_apply_apply (X - D) 0
  have hφ1 (X : ℝ²) : φ X 1 = inner ℝ e₂ (X - D) := by
    simpa only [basis, OrthonormalBasis.coe_mk, Matrix.cons_val_one, Matrix.cons_val_zero] using basis.repr_apply_apply (X - D) 1
  have hφdist (X Y : ℝ²) : dist (φ X) (φ Y) = dist X Y := by
    rw [show dist (φ X) (φ Y) = dist (X - D) (Y - D) from basis.repr.dist_map _ _]
    exact dist_sub_right _ _ _
  have hφinj : Function.Injective φ := by
    intro X Y h
    apply dist_eq_zero.mp
    rw [← hφdist, h, dist_self]
  have hD0 : φ D 0 = 0 := by simp [φ]
  have hD1 : φ D 1 = 0 := by simp [φ]
  have hA0 : φ A 0 = 0 := by simp [hφ0, e₁, real_inner_smul_left, hBCorth]
  have hA1 : φ A 1 = a := by
    simp only [hφ1, e₂, real_inner_smul_left, real_inner_self_eq_norm_sq]
    change a⁻¹ * a ^ 2 = a
    field_simp
  have hBDparam : B - D = -tD • (C - B) := by rw [hDparam]; module
  have hCDparam : C - D = (1-tD) • (C - B) := by rw [hDparam]; module
  have hB0 : φ B 0 = -b := by
    simp only [hφ0, hBDparam, e₁, real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [b]
    field_simp
  have hB1 : φ B 1 = 0 := by
    simp only [hφ1, e₂, real_inner_smul_left]
    rw [real_inner_comm, hBDorth, mul_zero]
  have hC0 : φ C 0 = c := by
    simp only [hφ0, hCDparam, e₁, real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
    dsimp [c]
    field_simp
  have hC1 : φ C 1 = 0 := by
    simp only [hφ1, e₂, real_inner_smul_left]
    rw [real_inner_comm, hCDorth, mul_zero]
  have hφinner (X Y Z W : ℝ²) :
      (φ X 0 - φ Y 0) * (φ Z 0 - φ W 0) +
      (φ X 1 - φ Y 1) * (φ Z 1 - φ W 1) = inner ℝ (X - Y) (Z - W) := by
    have he (U V : ℝ²) : φ U - φ V = basis.repr (U - V) := by
      dsimp [φ]
      rw [← map_sub]
      congr 1
      abel
    have hh := basis.repr.inner_map_map (X - Y) (Z - W)
    rw [← he X Y, ← he Z W] at hh
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hh
  have hacute : b * c < a ^ 2 := by
    have hh := hφinner B A C A
    rw [hB0, hB1, hC0, hC1, hA0, hA1] at hh
    nlinarith
  have hφline (X Y : ℝ²) (t : ℝ) :
      φ (t • (Y - X) + X) = t • (φ Y - φ X) + φ X := by
    dsimp [φ]
    rw [← map_sub, ← map_smul, ← map_add]
    congr 1
    module
  have hφmid (X Y : ℝ²) : φ (midpoint ℝ X Y) = midpoint ℝ (φ X) (φ Y) := by
    simpa only [midpoint, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] using hφline X Y (⅟2)
  have hG0 : φ G 0 = (c - b) / 2 := by
    rw [hG, hφmid]
    simp [midpoint_eq_smul_add, hB0, hC0]
    ring
  have hG1 : φ G 1 = 0 := by
    rw [hG, hφmid]
    simp [midpoint_eq_smul_add, hB1, hC1]
  have hHorth (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) :
      inner ℝ (T.points j - T.points k) (H - T.points i) = 0 := by
    have hh : H ∈ T.altitude i := by rw [hH]; exact T.orthocenter_mem_altitude
    have hh' := (AffineSubspace.mem_mk'.mp hh.1)
    apply (Submodule.mem_orthogonal _ _).mp hh'
    apply AffineSubspace.vsub_mem_direction <;> apply subset_affineSpan ℝ
    · exact ⟨j, hji, rfl⟩
    · exact ⟨k, hki, rfl⟩
  have hH0 : φ H 0 = 0 := by
    have hh := hφinner C B H A
    have ho := hHorth 0 2 1 (by decide) (by decide)
    change inner ℝ (C - B) (H - A) = 0 at ho
    rw [ho, hC0, hB0, hC1, hB1, hA0, hA1] at hh
    nlinarith
  have hH1 : φ H 1 = b * c / a := by
    have hh := hφinner C A H B
    have ho := hHorth 1 2 0 (by decide) (by decide)
    change inner ℝ (C - A) (H - B) = 0 at ho
    rw [ho, hC0, hA0, hC1, hA1, hB0, hB1, hH0] at hh
    apply (eq_div_iff ha.ne').mpr
    nlinarith
  have hlinecoord (X Y Z : ℝ²) (hz : Z ∈ affineSpan ℝ ({X,Y} : Set ℝ²)) :
      ∃ t : ℝ, φ Z 0 = t * (φ Y 0 - φ X 0) + φ X 0 ∧
        φ Z 1 = t * (φ Y 1 - φ X 1) + φ X 1 := by
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hz
    refine ⟨t, ?_, ?_⟩ <;> rw [← ht]
    · simpa [AffineMap.lineMap_apply] using congrArg (fun V : ℝ² => V 0) (hφline X Y t)
    · simpa [AffineMap.lineMap_apply] using congrArg (fun V : ℝ² => V 1) (hφline X Y t)
  have hcolcoord (X Y Z : ℝ²) (hne : X ≠ Y) (hz : Collinear ℝ {Z,X,Y}) :
      ∃ t : ℝ, φ Z 0 = t * (φ Y 0 - φ X 0) + φ X 0 ∧
        φ Z 1 = t * (φ Y 1 - φ X 1) + φ X 1 := by
    apply hlinecoord
    exact hz.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hne
  have hprojcoord (X Y Z V : ℝ²)
      (hv : V = orthogonalProjection (affineSpan ℝ ({X,Y} : Set ℝ²)) Z) :
      (∃ t : ℝ, φ V 0 = t * (φ Y 0 - φ X 0) + φ X 0 ∧
        φ V 1 = t * (φ Y 1 - φ X 1) + φ X 1) ∧
      (φ Y 0 - φ X 0) * (φ V 0 - φ Z 0) +
        (φ Y 1 - φ X 1) * (φ V 1 - φ Z 1) = 0 := by
    constructor
    · apply hlinecoord
      rw [hv]
      exact orthogonalProjection_mem Z
    · rw [hφinner, hv]
      apply (Submodule.mem_orthogonal _ _).mp (orthogonalProjection_vsub_mem_direction_orthogonal _ Z)
      exact AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ {X,Y} (show Y ∈ ({X,Y} : Set ℝ²) by simp))
        (subset_affineSpan ℝ {X,Y} (show X ∈ ({X,Y} : Set ℝ²) by simp))
  have hcircle (s : Set ℝ²) (hs : Cospherical s) :
      ∃ u v w : ℝ, ∀ X ∈ s, (φ X 0)^2 + (φ X 1)^2 - u * φ X 0 - v * φ X 1 + w = 0 := by
    have hs' : Cospherical (φ '' s) := by
      obtain ⟨Z, r, hr⟩ := hs
      refine ⟨φ Z, r, ?_⟩
      rintro _ ⟨X, hX, rfl⟩
      rw [hφdist]
      exact hr X hX
    obtain ⟨u,v,w,hh⟩ := LeanFlowProofs.PB009.cosphericalEquation (φ '' s) hs'
    exact ⟨u,v,w,fun X hX => hh (φ X) ⟨X,hX,rfl⟩⟩
  have hR1 : φ R 1 = 0 := by
    obtain ⟨t,_,ht⟩ := hcolcoord B C R hBC hR.2.2
    simpa [hB1,hC1] using ht
  have hRG0 : φ R 0 ≠ (c-b)/2 := by
    intro hh
    apply hR.1
    apply hφinj
    ext i
    fin_cases i
    · exact hh.trans hG0.symm
    · exact hR1.trans hG1.symm
  obtain ⟨ur,vr,wr,hcr⟩ := hcircle {R,A,H,G} hR.2.1
  have hrA := hcr A (by simp)
  have hrH := hcr H (by simp)
  have hrG := hcr G (by simp)
  have hrR := hcr R (by simp)
  simp only [hA0,hA1,hH0,hH1,hG0,hG1,hR1,zero_pow (by decide : 2 ≠ 0),
    mul_zero,zero_add,add_zero,sub_zero] at hrA hrH hrG hrR
  obtain ⟨hbc,hR0⟩ := LeanFlowProofs.PB009.ahgSecondIntersection a b c ur vr wr (φ R 0)
    ha hb hc hacute hrA hrH hrG hrR hRG0
  have hEline : E ∈ affineSpan ℝ ({A,C} : Set ℝ²) := by
    have he : T.points '' ({1}ᶜ : Set (Fin 3)) = ({A,C} : Set ℝ²) := by
      ext X
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i <;> simp_all [T]
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
    rw [hE]
    simpa only [← he] using T.altitudeFoot_mem_affineSpan_image_compl 1
  have hFline : F ∈ affineSpan ℝ ({A,B} : Set ℝ²) := by
    have he : T.points '' ({2}ᶜ : Set (Fin 3)) = ({A,B} : Set ℝ²) := by
      ext X
      simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        fin_cases i <;> simp_all [T]
      · rintro (rfl | rfl)
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    rw [hF]
    simpa only [← he] using T.altitudeFoot_mem_affineSpan_image_compl 2
  have hEorth : inner ℝ (C-A) (B-E) = 0 := by
    have h1 := T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i:=1) (j:=0) (by decide)
    have h2 := T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i:=1) (j:=2) (by decide)
    simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, ← hE,
      vsub_eq_sub] at h1 h2
    change inner ℝ (C-E) (B-E) = 0 at h2
    rw [show C-A = (C-E)-(A-E) by abel, inner_sub_left, h1,h2,sub_self]
  have hForth : inner ℝ (B-A) (C-F) = 0 := by
    have h1 := T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i:=2) (j:=0) (by decide)
    have h2 := T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i:=2) (j:=1) (by decide)
    simp only [T, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, ← hF,
      vsub_eq_sub] at h1 h2
    change inner ℝ (A-F) (C-F) = 0 at h1
    change inner ℝ (B-F) (C-F) = 0 at h2
    rw [show B-A = (B-F)-(A-F) by abel, inner_sub_left, h1,h2,sub_self]
  have hacden : 0 < a^2+c^2 := by positivity
  have habden : 0 < a^2+b^2 := by positivity
  have hEcoords : φ E 0 = c*(a^2-b*c)/(a^2+c^2) ∧
      φ E 1 = a*c*(b+c)/(a^2+c^2) := by
    obtain ⟨t,hx,hy⟩ := hlinecoord A C E hEline
    have hh := hφinner C A B E
    rw [hEorth,hA0,hA1,hB0,hB1,hC0,hC1] at hh
    simp only [hA0,hA1,hC0,hC1,sub_zero,mul_zero,zero_add,add_zero,zero_sub] at hx hy
    simp only [hx,hy] at hh ⊢
    constructor <;> apply (eq_div_iff hacden.ne').mpr
    · linear_combination -c * hh
    · linear_combination a * hh
  have hFcoords : φ F 0 = -b*(a^2-b*c)/(a^2+b^2) ∧
      φ F 1 = a*b*(b+c)/(a^2+b^2) := by
    obtain ⟨t,hx,hy⟩ := hlinecoord A B F hFline
    have hh := hφinner B A C F
    rw [hForth,hA0,hA1,hB0,hB1,hC0,hC1] at hh
    simp only [hA0,hA1,hB0,hB1,sub_zero,mul_zero,zero_add,add_zero,zero_sub] at hx hy
    simp only [hx,hy] at hh ⊢
    constructor <;> apply (eq_div_iff habden.ne').mpr
    · linear_combination b * hh
    · linear_combination a * hh
  let d := c-b
  let m := b+c
  let e := a^2-b*c
  let T0 := a^2+b*c
  let U := 4*a^2+d^2
  let W := a^2*d^2+T0^2
  have hd : d ≠ 0 := sub_ne_zero.mpr hbc.symm
  have he : 0 < e := sub_pos.mpr hacute
  have hm : 0 < m := add_pos hb hc
  have hT : 0 < T0 := by dsimp [T0]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hM0 : φ M 0 = 0 := by rw [hM,hφmid]; simp [midpoint_eq_smul_add,hA0,hH0]
  have hM1 : φ M 1 = T0/(2*a) := by
    rw [hM,hφmid]
    simp [midpoint_eq_smul_add,hA1,hH1]
    dsimp [T0]
    field_simp
  have hAGproj (Z V : ℝ²) (hv : V = orthogonalProjection (affineSpan ℝ {A,G}) Z) :
      φ V 0 = d*(2*a^2+d*φ Z 0-2*a*φ Z 1)/U ∧
      φ V 1 = (a*d^2-2*a*d*φ Z 0+4*a^2*φ Z 1)/U := by
    obtain ⟨⟨t,hx,hy⟩,hh⟩ := hprojcoord A G Z V hv
    simp only [hA0,hA1,hG0,hG1] at hx hy hh
    change φ V 0 = t * (d/2-0)+0 at hx
    change φ V 1 = t * (0-a)+a at hy
    change (d/2-0)*(φ V 0-φ Z 0)+(0-a)*(φ V 1-φ Z 1)=0 at hh
    simp only [hx,hy] at hh ⊢
    constructor <;> apply (eq_div_iff hU.ne').mpr <;> dsimp [U]
    · linear_combination 2*d*hh
    · linear_combination -4*a*hh
  have hIcoords : φ I 0 = d*(2*a^2-b*d)/U ∧ φ I 1 = a*d*m/U := by
    obtain ⟨hx,hy⟩ := hAGproj B I hI
    rw [hB0,hB1] at hx hy
    constructor
    · rw [hx]; congr 1; ring
    · rw [hy]; dsimp [d,m]; congr 1; ring
  have hJcoords : φ J 0 = d*(2*a^2+c*d)/U ∧ φ J 1 = -(a*d*m)/U := by
    obtain ⟨hx,hy⟩ := hAGproj C J hJ
    rw [hC0,hC1] at hx hy
    constructor
    · rw [hx]; congr 1; ring
    · rw [hy]; dsimp [d,m]; congr 1; ring
  have hLcoords : φ L 0 = d*e/U ∧ φ L 1 = a*(2*T0+d^2)/U := by
    obtain ⟨hx,hy⟩ := hAGproj M L hL
    rw [hM0,hM1] at hx hy
    constructor
    · rw [hx]; dsimp [e,T0]; field_simp; ring
    · rw [hy]; dsimp [T0]; field_simp; ring
  have hAH : A ≠ H := by
    intro hh
    have ht : a = b*c/a := hA1.symm.trans ((congrArg (fun X => φ X 1) hh).trans hH1)
    have ht' := (eq_div_iff ha.ne').mp ht
    nlinarith only [ht',hacute]
  have hS0 : φ S 0 = 0 := by
    obtain ⟨t,hx,_⟩ := hcolcoord A H S hAH hS.1
    simpa [hA0,hH0] using hx
  have hEF : E ≠ F := by
    intro hh
    have hex : 0 < φ E 0 := by rw [hEcoords.1]; exact div_pos (mul_pos hc he) hacden
    have hfx : φ F 0 < 0 := by
      rw [hFcoords.1]
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hb) he) habden
    rw [hh] at hex
    linarith
  have hEFline (X : ℝ²) (hx : X = E ∨ X = F) : -d * φ X 0 + (T0/a)*φ X 1 = 2*b*c := by
    rcases hx with rfl | rfl
    · rw [hEcoords.1,hEcoords.2]; dsimp [d,T0]; field_simp; ring
    · rw [hFcoords.1,hFcoords.2]; dsimp [d,T0]; field_simp; ring
  have hS1 : φ S 1 = 2*a*b*c/T0 := by
    obtain ⟨t,hx,hy⟩ := hcolcoord E F S hEF hS.2
    have hel := hEFline E (Or.inl rfl)
    have hfl := hEFline F (Or.inr rfl)
    have hsline : -d*φ S 0 + (T0/a)*φ S 1 = 2*b*c := by
      rw [hx,hy]
      linear_combination (1-t)*hel+t*hfl
    rw [hS0] at hsline
    apply (eq_div_iff hT.ne').mpr
    field_simp at hsline
    nlinarith only [hsline]
  have hNcoords : φ N 0 = 2*a*b*c*(a*d)/W ∧ φ N 1 = 2*a*b*c*T0/W := by
    obtain ⟨⟨t,hx,hy⟩,hh⟩ := hprojcoord R S D N hN
    simp only [hR0,hR1,hS0,hS1,hD0,hD1] at hx hy hh
    change (0-2*b*c/d)*(φ N 0-0)+(2*a*b*c/T0-0)*(φ N 1-0)=0 at hh
    change φ N 0 = t*(0-2*b*c/d)+2*b*c/d at hx
    have hn : -T0*φ N 0+a*d*φ N 1=0 := by
      calc
        _ = (d*T0/(2*b*c))*((0-2*b*c/d)*(φ N 0-0)+(2*a*b*c/T0-0)*(φ N 1-0)) := by
          field_simp; ring
        _ = 0 := by rw [hh,mul_zero]
    have hl : a*d*φ N 0+T0*φ N 1=2*a*b*c := by
      rw [hx,hy]
      field_simp
      ring
    constructor <;> apply (eq_div_iff hW.ne').mpr <;> dsimp [W]
    · linear_combination a*d*hl-T0*hn
    · linear_combination T0*hl+a*d*hn
  let s := a*b*c/W
  have hspos : 0 < s := by dsimp [s]; positivity
  have hOcoords : φ O 0 = s*(a*d) ∧ φ O 1 = s*T0 := by
    rw [hO,hφmid]
    simp only [midpoint_eq_smul_add, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul,
      hD0,hD1,hNcoords.1,hNcoords.2, invOf_eq_inv]
    dsimp [s]
    constructor <;> field_simp <;> ring
  have hDN : D ≠ N := by
    intro hh
    have hnpos : 0 < φ N 1 := by rw [hNcoords.2]; positivity
    rw [← hh,hD1] at hnpos
    exact lt_irrefl _ hnpos
  obtain ⟨tp,hp0,hp1⟩ := hcolcoord D N P hDN hP.2.1
  simp only [hD0,hD1,hNcoords.1,hNcoords.2,sub_zero,add_zero] at hp0 hp1
  let t := tp*(2*a*b*c/W)
  have hP0 : φ P 0 = t*a*d := by rw [hp0]; dsimp [t]; ring
  have hP1 : φ P 1 = t*T0 := by rw [hp1]; dsimp [t]; ring
  have ht : t ≠ 0 := by
    intro ht
    apply hP.1
    apply hφinj
    ext i
    fin_cases i
    · simp [hP0,ht,hD0]
    · simp [hP1,ht,hD1]
  have hQ1 : φ Q 1 = 0 := by
    obtain ⟨t,_,ht⟩ := hcolcoord B C Q hBC hQ.2.2
    simpa [hB1,hC1] using ht
  have hQc : φ Q 0 ≠ c := by
    intro hq
    apply hQ.1
    apply hφinj
    ext i
    fin_cases i
    · exact hq.trans hC0.symm
    · exact hQ1.trans hC1.symm
  have hDzero : φ D = 0 := by
    ext i
    fin_cases i <;> simp [hD0,hD1]
  have htransfer (ss : Set ℝ²) (hss : Cospherical ss) (hDs : D ∈ ss)
      (p q : ℝ²) (hp : p ∈ ss) (hq : q ∈ ss)
      (hpD : p ≠ D) (hqD : q ≠ D) (hpq : p ≠ q)
      (f u v : ℝ) (hf : f ≠ 0)
      (hpc : f*((φ p 0)^2+(φ p 1)^2)-u*φ p 0-v*φ p 1=0)
      (hqc : f*((φ q 0)^2+(φ q 1)^2)-u*φ q 0-v*φ q 1=0) :
      ∀ X ∈ ss, f*((φ X 0)^2+(φ X 1)^2)-u*φ X 0-v*φ X 1=0 := by
    have himg : Cospherical (φ '' ss) := by
      obtain ⟨Z,r,hr⟩ := hss
      refine ⟨φ Z,r,?_⟩
      rintro _ ⟨X,hX,rfl⟩
      rw [hφdist]
      exact hr X hX
    have hpz : φ p ≠ 0 := by intro hh; exact hpD (hφinj (hh.trans hDzero.symm))
    have hqz : φ q ≠ 0 := by intro hh; exact hqD (hφinj (hh.trans hDzero.symm))
    have hnorm (X : ℝ²) (hh : f*((φ X 0)^2+(φ X 1)^2)-u*φ X 0-v*φ X 1=0) :
        (φ X 0)^2+(φ X 1)^2 = (u/f)*φ X 0+(v/f)*φ X 1 := by
      rw [show (u/f)*φ X 0+(v/f)*φ X 1 = (u*φ X 0+v*φ X 1)/f by ring,
        eq_div_iff hf]
      linear_combination hh
    have hh := LeanFlowProofs.PB009.originCircleTransfer (φ '' ss) himg
      (show (0 : ℝ²) ∈ φ '' ss from ⟨D,hDs,hDzero⟩)
      (φ p) (φ q) ⟨p,hp,rfl⟩ ⟨q,hq,rfl⟩ hpz hqz
      (fun hh => hpq (hφinj hh)) (u/f) (v/f) (hnorm p hpc) (hnorm q hqc)
    intro X hX
    have hx := hh (φ X) ⟨X,hX,rfl⟩
    calc
      _ = f*((φ X 0)^2+(φ X 1)^2-((u/f)*φ X 0+(v/f)*φ X 1)) := by field_simp; ring
      _ = 0 := by rw [hx]; ring
  have hdetDistinct (p q : ℝ²) (hh : φ p 0*φ q 1-φ p 1*φ q 0 ≠ 0) :
      p ≠ D ∧ q ≠ D ∧ p ≠ q := by
    refine ⟨?_,?_,?_⟩
    · rintro rfl; simp [hD0,hD1] at hh
    · rintro rfl; simp [hD0,hD1] at hh
    · rintro rfl; apply hh; ring
  let f1 := 3*a^2+b^2-2*b*c
  let f2 := 3*a^2+c^2-2*b*c
  let n1 := a^2*(c-2*b)-b*(c^2-b*c+b^2)
  let n2 := a^2*(2*c-b)+c*(b^2-b*c+c^2)
  let z1 := a^2*T0-b^2*c*d
  let z2 := a^2*T0+b*c^2*d
  let F1 : ℝ → ℝ → ℝ := fun x y => a*f1*(x^2+y^2)-a*n1*x-z1*y
  let F2 : ℝ → ℝ → ℝ := fun x y => a*f2*(x^2+y^2)-a*n2*x-z2*y
  let F0 : ℝ → ℝ → ℝ := fun x y => a*d*(x^2+y^2)-a*(T0+d^2)*x-b*c*d*y
  have hfirst : 0 < f1 ∧ 0 < f2 ∧
      F1 (φ I 0) (φ I 1) = 0 ∧ F1 (φ F 0) (φ F 1) = 0 ∧
      F2 (φ J 0) (φ J 1) = 0 ∧ F2 (φ E 0) (φ E 1) = 0 ∧
      φ I 0*φ F 1-φ I 1*φ F 0 ≠ 0 ∧ φ J 0*φ E 1-φ J 1*φ E 0 ≠ 0 := by
    rw [hIcoords.1,hIcoords.2,hFcoords.1,hFcoords.2,hJcoords.1,hJcoords.2,hEcoords.1,hEcoords.2]
    exact LeanFlowProofs.PB009.firstCircleCertificates a b c ha hb hc hacute hbc
  obtain ⟨hf1,hf2,hFI,hFF,hFJ,hFE,hIFdet,hJEdet⟩ := hfirst
  obtain ⟨hID,hFD,hIF⟩ := hdetDistinct I F hIFdet
  obtain ⟨hJD,hED,hJE⟩ := hdetDistinct J E hJEdet
  have hKf1 : F1 (φ K 0) (φ K 1) = 0 :=
    htransfer {K,D,I,F} hK.2.1 (by simp) I F (by simp) (by simp)
      hID hFD hIF (a*f1) (a*n1) z1 (mul_ne_zero ha.ne' hf1.ne') hFI hFF K (by simp)
  have hKf2 : F2 (φ K 0) (φ K 1) = 0 :=
    htransfer {K,D,J,E} hK.2.2 (by simp) J E (by simp) (by simp)
      hJD hED hJE (a*f2) (a*n2) z2 (mul_ne_zero ha.ne' hf2.ne') hFJ hFE K (by simp)
  have hpencil : (∀ x y, F2 x y-F1 x y=m*F0 x y) ∧
      F0 (φ L 0) (φ L 1)=0 ∧ 0 < F1 (φ L 0) (φ L 1) ∧ 0 < φ L 1 := by
    rw [hLcoords.1,hLcoords.2]
    exact LeanFlowProofs.PB009.pencilCertificates a b c ha hb hc hacute
  obtain ⟨hpencil,hLf0,hLf1,hLy⟩ := hpencil
  have hKf0 : F0 (φ K 0) (φ K 1)=0 := by
    have hh := hpencil (φ K 0) (φ K 1)
    rw [hKf1,hKf2,sub_self] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hm.ne'
  have hKL : K ≠ L := by
    intro hh
    rw [hh] at hKf1
    exact (ne_of_gt hLf1) hKf1
  have hLD : L ≠ D := by
    intro hh
    rw [hh,hD1] at hLy
    exact lt_irrefl _ hLy
  have hPf0 : F0 (φ P 0) (φ P 1)=0 :=
    htransfer {P,D,K,L} hP.2.2 (by simp) K L (by simp) (by simp)
      hK.1 hLD hKL (a*d) (a*(T0+d^2)) (b*c*d) (mul_ne_zero ha.ne' hd)
      hKf0 hLf0 P (by simp)
  obtain ⟨uq,vq,wq,hcq⟩ := hcircle {Q,O,C,P} hQ.2.1
  have hqO := hcq O (by simp)
  have hqP := hcq P (by simp)
  have hqC := hcq C (by simp)
  have hqQ := hcq Q (by simp)
  simp only [hOcoords.1,hOcoords.2,hP0,hP1,hC0,hC1,hQ1,
    zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,sub_zero] at hqO hqP hqC hqQ
  have hpf : a*d*((t*a*d)^2+(t*T0)^2)-a*(T0+d^2)*(t*a*d)-b*c*d*(t*T0)=0 := by
    simpa only [F0,hP0,hP1] using hPf0
  have hcompletion := LeanFlowProofs.PB009.scalarCompletion a b c ha hb hc hbc
    t (φ Q 0) uq vq wq ht hQc hpf (by simpa only [s,W,T0,d,mul_assoc] using hqO) hqP hqC hqQ
  have hQ0 : φ Q 0 = b := hcompletion.2
  have hdist2 : dist A B ^ 2 = dist A Q ^ 2 := by
    have hb' := hφinner A B A B
    have hq' := hφinner A Q A Q
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm] at hb' hq'
    simp only [hA0,hA1,hB0,hB1,hQ0,hQ1] at hb' hq'
    nlinarith only [hb',hq']
  nlinarith only [hdist2,dist_nonneg (x:=A) (y:=B),dist_nonneg (x:=A) (y:=Q)]
  }))

