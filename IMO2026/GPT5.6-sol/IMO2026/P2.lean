import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

open Affine EuclideanGeometry Module

namespace IMO2026P2

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- If the antipode of `A` about `O` is equidistant from `B` and `C`, then `O` is
equidistant from the midpoints of `AB` and `AC`. -/
private lemma dist_midpoints_of_antipode_dist_eq {A B C O : P}
    (h : dist (Equiv.pointReflection O A) B = dist (Equiv.pointReflection O A) C) :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) := by
  let Z := Equiv.pointReflection O A
  have hO : O = midpoint ℝ A Z := by
    simpa [Z] using (AffineEquiv.midpoint_pointReflection_right ℝ O A).symm
  have hh : ‖Z -ᵥ B‖ = ‖Z -ᵥ C‖ := by
    simpa [Z, dist_eq_norm_vsub] using h
  rw [hO]
  simp only [dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left, norm_smul]
  rw [hh]

lemma result_reduce_midpoints {A B C M N O : P}
    (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C) :
    (dist O M = dist O N ↔
      dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C)) := by
  subst M
  subst N
  rfl

/-- Equality of powers with respect to two spheres propagates along the affine line
through two points where the powers agree. -/
private lemma sphere_power_eq_on_affine_line {s₁ s₂ : Sphere P} {X Y : P} (t : ℝ)
    (hX : s₁.power X = s₂.power X) (hY : s₁.power Y = s₂.power Y) :
    s₁.power (t • (Y -ᵥ X) +ᵥ X) = s₂.power (t • (Y -ᵥ X) +ᵥ X) := by
  simp only [Sphere.power, dist_eq_norm_vsub, vadd_vsub_assoc]
  rw [norm_add_sq_real, norm_add_sq_real]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs]
  simp only [starRingEnd_apply, star_trivial]
  simp only [Sphere.power, dist_eq_norm_vsub] at hX hY
  have hY₁ : ‖Y -ᵥ X + (X -ᵥ s₁.center)‖ ^ 2 - s₁.radius ^ 2 =
      ‖Y -ᵥ X + (X -ᵥ s₂.center)‖ ^ 2 - s₂.radius ^ 2 := by
    simpa [vsub_add_vsub_cancel] using hY
  rw [norm_add_sq_real, norm_add_sq_real] at hY₁
  linear_combination t * hY₁ + (1 - t) * hX

/-- A point in a triangle's interior is strictly on the same side of each opposite
face as the corresponding vertex. -/
private lemma sSameSide_vertex_of_mem_triangle_interior (t : Triangle ℝ P) {Q : P}
    (hQ : Q ∈ t.interior) (i : Fin 3) :
    (affineSpan ℝ (Set.range (t.faceOpposite i).points)).SSameSide Q (t.points i) := by
  rcases hQ with ⟨w, hw, hwi, rfl⟩
  exact (t.sSameSide_affineSpan_faceOpposite_point_right_iff hw).2 (hwi i).1

private lemma sSameSide_AB_of_mem_interior_ABL {A B K L : P}
    (h : AffineIndependent ℝ ![A, B, L])
    (hK : K ∈ (⟨![A, B, L], h⟩ : Triangle ℝ P).interior) :
    line[ℝ, A, B].SSameSide K L := by
  have hs := sSameSide_vertex_of_mem_triangle_interior
      (⟨![A, B, L], h⟩ : Triangle ℝ P) hK (2 : Fin 3)
  rw [Simplex.range_faceOpposite_points] at hs
  have heq : ((fun a => ![A, B, L] a) '' ({2}ᶜ : Set (Fin 3))) = {A, B} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  rw [heq] at hs
  exact hs

private lemma sSameSide_edge02_of_mem_triangle_interior {X Y Z Q : P}
    (h : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ (⟨![X, Y, Z], h⟩ : Triangle ℝ P).interior) :
    line[ℝ, X, Z].SSameSide Q Y := by
  have hs := sSameSide_vertex_of_mem_triangle_interior
      (⟨![X, Y, Z], h⟩ : Triangle ℝ P) hQ (1 : Fin 3)
  rw [Simplex.range_faceOpposite_points] at hs
  have heq : ((fun a => ![X, Y, Z] a) '' ({1}ᶜ : Set (Fin 3))) = {X, Z} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with (rfl | rfl)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  rw [heq] at hs
  exact hs

/-- A point in a triangle's interior lies on a segment from the first vertex to
an interior point of the opposite edge, with both parameters strict. -/
private lemma exists_nested_open_segment_of_mem_triangle_interior {X Y Z Q : P}
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).interior) :
    ∃ u v : ℝ, u ∈ Set.Ioo 0 1 ∧ v ∈ Set.Ioo 0 1 ∧
      Q = u • ((v • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X := by
  rcases hQ with ⟨w, hw, hwi, rfl⟩
  let u := w 1 + w 2
  let v := w 2 / u
  have h1 := (hwi 1).1
  have h2 := (hwi 2).1
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 := by
    have h0 := (hwi 0).1
    dsimp [u]
    rw [Fin.sum_univ_three] at hw
    linarith
  have hv0 : 0 < v := by exact div_pos h2 hu0
  have hv1 : v < 1 := by
    dsimp [v, u]
    rw [div_lt_one (by linarith)]
    linarith
  refine ⟨u, v, ⟨hu0, hu1⟩, ⟨hv0, hv1⟩, ?_⟩
  dsimp [u, v]
  have hne : w 1 + w 2 ≠ 0 := ne_of_gt hu0
  have hmul : (w 1 + w 2) * (w 2 / (w 1 + w 2)) = w 2 := by
    field_simp
  change (Finset.affineCombination ℝ Finset.univ ![X, Y, Z]) w =
    (w 1 + w 2) • (((w 2 / (w 1 + w 2)) • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![X, Y, Z] (by simpa using hw) X]
  rw [vadd_right_cancel_iff X]
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three]
  rw [vadd_vsub_assoc, smul_add, smul_smul, hmul]
  rw [← vsub_add_vsub_cancel Z Y X]
  module

/-- An undirected angle equality determines a cyclic quadrilateral once a strict
same-side hypothesis selects the oriented-angle branch. -/
private lemma cospherical_of_angle_eq_of_same_side [Module.Oriented ℝ V (Fin 2)]
    {p₁ p₂ p₃ p₄ : P}
    (hangle : ∠ p₁ p₂ p₄ = ∠ p₁ p₃ p₄)
    (hside : line[ℝ, p₁, p₄].SSameSide p₂ p₃)
    (hn : ¬ Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hsign : (∡ p₁ p₂ p₄).sign = (∡ p₁ p₃ p₄).sign :=
    (hside.oangle_sign_eq (left_mem_affineSpan_pair ℝ p₁ p₄)
      (right_mem_affineSpan_pair ℝ p₁ p₄)).symm
  have ho : ∡ p₁ p₂ p₄ = ∡ p₁ p₃ p₄ :=
    oangle_eq_of_angle_eq_of_sign_eq hangle hsign
  apply cospherical_of_two_zsmul_oangle_eq_of_not_collinear _ hn
  rw [ho]

private lemma pointReflection_apollonius {A B O : P} :
    dist (Equiv.pointReflection O A) B ^ 2 + dist A B ^ 2 =
      2 * (dist O A ^ 2 + dist O B ^ 2) := by
  rw [show Equiv.pointReflection O A = (O -ᵥ A) +ᵥ O by
    exact Equiv.pointReflection_apply O A]
  simp only [dist_eq_norm_vsub, vadd_vsub_assoc]
  have h := parallelogram_law (𝕜 := ℝ) (x := O -ᵥ A) (y := O -ᵥ B)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  convert h using 1 <;> simp
  simpa only [← dist_eq_norm_vsub] using dist_comm A B

private lemma pointReflection_equidistant_iff_power_balance {A B C O : P} :
    dist (Equiv.pointReflection O A) B = dist (Equiv.pointReflection O A) C ↔
      2 * dist O B ^ 2 - dist A B ^ 2 =
        2 * dist O C ^ 2 - dist A C ^ 2 := by
  have hB := pointReflection_apollonius (A := A) (B := B) (O := O)
  have hC := pointReflection_apollonius (A := A) (B := C) (O := O)
  constructor
  · intro h
    rw [h] at hB
    nlinarith
  · intro h
    have hs : dist (Equiv.pointReflection O A) B ^ 2 =
        dist (Equiv.pointReflection O A) C ^ 2 := by
      nlinarith
    have hnB : 0 ≤ dist (Equiv.pointReflection O A) B := dist_nonneg
    have hnC : 0 ≤ dist (Equiv.pointReflection O A) C := dist_nonneg
    nlinarith

private lemma sphere_power_eq_of_mem_triangle_interior
    {s₁ s₂ : Sphere P} {X Y Z Q : P}
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).interior)
    (hX : s₁.power X = s₂.power X)
    (hY : s₁.power Y = s₂.power Y)
    (hZ : s₁.power Z = s₂.power Z) :
    s₁.power Q = s₂.power Q := by
  rcases exists_nested_open_segment_of_mem_triangle_interior hXYZ hQ with
    ⟨u, v, hu, hv, rfl⟩
  let R : P := v • (Z -ᵥ Y) +ᵥ Y
  have hR : s₁.power R = s₂.power R := by
    exact sphere_power_eq_on_affine_line v hY hZ
  exact sphere_power_eq_on_affine_line u hX hR

private lemma sphere_power_line_interpolation {s : Sphere P} {X Y : P} (t : ℝ) :
    s.power (t • (Y -ᵥ X) +ᵥ X) =
      (1 - t) * s.power X + t * s.power Y - t * (1 - t) * dist X Y ^ 2 := by
  simp only [Sphere.power, dist_eq_norm_vsub, vadd_vsub_assoc]
  rw [norm_add_sq_real]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs]
  simp only [starRingEnd_apply, star_trivial]
  rw [show Y -ᵥ s.center = (Y -ᵥ X) + (X -ᵥ s.center) by
    rw [vsub_add_vsub_cancel]]
  rw [norm_add_sq_real]
  rw [mul_pow, sq_abs]
  have hdist : ‖X -ᵥ Y‖ ^ 2 = ‖Y -ᵥ X‖ ^ 2 := by
    congr 1
    simpa only [← dist_eq_norm_vsub] using dist_comm X Y
  rw [hdist]
  ring

private lemma dist_midpoints_iff_power_balance {A B C O : P} :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) ↔
      2 * dist O B ^ 2 - dist A B ^ 2 =
        2 * dist O C ^ 2 - dist A C ^ 2 := by
  rw [← pointReflection_equidistant_iff_power_balance]
  let Z := Equiv.pointReflection O A
  have hO : O = midpoint ℝ A Z := by
    simpa [Z] using (AffineEquiv.midpoint_pointReflection_right ℝ O A).symm
  rw [hO]
  simp only [dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left, norm_smul]
  simp [Z]

lemma coordinate_tangent_circumcenter_identity_of_construction
    (x y c u v : ℝ) (hx : x ≠ 2) (hy : y ≠ 0)
    (hc : c = ((1 - x) * y ^ 2 + x * (x - 1) * (2 - x)) / (2 * y))
    (hu : u = y * (2 * c - v) / (2 - x)) :
    x * ((x - 1) ^ 2 + y ^ 2 - c ^ 2) *
        (((u - 2) * y - v * (x - 2)) * (v - c) -
          u * ((u - 2) * (x - 2) + v * y)) =
      (c * (2 - x) - y) *
        ((v + c * u) * (x ^ 2 + y ^ 2) +
          (-y - c * x) * (u ^ 2 + v ^ 2) -
          (1 - c ^ 2) * (x * v - y * u)) := by
  subst c
  subst u
  field_simp
  ring

private lemma affineIndependent_fin3_pairwise_ne {X Y Z : P}
    (h : AffineIndependent ℝ ![X, Y, Z]) :
    X ≠ Y ∧ X ≠ Z ∧ Y ≠ Z := by
  have hi := h.injective
  constructor
  · exact hi.ne (by decide : (0 : Fin 3) ≠ 1)
  constructor
  · exact hi.ne (by decide : (0 : Fin 3) ≠ 2)
  · exact hi.ne (by decide : (1 : Fin 3) ≠ 2)

private lemma symmetric_nested_barycentric_family
    (h k : ℝ) (hh0 : 0 < h) (hh13 : h < 1 / 3)
    (hl : (1 - h) / 2 < k) (hu : k < 1 - h) :
    0 < 2 * k + h - 1 ∧
    0 < 2 * (1 - h - k) ∧
    0 < (k - h) * (1 - k - h) / k ∧
    0 < (k ^ 2 - h ^ 2) / k ∧
    0 < h / k ∧
    (2 * k + h - 1) + 2 * (1 - h - k) + h = 1 ∧
    (k - h) * (1 - k - h) / k + (k ^ 2 - h ^ 2) / k + h / k = 1 := by
  have hk0 : 0 < k := by nlinarith
  have hhk : h < k := by nlinarith
  have hsum : k + h < 1 := by nlinarith
  have hsq : 0 < k ^ 2 - h ^ 2 := by nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · exact div_pos (mul_pos (sub_pos.mpr hhk) (by nlinarith)) hk0
  constructor
  · exact div_pos hsq hk0
  constructor
  · exact div_pos hh0 hk0
  constructor
  · ring
  field_simp
  ring

private lemma sphere_power_nested_chord_identity
    {s : Sphere P} {A K L : P} (u v : ℝ)
    (hA : s.power A = 0) (hK : s.power K = 0) (hL : s.power L = 0) :
    s.power
        (u • ((v • (L -ᵥ K) +ᵥ K) -ᵥ A) +ᵥ A) =
      -u * (1 - u) * dist A (v • (L -ᵥ K) +ᵥ K) ^ 2 -
        u * v * (1 - v) * dist K L ^ 2 := by
  rw [sphere_power_line_interpolation]
  rw [hA, sphere_power_line_interpolation, hK, hL]
  ring

private lemma sphere_power_nested_chord_eq_iff
    {s : Sphere P} {A K L : P} (u v u' v' : ℝ)
    (hA : s.power A = 0) (hK : s.power K = 0) (hL : s.power L = 0) :
    s.power (u • ((v • (L -ᵥ K) +ᵥ K) -ᵥ A) +ᵥ A) =
        s.power (u' • ((v' • (L -ᵥ K) +ᵥ K) -ᵥ A) +ᵥ A) ↔
      u * (1 - u) * dist A (v • (L -ᵥ K) +ᵥ K) ^ 2 +
          u * v * (1 - v) * dist K L ^ 2 =
        u' * (1 - u') * dist A (v' • (L -ᵥ K) +ᵥ K) ^ 2 +
          u' * v' * (1 - v') * dist K L ^ 2 := by
  rw [sphere_power_nested_chord_identity u v hA hK hL,
    sphere_power_nested_chord_identity u' v' hA hK hL]
  constructor <;> intro h <;> linarith

private lemma coupled_angle_sum_12 {A B C K L N : P}
    (h₁ : ∠ K B A = ∠ A C L)
    (h₂ : ∠ L B K = ∠ L N C) :
    ∠ K B A + ∠ L B K = ∠ A C L + ∠ L N C := by
  rw [h₁, h₂]

private lemma coupled_angle_sums {A B C K L M N : P}
    (h₁ : ∠ K B A = ∠ A C L)
    (h₂ : ∠ L B K = ∠ L N C)
    (h₃ : ∠ L C K = ∠ B M K) :
    (∠ K B A + ∠ L B K = ∠ A C L + ∠ L N C) ∧
    (∠ L B K + ∠ L C K = ∠ L N C + ∠ B M K) ∧
    (∠ K B A + ∠ L C K = ∠ A C L + ∠ B M K) := by
  constructor
  · rw [h₁, h₂]
  constructor
  · rw [h₂, h₃]
  · rw [h₁, h₃]

private lemma inner_antipode_eq_zero_of_equidistant {A K O : P}
    (h : dist O A = dist O K) :
    inner ℝ (A -ᵥ K) (Equiv.pointReflection O A -ᵥ K) = 0 := by
  rw [Equiv.pointReflection_apply]
  simp only [vadd_vsub_assoc]
  have hn0 : ‖O -ᵥ A‖ = ‖O -ᵥ K‖ := by
    simpa [dist_eq_norm_vsub] using h
  have hn := congrArg (fun x : ℝ => x ^ 2) hn0
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at hn
  have hv : A -ᵥ K = (O -ᵥ K) - (O -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_left]
  rw [hv, inner_sub_left, inner_add_right, inner_add_right]
  rw [real_inner_comm (O -ᵥ K) (O -ᵥ A)]
  linarith

private lemma inner_diameter_endpoint_identity {A K O : P} :
    inner ℝ (A -ᵥ K) (Equiv.pointReflection O A -ᵥ K) =
      dist O K ^ 2 - dist O A ^ 2 := by
  rw [Equiv.pointReflection_apply]
  simp only [vadd_vsub_assoc, dist_eq_norm_vsub]
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  have hv : A -ᵥ K = (O -ᵥ K) - (O -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_left]
  rw [hv, inner_sub_left, inner_add_right, inner_add_right]
  rw [real_inner_comm (O -ᵥ K) (O -ᵥ A)]
  ring

private lemma inner_antipode_vertices_eq_zero_of_circumcenter {A K L : P}
    (h : AffineIndependent ℝ ![A, K, L]) :
    inner ℝ (A -ᵥ K)
        (Equiv.pointReflection ((⟨![A, K, L], h⟩ : Triangle ℝ P).circumcenter) A -ᵥ K) = 0 ∧
      inner ℝ (A -ᵥ L)
        (Equiv.pointReflection ((⟨![A, K, L], h⟩ : Triangle ℝ P).circumcenter) A -ᵥ L) = 0 := by
  let t : Triangle ℝ P := ⟨![A, K, L], h⟩
  have hA : dist t.circumcenter A = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 0
  have hK : dist t.circumcenter K = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 1
  have hL : dist t.circumcenter L = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 2
  constructor
  · rw [inner_diameter_endpoint_identity]
    change dist t.circumcenter K ^ 2 - dist t.circumcenter A ^ 2 = 0
    rw [hA, hK]
    ring
  · rw [inner_diameter_endpoint_identity]
    change dist t.circumcenter L ^ 2 - dist t.circumcenter A ^ 2 = 0
    rw [hA, hL]
    ring

private lemma dist_sq_sub_dist_sq_eq_inner {X Y Z : P} :
    dist Z X ^ 2 - dist Z Y ^ 2 =
      inner ℝ (X -ᵥ Y) ((X -ᵥ Z) + (Y -ᵥ Z)) := by
  rw [dist_comm Z X, dist_comm Z Y, dist_eq_norm_vsub, dist_eq_norm_vsub]
  rw [show X -ᵥ Y = (X -ᵥ Z) - (Y -ᵥ Z) by
    rw [vsub_sub_vsub_cancel_right]]
  simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq,
    real_inner_comm]
  ring

private lemma eq_of_sq_eq_sq_of_mul_nonneg {x y : ℝ}
    (hsq : x ^ 2 = y ^ 2) (hsign : 0 ≤ x * y) : x = y := by
  have hfactor : (x - y) * (x + y) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hxy : x = -y := by linarith
    rw [hxy] at hsign ⊢
    nlinarith [sq_nonneg y]

private lemma cross_mul_eq_of_sq_eq_and_same_sign {a b c d : ℝ}
    (hsq : (a * d) ^ 2 = (b * c) ^ 2)
    (hsign : 0 ≤ (a * d) * (b * c)) : a * d = b * c := by
  have hfactor : (a * d - b * c) * (a * d + b * c) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · have hopposite : a * d = -(b * c) := by linarith
    rw [hopposite] at hsign ⊢
    nlinarith [sq_nonneg (b * c)]

private lemma cross_mul_eq_or_eq_neg_of_sq_eq {a b c d : ℝ}
    (hsq : (a * d) ^ 2 = (b * c) ^ 2) :
    a * d = b * c ∨ a * d = -(b * c) := by
  have hfactor : (a * d - b * c) * (a * d + b * c) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private lemma equidistant_iff_inner_vsub_add_eq_zero {X Y Z : P} :
    dist Z X = dist Z Y ↔
      inner ℝ (X -ᵥ Y) ((X -ᵥ Z) + (Y -ᵥ Z)) = 0 := by
  have hid : dist Z X ^ 2 - dist Z Y ^ 2 =
      inner ℝ (X -ᵥ Y) ((X -ᵥ Z) + (Y -ᵥ Z)) := by
    rw [dist_comm Z X, dist_comm Z Y, dist_eq_norm_vsub, dist_eq_norm_vsub]
    rw [show X -ᵥ Y = (X -ᵥ Z) - (Y -ᵥ Z) by
      rw [vsub_sub_vsub_cancel_right]]
    simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_comm]
    ring
  constructor
  · intro h
    rw [h] at hid
    simpa using hid.symm
  · intro h
    rw [h] at hid
    have hs : dist Z X ^ 2 = dist Z Y ^ 2 := by linarith
    exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

private lemma norm_add_sq_difference_identity {x y z : V} :
    ‖x + y‖ ^ 2 - ‖x + z‖ ^ 2 =
      2 * (‖y‖ ^ 2 - ‖z‖ ^ 2) - (‖x - y‖ ^ 2 - ‖x - z‖ ^ 2) := by
  simp only [sub_eq_add_neg]
  rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
  simp only [norm_neg, inner_neg_right, starRingEnd_apply, star_trivial]
  ring

private lemma antipode_apollonius_difference {A B C O : P} :
    dist (Equiv.pointReflection O A) B ^ 2 - dist (Equiv.pointReflection O A) C ^ 2 =
      2 * (dist O B ^ 2 - dist O C ^ 2) - (dist A B ^ 2 - dist A C ^ 2) := by
  have h : ‖(O -ᵥ A) + (O -ᵥ B)‖ ^ 2 - ‖(O -ᵥ A) + (O -ᵥ C)‖ ^ 2 =
      2 * (‖O -ᵥ B‖ ^ 2 - ‖O -ᵥ C‖ ^ 2) -
        (‖(O -ᵥ A) - (O -ᵥ B)‖ ^ 2 - ‖(O -ᵥ A) - (O -ᵥ C)‖ ^ 2) := by
    simp only [sub_eq_add_neg]
    rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
    simp only [norm_neg, inner_neg_right, starRingEnd_apply, star_trivial]
    ring
  have hnAB : ‖B -ᵥ A‖ = ‖A -ᵥ B‖ := by
    simpa only [dist_eq_norm_vsub] using dist_comm B A
  have hnAC : ‖C -ᵥ A‖ = ‖A -ᵥ C‖ := by
    simpa only [dist_eq_norm_vsub] using dist_comm C A
  simpa [dist_eq_norm_vsub, Equiv.pointReflection_apply, vadd_vsub_assoc,
    vsub_sub_vsub_cancel_right, hnAB, hnAC] using h

private lemma angle_eq_expands_without_squaring
    {A B C D E F : P}
    (h : ∠ A B C = ∠ D E F) :
    Real.arccos (inner ℝ (A -ᵥ B) (C -ᵥ B) /
      (‖A -ᵥ B‖ * ‖C -ᵥ B‖)) =
    Real.arccos (inner ℝ (D -ᵥ E) (F -ᵥ E) /
      (‖D -ᵥ E‖ * ‖F -ᵥ E‖)) := by
  simpa only [EuclideanGeometry.angle, InnerProductGeometry.angle] using h

private lemma sphere_power_eq_on_nested_affine_triangle {s₁ s₂ : Sphere P}
    {X Y Z : P} (t u : ℝ)
    (hX : s₁.power X = s₂.power X)
    (hY : s₁.power Y = s₂.power Y)
    (hZ : s₁.power Z = s₂.power Z) :
    s₁.power (t • ((u • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X) =
      s₂.power (t • ((u • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X) := by
  have hYZ :
      s₁.power (u • (Z -ᵥ Y) +ᵥ Y) =
        s₂.power (u • (Z -ᵥ Y) +ᵥ Y) :=
    sphere_power_eq_on_affine_line u hY hZ
  exact sphere_power_eq_on_affine_line t hX hYZ

private lemma sphere_power_difference_affine {s₁ s₂ : Sphere P} {X Y : P} (t : ℝ) :
    s₁.power (t • (Y -ᵥ X) +ᵥ X) - s₂.power (t • (Y -ᵥ X) +ᵥ X) =
      (1 - t) * (s₁.power X - s₂.power X) +
        t * (s₁.power Y - s₂.power Y) := by
  simp only [Sphere.power, dist_eq_norm_vsub, vadd_vsub_assoc]
  rw [show Y -ᵥ s₁.center = (Y -ᵥ X) + (X -ᵥ s₁.center) by
      exact (vsub_add_vsub_cancel Y X s₁.center).symm,
    show Y -ᵥ s₂.center = (Y -ᵥ X) + (X -ᵥ s₂.center) by
      exact (vsub_add_vsub_cancel Y X s₂.center).symm]
  rw [norm_add_sq_real, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, starRingEnd_apply,
    star_trivial]
  ring

private lemma sphere_power_difference_eq_base_add_inner
    {s₁ s₂ : Sphere P} {X Q : P} :
    s₁.power X - s₂.power X =
      (s₁.power Q - s₂.power Q) +
        2 * inner ℝ (Q -ᵥ s₁.center) (X -ᵥ Q) -
        2 * inner ℝ (Q -ᵥ s₂.center) (X -ᵥ Q) := by
  simp only [Sphere.power, dist_eq_norm_vsub]
  rw [show X -ᵥ s₁.center = (X -ᵥ Q) + (Q -ᵥ s₁.center) by
    exact (vsub_add_vsub_cancel X Q s₁.center).symm]
  rw [show X -ᵥ s₂.center = (X -ᵥ Q) + (Q -ᵥ s₂.center) by
    exact (vsub_add_vsub_cancel X Q s₂.center).symm]
  rw [norm_add_sq_real, norm_add_sq_real]
  rw [real_inner_comm (Q -ᵥ s₁.center) (X -ᵥ Q),
    real_inner_comm (Q -ᵥ s₂.center) (X -ᵥ Q)]
  ring

private lemma sphere_power_eq_on_affine_plane
    {s₁ s₂ : Sphere P} {X Y Z : P} (u v : ℝ)
    (hX : s₁.power X = s₂.power X)
    (hY : s₁.power Y = s₂.power Y)
    (hZ : s₁.power Z = s₂.power Z) :
    s₁.power ((u • (Y -ᵥ X) + v • (Z -ᵥ X)) +ᵥ X) =
      s₂.power ((u • (Y -ᵥ X) + v • (Z -ᵥ X)) +ᵥ X) := by
  simp only [Sphere.power, dist_eq_norm_vsub, vadd_vsub_assoc]
  rw [norm_add_sq_real, norm_add_sq_real]
  simp only [inner_add_left, inner_smul_left, norm_add_sq_real, norm_smul,
    Real.norm_eq_abs, starRingEnd_apply, star_trivial]
  simp only [Sphere.power, dist_eq_norm_vsub] at hX hY hZ
  have hY₁ : ‖Y -ᵥ X + (X -ᵥ s₁.center)‖ ^ 2 - s₁.radius ^ 2 =
      ‖Y -ᵥ X + (X -ᵥ s₂.center)‖ ^ 2 - s₂.radius ^ 2 := by
    simpa [vsub_add_vsub_cancel] using hY
  have hZ₁ : ‖Z -ᵥ X + (X -ᵥ s₁.center)‖ ^ 2 - s₁.radius ^ 2 =
      ‖Z -ᵥ X + (X -ᵥ s₂.center)‖ ^ 2 - s₂.radius ^ 2 := by
    simpa [vsub_add_vsub_cancel] using hZ
  rw [norm_add_sq_real, norm_add_sq_real] at hY₁ hZ₁
  linear_combination u * hY₁ + v * hZ₁ + (1 - u - v) * hX

lemma coordinate_circumcenter_residual_eq_zero
    (x y c u v : ℝ)
    (hidentity :
      x * ((x - 1) ^ 2 + y ^ 2 - c ^ 2) *
          (((u - 2) * y - v * (x - 2)) * (v - c) -
            u * ((u - 2) * (x - 2) + v * y)) =
        (c * (2 - x) - y) *
          ((v + c * u) * (x ^ 2 + y ^ 2) +
            (-y - c * x) * (u ^ 2 + v ^ 2) -
            (1 - c ^ 2) * (x * v - y * u)))
    (hE : ((u - 2) * y - v * (x - 2)) * (v - c) -
      u * ((u - 2) * (x - 2) + v * y) = 0)
    (hfactor : c * (2 - x) - y ≠ 0) :
    (v + c * u) * (x ^ 2 + y ^ 2) +
        (-y - c * x) * (u ^ 2 + v ^ 2) -
        (1 - c ^ 2) * (x * v - y * u) = 0 := by
  have hproduct :
      (c * (2 - x) - y) *
        ((v + c * u) * (x ^ 2 + y ^ 2) +
          (-y - c * x) * (u ^ 2 + v ^ 2) -
          (1 - c ^ 2) * (x * v - y * u)) = 0 := by
    rw [← hidentity, hE]
    ring
  exact (mul_eq_zero.mp hproduct).resolve_left hfactor

private lemma dist_pointReflection_eq_two_mul_dist_midpoint {A B O : P} :
    dist (Equiv.pointReflection O A) B = 2 * dist O (midpoint ℝ A B) := by
  let Z := Equiv.pointReflection O A
  have hO : O = midpoint ℝ A Z := by
    simpa [Z] using (AffineEquiv.midpoint_pointReflection_right ℝ O A).symm
  rw [hO]
  simp only [dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left, norm_smul]
  simp [Z]

private lemma dist_midpoints_iff_pointReflection_equidistant {A B C O : P} :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) ↔
      dist (Equiv.pointReflection O A) B = dist (Equiv.pointReflection O A) C := by
  let Z := Equiv.pointReflection O A
  have hO : O = midpoint ℝ A Z := by
    simpa [Z] using (AffineEquiv.midpoint_pointReflection_right ℝ O A).symm
  rw [hO]
  simp only [dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left, norm_smul]
  simp [Z]

private lemma midpoint_apollonius {A B O : P} :
    4 * dist O (midpoint ℝ A B) ^ 2 + dist A B ^ 2 =
      2 * (dist O A ^ 2 + dist O B ^ 2) := by
  have h := pointReflection_apollonius (A := A) (B := B) (O := O)
  have hz : dist (Equiv.pointReflection O A) B =
      2 * dist O (midpoint ℝ A B) := by
    let Z := Equiv.pointReflection O A
    have hO : O = midpoint ℝ A Z := by
      simpa [Z] using (AffineEquiv.midpoint_pointReflection_right ℝ O A).symm
    rw [hO]
    simp only [dist_eq_norm_vsub, midpoint_vsub_midpoint_same_left, norm_smul]
    simp [Z]
  rw [hz] at h
  nlinarith

lemma coordinate_identity_singular_audit :
    let x : ℝ := 7 / 5
    let y : ℝ := 3 / 10
    let c : ℝ := 1 / 2
    (1 < x ∧ x < 2 ∧ 0 < y ∧ 0 < c) ∧
    ((1 - x) * y ^ 2 - 2 * c * y + x * (x - 1) * (2 - x) = 0) ∧
    ((x - 1) ^ 2 + y ^ 2 - c ^ 2 = 0) ∧
    (c * (2 - x) - y = 0) ∧
    ∀ v : ℝ, let u : ℝ := (1 - v) / 2
      (((u - 2) * y - v * (x - 2)) * (v - c) -
          u * ((u - 2) * (x - 2) + v * y) =
        (3 / 4 : ℝ) * (v - 1) * (v + 3 / 10)) ∧
      ((v + c * u) * (x ^ 2 + y ^ 2) +
          (-y - c * x) * (u ^ 2 + v ^ 2) -
          (1 - c ^ 2) * (x * v - y * u) =
        (-5 / 3 : ℝ) *
          (((u - 2) * y - v * (x - 2)) * (v - c) -
            u * ((u - 2) * (x - 2) + v * y))) := by
  norm_num
  intro v
  constructor <;> ring

private lemma sphere_power_sub_nested_interpolation {s₁ s₂ : Sphere P} {X Y Z : P}
    (u v : ℝ) :
    s₁.power (u • ((v • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X) -
        s₂.power (u • ((v • (Z -ᵥ Y) +ᵥ Y) -ᵥ X) +ᵥ X) =
      (1 - u) * (s₁.power X - s₂.power X) +
        u * ((1 - v) * (s₁.power Y - s₂.power Y) +
          v * (s₁.power Z - s₂.power Z)) := by
  let R : P := v • (Z -ᵥ Y) +ᵥ Y
  rw [sphere_power_line_interpolation (s := s₁) (X := X) (Y := R),
    sphere_power_line_interpolation (s := s₂) (X := X) (Y := R)]
  dsimp [R]
  rw [sphere_power_line_interpolation (s := s₁) (X := Y) (Y := Z),
    sphere_power_line_interpolation (s := s₂) (X := Y) (Y := Z)]
  ring

private lemma interior_BNC_ne_C {B N C L : P}
    (h : AffineIndependent ℝ ![B, N, C])
    (hL : L ∈ (⟨![B, N, C], h⟩ : Triangle ℝ P).interior) : L ≠ C := by
  have hs := sSameSide_vertex_of_mem_triangle_interior
      (⟨![B, N, C], h⟩ : Triangle ℝ P) hL (0 : Fin 3)
  rw [Simplex.range_faceOpposite_points] at hs
  have heq : ((fun a => ![B, N, C] a) '' ({0}ᶜ : Set (Fin 3))) = {N, C} := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · intro hx
      rcases hx with (rfl | rfl)
      · exact ⟨1, by simp, rfl⟩
      · exact ⟨2, by simp, rfl⟩
  rw [heq] at hs
  intro hLC
  subst L
  exact hs.2.1 (right_mem_affineSpan_pair ℝ N C)

private lemma angle_eq_metric_cross_identity {p q r p' q' r' : P}
    (h : ∠ p q r = ∠ p' q' r') :
    (dist p q ^ 2 + dist r q ^ 2 - dist p r ^ 2) *
        (dist p' q' * dist r' q') =
      (dist p' q' ^ 2 + dist r' q' ^ 2 - dist p' r' ^ 2) *
        (dist p q * dist r q) := by
  have h₁ :=
    dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p q r
  have h₂ :=
    dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p' q' r'
  have e₁ : dist p q ^ 2 + dist r q ^ 2 - dist p r ^ 2 =
      2 * dist p q * dist r q * Real.cos (∠ p q r) := by
    nlinarith
  have e₂ : dist p' q' ^ 2 + dist r' q' ^ 2 - dist p' r' ^ 2 =
      2 * dist p' q' * dist r' q' * Real.cos (∠ p' q' r') := by
    nlinarith
  rw [e₁, e₂, ← h]
  ring

private lemma interior_barycentric_no_opposite_coeffs {X Y Z Q : P}
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).interior) :
    ∃ w : Fin 3 → ℝ,
      (∀ i, 0 < w i) ∧
      Q = (Finset.affineCombination ℝ Finset.univ ![X, Y, Z]) w ∧
      ∀ i j, w i ≠ -w j := by
  rcases hQ with ⟨w, hw, hwi, rfl⟩
  refine ⟨w, fun i => (hwi i).1, rfl, ?_⟩
  intro i j hij
  have hi : 0 < w i := (hwi i).1
  have hj : 0 < w j := (hwi j).1
  linarith

private lemma barycentric_coordinates_unique {X : Fin 3 → P} (hX : AffineIndependent ℝ X)
    {w v : Fin 3 → ℝ}
    (hw : ∑ i ∈ Finset.univ, w i = 1)
    (hv : ∑ i ∈ Finset.univ, v i = 1)
    (heq : (Finset.affineCombination ℝ Finset.univ X) w =
      (Finset.affineCombination ℝ Finset.univ X) v) :
    w = v := by
  rw [hX.affineCombination_eq_iff_eq hw hv] at heq
  funext i
  exact heq i (Finset.mem_univ i)

private lemma normalized_coordinates_positive_of_mem_interior
    {X : Fin 3 → P} (hX : AffineIndependent ℝ X) {Q : P}
    (hQ : Q ∈ (⟨X, hX⟩ : Triangle ℝ P).interior)
    {v : Fin 3 → ℝ} (hvsum : ∑ i ∈ Finset.univ, v i = 1)
    (hvQ : Q = (Finset.affineCombination ℝ Finset.univ X) v) :
    ∀ i, 0 < v i := by
  rcases hQ with ⟨w, hwsum, hwpos, hwQ⟩
  have heq : (Finset.affineCombination ℝ Finset.univ X) w =
      (Finset.affineCombination ℝ Finset.univ X) v := hwQ.trans hvQ
  rw [hX.affineCombination_eq_iff_eq hwsum hvsum] at heq
  intro i
  rw [← heq i (Finset.mem_univ i)]
  exact (hwpos i).1

private lemma affineCombination_BmidpointC_to_ABC
    {A B C : P} (w : Fin 3 → ℝ)
    (hw : ∑ i ∈ Finset.univ, w i = 1) :
    (Finset.affineCombination ℝ Finset.univ
        ![B, midpoint ℝ A B, C]) w =
      (Finset.affineCombination ℝ Finset.univ ![A, B, C])
        ![w 1 / 2, w 0 + w 1 / 2, w 2] := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![B, midpoint ℝ A B, C]
      (by simpa using hw) A]
  have hv :
      ∑ i ∈ Finset.univ,
          (![w 1 / 2, w 0 + w 1 / 2, w 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hw
    linarith
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ ![w 1 / 2, w 0 + w 1 / 2, w 2] ![A, B, C]
      (by simpa using hv) A]
  rw [vadd_right_cancel_iff A]
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three,
    midpoint_vsub_left]
  module

private lemma exists_positive_ABC_coordinates_of_mem_interior_BmidpointC
    {A B C Q : P}
    (hBMC : AffineIndependent ℝ ![B, midpoint ℝ A B, C])
    (hQ :
      Q ∈
        (⟨![B, midpoint ℝ A B, C], hBMC⟩ :
          Triangle ℝ P).interior) :
    ∃ v : Fin 3 → ℝ,
      (∑ i ∈ Finset.univ, v i = 1) ∧
      (∀ i, 0 < v i) ∧
      Q =
        (Finset.affineCombination ℝ Finset.univ ![A, B, C]) v := by
  rcases hQ with ⟨w, hw, hwi, hwQ⟩
  have hwpos : ∀ i, 0 < w i :=
    normalized_coordinates_positive_of_mem_interior hBMC
      ⟨w, hw, hwi, hwQ⟩ hw hwQ.symm
  let v : Fin 3 → ℝ :=
    ![w 1 / 2, w 0 + w 1 / 2, w 2]
  have hvsum : ∑ i ∈ Finset.univ, v i = 1 := by
    dsimp [v]
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hw
    linarith
  have hvpos : ∀ i, 0 < v i := by
    intro i
    fin_cases i
    · dsimp [v]
      exact div_pos (hwpos 1) (by norm_num)
    · dsimp [v]
      linarith [hwpos 0, hwpos 1]
    · dsimp [v]
      exact hwpos 2
  refine ⟨v, hvsum, hvpos, ?_⟩
  exact hwQ.symm.trans
    (affineCombination_BmidpointC_to_ABC w hw)

private lemma affineCombination_BmidpointAC_C_to_ABC
    {A B C : P} (w : Fin 3 → ℝ)
    (hw : ∑ i ∈ Finset.univ, w i = 1) :
    (Finset.affineCombination ℝ Finset.univ
        ![B, midpoint ℝ A C, C]) w =
      (Finset.affineCombination ℝ Finset.univ ![A, B, C])
        ![w 1 / 2, w 0, w 1 / 2 + w 2] := by
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![B, midpoint ℝ A C, C]
      (by simpa using hw) A]
  have hv :
      ∑ i ∈ Finset.univ,
          (![w 1 / 2, w 0, w 1 / 2 + w 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hw
    linarith
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ ![w 1 / 2, w 0, w 1 / 2 + w 2] ![A, B, C]
      (by simpa using hv) A]
  rw [vadd_right_cancel_iff A]
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three,
    midpoint_vsub_left]
  module

private lemma exists_positive_ABC_coordinates_of_mem_interior_BmidpointAC_C
    {A B C Q : P}
    (hBNC : AffineIndependent ℝ ![B, midpoint ℝ A C, C])
    (hQ : Q ∈
        (⟨![B, midpoint ℝ A C, C], hBNC⟩ : Triangle ℝ P).interior) :
    ∃ v : Fin 3 → ℝ,
      (∑ i ∈ Finset.univ, v i = 1) ∧
      (∀ i, 0 < v i) ∧
      Q = (Finset.affineCombination ℝ Finset.univ ![A, B, C]) v := by
  rcases hQ with ⟨w, hw, hwi, hwQ⟩
  have hwpos : ∀ i, 0 < w i :=
    normalized_coordinates_positive_of_mem_interior hBNC
      ⟨w, hw, hwi, hwQ⟩ hw hwQ.symm
  let v : Fin 3 → ℝ := ![w 1 / 2, w 0, w 1 / 2 + w 2]
  have hvsum : ∑ i ∈ Finset.univ, v i = 1 := by
    dsimp [v]
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hw
    linarith
  have hvpos : ∀ i, 0 < v i := by
    intro i
    fin_cases i
    · dsimp [v]
      exact div_pos (hwpos 1) (by norm_num)
    · dsimp [v]
      exact hwpos 0
    · dsimp [v]
      linarith [hwpos 1, hwpos 2]
  refine ⟨v, hvsum, hvpos, ?_⟩
  exact hwQ.symm.trans
    (affineCombination_BmidpointAC_C_to_ABC w hw)

private lemma strict_ratio_order_of_nested_coordinates
    {x y u v : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hdet : 0 < x * v - y * u)
    (hA : 0 < v - y - (x * v - y * u))
    (hC : 0 < x - u - (x * v - y * u)) :
    u / x ∈ Set.Ioo 0 1 ∧ y / v ∈ Set.Ioo 0 1 ∧
      0 < x * v - y * u ∧ u < x ∧ y < v := by
  have hux : u < x := by linarith
  have hyv : y < v := by linarith
  refine ⟨⟨div_pos hu hx, (div_lt_one hx).2 hux⟩,
    ⟨div_pos hy hv, (div_lt_one hv).2 hyv⟩, hdet, hux, hyv⟩

private lemma affineCombination_ABL_to_ABC
    {A B C L : P} (l w : Fin 3 → ℝ)
    (hlsum : ∑ i ∈ Finset.univ, l i = 1)
    (hwsum : ∑ i ∈ Finset.univ, w i = 1)
    (hLcoord : L = (Finset.affineCombination ℝ Finset.univ ![A, B, C]) l) :
    (Finset.affineCombination ℝ Finset.univ ![A, B,L]) w =
      (Finset.affineCombination ℝ Finset.univ ![A, B, C])
        ![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2] := by
  have hv : ∑ i ∈ Finset.univ,
      (![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hlsum hwsum
    linear_combination w 2 * hlsum + hwsum
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![A, B, L] (by simpa using hwsum) A]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ ![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2]
      ![A, B, C] (by simpa using hv) A]
  rw [vadd_right_cancel_iff A]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ l ![A, B, C] (by simpa using hlsum) A] at hLcoord
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three] at hLcoord ⊢
  rw [hLcoord]
  simp only [vadd_vsub]
  module

private lemma affineCombination_AKC_to_ABC
    {A B C K : P} (k w : Fin 3 → ℝ)
    (hksum : ∑ i ∈ Finset.univ, k i = 1)
    (hwsum : ∑ i ∈ Finset.univ, w i = 1)
    (hKcoord : K = (Finset.affineCombination ℝ Finset.univ ![A, B, C]) k) :
    (Finset.affineCombination ℝ Finset.univ ![A, K, C]) w =
      (Finset.affineCombination ℝ Finset.univ ![A, B, C])
        ![w 0 + w 1 * k 0, w 1 * k 1, w 2 + w 1 * k 2] := by
  have hv : ∑ i ∈ Finset.univ,
      (![w 0 + w 1 * k 0, w 1 * k 1, w 2 + w 1 * k 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hksum hwsum
    linear_combination w 1 * hksum + hwsum
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ w ![A, K, C] (by simpa using hwsum) A]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ ![w 0 + w 1 * k 0, w 1 * k 1, w 2 + w 1 * k 2]
      ![A, B, C] (by simpa using hv) A]
  rw [vadd_right_cancel_iff A]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ k ![A, B, C] (by simpa using hksum) A] at hKcoord
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three] at hKcoord ⊢
  rw [hKcoord]
  simp only [vadd_vsub]
  module

private lemma strict_determinant_signs_of_nested_coordinate_identities
    (k l w z : Fin 3 → ℝ)
    (hkpos : ∀ i, 0 < k i) (hlpos : ∀ i, 0 < l i)
    (hwsum : ∑ i ∈ Finset.univ, w i = 1) (hwpos : ∀ i, 0 < w i)
    (hzsum : ∑ i ∈ Finset.univ, z i = 1) (hzpos : ∀ i, 0 < z i)
    (hkw : k = ![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2])
    (hlz : l = ![z 0 + z 1 * k 0, z 1 * k 1, z 2 + z 1 * k 2]) :
    0 < k 1 * l 2 - k 2 * l 1 ∧
      0 < l 2 - k 2 - (k 1 * l 2 - k 2 * l 1) ∧
      0 < k 1 - l 1 - (k 1 * l 2 - k 2 * l 1) := by
  have hk1 : k 1 = w 1 + w 2 * l 1 := by simpa using congrFun hkw 1
  have hk2 : k 2 = w 2 * l 2 := by simpa using congrFun hkw 2
  have hl1 : l 1 = z 1 * k 1 := by simpa using congrFun hlz 1
  have hl2 : l 2 = z 2 + z 1 * k 2 := by simpa using congrFun hlz 2
  have hD1 : k 1 * l 2 - k 2 * l 1 = w 1 * l 2 := by rw [hk1, hk2]; ring
  have hD2 : k 1 * l 2 - k 2 * l 1 = z 2 * k 1 := by rw [hl1, hl2]; ring
  have hpD : 0 < k 1 * l 2 - k 2 * l 1 := by
    rw [hD1]
    exact mul_pos (hwpos 1) (hlpos 2)
  rw [Fin.sum_univ_three] at hwsum hzsum
  constructor
  · exact hpD
  constructor
  · rw [hD1, hk2]
    have heq : l 2 - w 2 * l 2 - w 1 * l 2 = w 0 * l 2 := by
      linear_combination -(l 2) * hwsum
    rw [heq]
    exact mul_pos (hwpos 0) (hlpos 2)
  · rw [hD2, hl1]
    have heq : k 1 - z 1 * k 1 - z 2 * k 1 = z 0 * k 1 := by
      linear_combination -(k 1) * hzsum
    rw [heq]
    exact mul_pos (hzpos 0) (hkpos 1)

private lemma determinant_circumcenter_midpoint_residual
    (k₁ k₂ l₁ l₂ ob oc kk ll bb cc : ℝ)
    (hk : 2 * (k₁ * ob + k₂ * oc) = kk)
    (hl : 2 * (l₁ * ob + l₂ * oc) = ll) :
    4 * (k₁ * l₂ - k₂ * l₁) * (oc - ob) +
        (k₁ * l₂ - k₂ * l₁) * (bb - cc) =
      2 * ((k₁ + k₂) * ll - (l₁ + l₂) * kk) +
        (k₁ * l₂ - k₂ * l₁) * (bb - cc) := by
  linear_combination 2 * (k₁ + k₂) * hl - 2 * (l₁ + l₂) * hk

private lemma nondegenerate_circumcenter_antipode_residual_iff
    (k₁ k₂ l₁ l₂ ob oc kk ll bb cc : ℝ)
    (hD : k₁ * l₂ - k₂ * l₁ ≠ 0)
    (hk : 2 * (k₁ * ob + k₂ * oc) = kk)
    (hl : 2 * (l₁ * ob + l₂ * oc) = ll) :
    4 * (oc - ob) + (bb - cc) = 0 ↔
      2 * ((k₁ + k₂) * ll - (l₁ + l₂) * kk) +
        (k₁ * l₂ - k₂ * l₁) * (bb - cc) = 0 := by
  have hscale := determinant_circumcenter_midpoint_residual
    k₁ k₂ l₁ l₂ ob oc kk ll bb cc hk hl
  constructor
  · intro h
    calc
      2 * ((k₁ + k₂) * ll - (l₁ + l₂) * kk) +
          (k₁ * l₂ - k₂ * l₁) * (bb - cc) =
          4 * (k₁ * l₂ - k₂ * l₁) * (oc - ob) +
            (k₁ * l₂ - k₂ * l₁) * (bb - cc) := hscale.symm
      _ = (k₁ * l₂ - k₂ * l₁) *
          (4 * (oc - ob) + (bb - cc)) := by ring
      _ = 0 := by rw [h, mul_zero]
  · intro h
    have hscaled : (k₁ * l₂ - k₂ * l₁) *
        (4 * (oc - ob) + (bb - cc)) = 0 := by
      calc
        (k₁ * l₂ - k₂ * l₁) *
            (4 * (oc - ob) + (bb - cc)) =
            4 * (k₁ * l₂ - k₂ * l₁) * (oc - ob) +
              (k₁ * l₂ - k₂ * l₁) * (bb - cc) := by ring
        _ = 2 * ((k₁ + k₂) * ll - (l₁ + l₂) * kk) +
              (k₁ * l₂ - k₂ * l₁) * (bb - cc) := hscale
        _ = 0 := h
    exact (mul_eq_zero.mp hscaled).resolve_left hD

private lemma positive_determinant_residual_reduction
    (k₁ k₂ l₁ l₂ ob oc kk ll bb cc : ℝ)
    (hD : 0 < k₁ * l₂ - k₂ * l₁)
    (hk : 2 * (k₁ * ob + k₂ * oc) = kk)
    (hl : 2 * (l₁ * ob + l₂ * oc) = ll) :
    4 * (oc - ob) + (bb - cc) = 0 ↔
      2 * ((k₁ + k₂) * ll - (l₁ + l₂) * kk) +
        (k₁ * l₂ - k₂ * l₁) * (bb - cc) = 0 := by
  exact nondegenerate_circumcenter_antipode_residual_iff
    k₁ k₂ l₁ l₂ ob oc kk ll bb cc (ne_of_gt hD) hk hl

private lemma antipode_equidistant_of_apollonius_residual {A B C O : P}
    (h : 2 * (dist O B ^ 2 - dist O C ^ 2) -
      (dist A B ^ 2 - dist A C ^ 2) = 0) :
    dist (Equiv.pointReflection O A) B = dist (Equiv.pointReflection O A) C := by
  have hd := antipode_apollonius_difference (A := A) (B := B) (C := C) (O := O)
  rw [h] at hd
  have hs : dist (Equiv.pointReflection O A) B ^ 2 =
      dist (Equiv.pointReflection O A) C ^ 2 := by linarith
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hs

private lemma audit_coordinate_linearizes_circumcenter_equations
    {A B C K L O : P} (k₁ k₂ l₁ l₂ : ℝ)
    (hKcoord : K -ᵥ A = k₁ • (B -ᵥ A) + k₂ • (C -ᵥ A))
    (hLcoord : L -ᵥ A = l₁ • (B -ᵥ A) + l₂ • (C -ᵥ A))
    (hKcirc : 2 * inner ℝ (K -ᵥ A) (O -ᵥ A) = ‖K -ᵥ A‖ ^ 2)
    (hLcirc : 2 * inner ℝ (L -ᵥ A) (O -ᵥ A) = ‖L -ᵥ A‖ ^ 2) :
    2 * (k₁ * inner ℝ (B -ᵥ A) (O -ᵥ A) +
      k₂ * inner ℝ (C -ᵥ A) (O -ᵥ A)) = ‖K -ᵥ A‖ ^ 2 ∧
    2 * (l₁ * inner ℝ (B -ᵥ A) (O -ᵥ A) +
      l₂ * inner ℝ (C -ᵥ A) (O -ᵥ A)) = ‖L -ᵥ A‖ ^ 2 := by
  constructor
  · rw [← hKcirc, hKcoord]
    simp [inner_add_left, real_inner_smul_left]
  · rw [← hLcirc, hLcoord]
    simp [inner_add_left, real_inner_smul_left]

private lemma midpoint_power_eq_iff_endpoint_power_balance
    {s : Sphere P} {A B C : P} (hA : s.power A = 0) :
    s.power (midpoint ℝ A B) = s.power (midpoint ℝ A C) ↔
      2 * (s.power B - s.power C) = dist A B ^ 2 - dist A C ^ 2 := by
  simp only [midpoint, AffineMap.lineMap_apply]
  rw [sphere_power_line_interpolation, sphere_power_line_interpolation, hA]
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

private lemma normalized_affineCombination_fin3_vsub_first {A B C K : P}
    (k : Fin 3 → ℝ) (hksum : ∑ i ∈ Finset.univ, k i = 1)
    (hk : (Finset.affineCombination ℝ Finset.univ ![A, B, C]) k = K) :
    K -ᵥ A = k 1 • (B -ᵥ A) + k 2 • (C -ᵥ A) := by
  rw [← hk]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    Finset.univ k ![A, B, C] (by simpa using hksum) A]
  rw [vadd_vsub]
  simp [Finset.weightedVSubOfPoint, Fin.sum_univ_three]

private lemma first_signed_tangent_relation_cancels_mixed_term
    (x y u v p q r : ℝ)
    (h : y * ((1 - v) * q - u * r) =
      u * ((1 - x) * p - y * r)) :
    y * (1 - v) * q = u * (1 - x) * p := by
  linear_combination h

private lemma parametric_two_coordinate_apollonius_expansion
    (b c : V) (x y u v : ℝ) :
    2 * ((x + y) * ‖u • b + v • c‖ ^ 2 -
      (u + v) * ‖x • b + y • c‖ ^ 2) +
      (x * v - y * u) * (‖b‖ ^ 2 - ‖c‖ ^ 2) =
    2 * ((x + y) *
        (u ^ 2 * ‖b‖ ^ 2 + v ^ 2 * ‖c‖ ^ 2 +
          2 * u * v * inner ℝ b c) -
      (u + v) *
        (x ^ 2 * ‖b‖ ^ 2 + y ^ 2 * ‖c‖ ^ 2 +
          2 * x * y * inner ℝ b c)) +
      (x * v - y * u) * (‖b‖ ^ 2 - ‖c‖ ^ 2) := by
  rw [norm_add_sq_real, norm_add_sq_real]
  simp only [inner_smul_left, inner_smul_right]
  rw [norm_smul, norm_smul, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, starRingEnd_apply, star_trivial]
  simp only [mul_pow, sq_abs]
  ring

private lemma positive_metric_cross_identity_iff_cosine_equality
    (a b c d e f s t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hs : a ^ 2 + b ^ 2 - e ^ 2 = 2 * a * b * s)
    (ht : c ^ 2 + d ^ 2 - f ^ 2 = 2 * c * d * t) :
    (a ^ 2 + b ^ 2 - e ^ 2) * (c * d) =
        (c ^ 2 + d ^ 2 - f ^ 2) * (a * b) ↔ s = t := by
  rw [hs, ht]
  constructor
  · intro h
    have hab : 0 < a * b := mul_pos ha hb
    have hcd : 0 < c * d := mul_pos hc hd
    nlinarith [mul_pos hab hcd]
  · intro h
    rw [h]
    ring

private lemma signed_cross_of_sq_cross_and_same_sign
    (a b c d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hsq : a ^ 2 * d ^ 2 = c ^ 2 * b ^ 2)
    (hsign : 0 ≤ a * c) :
    b * c = d * a := by
  have hfac : (d * a - b * c) * (d * a + b * c) = 0 := by
    calc
      (d * a - b * c) * (d * a + b * c) = a ^ 2 * d ^ 2 - c ^ 2 * b ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq
  rcases mul_eq_zero.mp hfac with hminus | hplus
  · linarith
  · by_cases ha0 : a = 0
    · subst a
      have hc0 : c = 0 := by nlinarith [sq_pos_of_pos hb]
      simp [hc0]
    · rcases lt_or_gt_of_ne ha0 with ha | ha
      · have hsign' : 0 ≤ c * a := by simpa [mul_comm] using hsign
        have hc : c ≤ 0 := nonpos_of_mul_nonneg_left hsign' ha
        have hda : d * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd) (le_of_lt ha)
        have hbc : b * c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hb) hc
        nlinarith
      · have hsign' : 0 ≤ c * a := by simpa [mul_comm] using hsign
        have hc : 0 ≤ c := nonneg_of_mul_nonneg_left hsign' ha
        have hda : 0 ≤ d * a := mul_nonneg (le_of_lt hd) (le_of_lt ha)
        have hbc : 0 ≤ b * c := mul_nonneg (le_of_lt hb) hc
        nlinarith

private lemma circumcenter_equidistant_linear_equation {A K O : P}
    (h : dist O A = dist O K) :
    2 * inner ℝ (K -ᵥ A) (O -ᵥ A) = ‖K -ᵥ A‖ ^ 2 := by
  have hz := inner_antipode_eq_zero_of_equidistant h
  rw [Equiv.pointReflection_apply] at hz
  simp only [vadd_vsub_assoc] at hz
  have hv : O -ᵥ K = (O -ᵥ A) + (A -ᵥ K) := by
    exact (vsub_add_vsub_cancel O A K).symm
  have ha : A -ᵥ K = -(K -ᵥ A) := by
    exact (neg_vsub_eq_vsub_rev K A).symm
  rw [hv, ha, inner_neg_left, inner_add_right, inner_add_right,
    inner_neg_right, real_inner_self_eq_norm_sq] at hz
  linarith

private lemma parametric_nested_angle_wedge_gaps (x y u v : ℝ) :
    ((u - 1) * y - v * (x - 1) = v - y - (x * v - y * u)) ∧
      (u * (y - 1) - (v - 1) * x = x - u - (x * v - y * u)) := by
  constructor <;> ring

private lemma positive_oriented_wedges_of_nested_determinant_gaps
    (x y u v : ℝ)
    (h₂ : 0 < v - y - (x * v - y * u))
    (h₃ : 0 < x - u - (x * v - y * u)) :
    0 < (u - 1) * y - v * (x - 1) ∧
      0 < u * (y - 1) - (v - 1) * x := by
  constructor <;> nlinarith

private lemma angle_eq_normalized_inner {A B C D E F : P}
    (h : ∠ A B C = ∠ D E F) :
    inner ℝ (A -ᵥ B) (C -ᵥ B) / (‖A -ᵥ B‖ * ‖C -ᵥ B‖) =
      inner ℝ (D -ᵥ E) (F -ᵥ E) / (‖D -ᵥ E‖ * ‖F -ᵥ E‖) := by
  apply Real.arccos_injOn
  · exact abs_le.mp
      (abs_real_inner_div_norm_mul_norm_le_one (A -ᵥ B) (C -ᵥ B))
  · exact abs_le.mp
      (abs_real_inner_div_norm_mul_norm_le_one (D -ᵥ E) (F -ᵥ E))
  · exact angle_eq_expands_without_squaring h

private lemma swapped_coordinate_apollonius_factorization
    (b c : V) (x y : ℝ) :
    2 * ((x + y) * ‖y • b + x • c‖ ^ 2 -
      (y + x) * ‖x • b + y • c‖ ^ 2) +
      (x * x - y * y) * (‖b‖ ^ 2 - ‖c‖ ^ 2) =
        (x ^ 2 - y ^ 2) * (1 - 2 * (x + y)) *
          (‖b‖ ^ 2 - ‖c‖ ^ 2) := by
  rw [parametric_two_coordinate_apollonius_expansion]
  ring

private lemma three_linear_metric_relations_force_singular
    (a11 a12 a13 a21 a22 a23 a31 a32 a33 p q r : ℝ)
    (hp : p ≠ 0)
    (h1 : a11 * p + a12 * q + a13 * r = 0)
    (h2 : a21 * p + a22 * q + a23 * r = 0)
    (h3 : a31 * p + a32 * q + a33 * r = 0) :
    a11 * (a22 * a33 - a23 * a32) -
      a12 * (a21 * a33 - a23 * a31) +
      a13 * (a21 * a32 - a22 * a31) = 0 := by
  have hscaled : p * (a11 * (a22 * a33 - a23 * a32) -
      a12 * (a21 * a33 - a23 * a31) +
      a13 * (a21 * a32 - a22 * a31)) = 0 := by
    linear_combination
      (a22 * a33 - a23 * a32) * h1 +
      (a13 * a32 - a12 * a33) * h2 +
      (a12 * a23 - a13 * a22) * h3
  exact (mul_eq_zero.mp hscaled).resolve_left hp

private lemma cross_relation_of_common_angle_data
    (c s d₁ d₂ p q a b : ℝ)
    (hs : s ≠ 0)
    (hc₁ : c * d₁ = p) (hc₂ : c * d₂ = q)
    (hs₁ : s * d₁ = a) (hs₂ : s * d₂ = b) :
    a * q = b * p := by
  apply (mul_left_cancel₀ hs)
  calc
    s * (a * q) = (s * d₁) * (s * d₂) * c := by rw [← hc₂, hs₁]; ring
    _ = s * (b * p) := by rw [← hc₁, hs₂]; ring

private lemma scaled_inner_eq_of_normalized_inner_eq
    (o : Orientation ℝ V (Fin 2)) (a b c d : V) (α β W : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hW : W ≠ 0)
    (hab : o.areaForm a b = α * W)
    (hcd : o.areaForm c d = β * W)
    (hcos :
      inner ℝ a b / (‖a‖ * ‖b‖) =
        inner ℝ c d / (‖c‖ * ‖d‖)) :
    β * inner ℝ a b = α * inner ℝ c d := by
  have hab0 : o.areaForm a b ≠ 0 := by
    rw [hab]
    exact mul_ne_zero (ne_of_gt hα) hW
  have hcd0 : o.areaForm c d ≠ 0 := by
    rw [hcd]
    exact mul_ne_zero (ne_of_gt hβ) hW
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab0
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab0
  have hc0 : c ≠ 0 := by rintro rfl; simp at hcd0
  have hd0 : d ≠ 0 := by rintro rfl; simp at hcd0
  have hn1 : 0 < ‖a‖ * ‖b‖ :=
    mul_pos (norm_pos_iff.mpr ha0) (norm_pos_iff.mpr hb0)
  have hn2 : 0 < ‖c‖ * ‖d‖ :=
    mul_pos (norm_pos_iff.mpr hc0) (norm_pos_iff.mpr hd0)
  have hcross :
      inner ℝ a b * (‖c‖ * ‖d‖) =
        inner ℝ c d * (‖a‖ * ‖b‖) :=
    (div_eq_div_iff (ne_of_gt hn1) (ne_of_gt hn2)).mp hcos
  have hg1 := o.inner_sq_add_areaForm_sq a b
  have hg2 := o.inner_sq_add_areaForm_sq c d
  rw [hab] at hg1
  rw [hcd] at hg2
  have hcrosssq := congrArg (fun z : ℝ => z ^ 2) hcross
  have hsquare :
      (β * inner ℝ a b) ^ 2 = (α * inner ℝ c d) ^ 2 := by
    have hW2 : 0 < W ^ 2 := sq_pos_of_ne_zero hW
    nlinarith
  have hIeq :
      inner ℝ a b =
        inner ℝ c d * (‖a‖ * ‖b‖) / (‖c‖ * ‖d‖) := by
    apply (eq_div_iff (ne_of_gt hn2)).2
    exact hcross
  have hsignI : 0 ≤ inner ℝ a b * inner ℝ c d := by
    calc
      inner ℝ a b * inner ℝ c d =
          (inner ℝ c d ^ 2 * (‖a‖ * ‖b‖)) /
            (‖c‖ * ‖d‖) := by rw [hIeq]; ring
      _ ≥ 0 := div_nonneg
        (mul_nonneg (sq_nonneg _) hn1.le) hn2.le
  have hsign :
      0 ≤ (β * inner ℝ a b) * (α * inner ℝ c d) := by
    calc
      _ = (α * β) * (inner ℝ a b * inner ℝ c d) := by ring
      _ ≥ 0 := mul_nonneg
        (mul_nonneg hα.le hβ.le) hsignI
  have hfac :
      (β * inner ℝ a b - α * inner ℝ c d) *
          (β * inner ℝ a b + α * inner ℝ c d) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · nlinarith

private lemma metric_singular_instantiation_is_polynomial_identity (p q r : ℝ) :
    q * (0 * (-q) - (-p) * r) -
      (-p) * (r * (-q) - (-p) * 0) +
      0 * (r * r - 0 * 0) = 0 := by
  ring

private lemma parametric_circumcircle_metric_wedge_identity
    (c v : ℝ) :
    let x : ℝ := (1 + 3 * c ^ 2) / (1 + c ^ 2)
    let y : ℝ := c * (1 - c ^ 2) / (1 + c ^ 2)
    let u : ℝ := c * (2 * c - v)
    (1 - c ^ 2) *
        ((v + c * u) * (x ^ 2 + y ^ 2) +
          (-y - c * x) * (u ^ 2 + v ^ 2) -
          (1 - c ^ 2) * (x * v - y * u)) +
      2 * c * (1 + c ^ 2) *
        ((((u - 2) * y - v * (x - 2)) * (v - c) -
          u * ((u - 2) * (x - 2) + v * y))) = 0 := by
  dsimp
  have hd : 1 + c ^ 2 ≠ 0 := by nlinarith [sq_nonneg c]
  field_simp [hd]
  ring

private lemma orientation_volumeForm_ne_zero (o : Orientation ℝ V (Fin 2)) :
    o.volumeForm ≠ 0 := by
  let ob := Orientation.finOrthonormalBasis (by omega) (Fact.out : finrank ℝ V = 2) o
  have hob : ob.toBasis.orientation = o := by
    exact Orientation.finOrthonormalBasis_orientation (by omega)
      (Fact.out : finrank ℝ V = 2) o
  have hv : o.volumeForm = ob.toBasis.det := Orientation.volumeForm_robust o ob hob
  intro hzero
  have hd : ob.toBasis.det = 0 := by rw [← hv, hzero]
  have hs := Module.Basis.det_self ob.toBasis
  rw [hd] at hs
  norm_num at hs

private lemma affineIndependent_fin3_vsub_basis
    {A B C : P} (h : AffineIndependent ℝ ![A, B, C]) :
    LinearIndependent ℝ ![B -ᵥ A, C -ᵥ A] := by
  have h0 :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ![A, B, C] (0 : Fin 3)).1 h
  let f : Fin 2 → {j : Fin 3 // j ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.succ_inj.mp
    exact congrArg Subtype.val hij
  have h1 := h0.comp f hf
  have heq : (fun i => ![A, B, C] (↑(f i) : Fin 3) -ᵥ ![A, B, C] 0) =
      ![B -ᵥ A, C -ᵥ A] := by
    funext i
    fin_cases i <;> simp [f]
  rw [← heq]
  exact h1

private lemma three_angle_metric_system_implies_apollonius
    (a b c d p q r : ℝ) (hp : p ≠ 0)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (ha1 : a < 1) (hd1 : d < 1)
    (h1 : c * (1 - a) * p + b * (d - 1) * r = 0)
    (h2 : 2 * c * (a - 1) * (c - 1) * p + 4 * c * d * (a - 1) * q +
      (2 * a * d ^ 2 - a * d + b * c + 2 * b * d - b - 2 * d ^ 2 + d) * r = 0)
    (h3 : (2 * a ^ 2 * d - 2 * a ^ 2 + 2 * a * c - a * d + a + b * c - c) * p +
      4 * a * b * (d - 1) * q + 2 * b * (b - 1) * (d - 1) * r = 0) :
    (-2 * a ^ 2 * c - 2 * a ^ 2 * d + 2 * a * c ^ 2 + a * d + 2 * b * c ^ 2 - b * c) * p +
      (-4 * (a * b * c + a * b * d - a * c * d - b * c * d)) * q +
      (2 * a * d ^ 2 - a * d - 2 * b ^ 2 * c - 2 * b ^ 2 * d + b * c + 2 * b * d ^ 2) * r = 0 := by
  have hdet := three_linear_metric_relations_force_singular
    (c * (1 - a)) 0 (b * (d - 1))
    (2 * c * (a - 1) * (c - 1)) (4 * c * d * (a - 1))
      (2 * a * d ^ 2 - a * d + b * c + 2 * b * d - b - 2 * d ^ 2 + d)
    (2 * a ^ 2 * d - 2 * a ^ 2 + 2 * a * c - a * d + a + b * c - c)
      (4 * a * b * (d - 1)) (2 * b * (b - 1) * (d - 1))
    p q r hp (by simpa using h1) h2 h3
  let H := a ^ 2 * d - a * b * c + a * b - a * d ^ 2 + b * c * d - c * d
  have hfactor : 4 * b * c * (a - 1) * (d - 1) * H = 0 := by
    dsimp [H]
    linear_combination hdet
  have ha0 : a - 1 ≠ 0 := by nlinarith
  have hd0 : d - 1 ≠ 0 := by nlinarith
  have hcoef : 4 * b * c * (a - 1) * (d - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (ne_of_gt hb)) (ne_of_gt hc)) ha0) hd0
  have hH : H = 0 := (mul_eq_zero.mp hfactor).resolve_left hcoef
  let T :=
    (-2 * a ^ 2 * c - 2 * a ^ 2 * d + 2 * a * c ^ 2 + a * d + 2 * b * c ^ 2 - b * c) * p +
      (-4 * (a * b * c + a * b * d - a * c * d - b * c * d)) * q +
      (2 * a * d ^ 2 - a * d - 2 * b ^ 2 * c - 2 * b ^ 2 * d + b * c + 2 * b * d ^ 2) * r
  let n1 := 2 * a ^ 2 * c * d + 2 * a ^ 2 * d ^ 2 - 2 * a * b * c ^ 2 -
    2 * a * b * c * d + 2 * a * b * c + 2 * a * b * d - 2 * a * c * d -
    a * d ^ 2 - b * c * d
  let n2 := -4 * a * b * c - 4 * a * b * d + 4 * a * c * d + 4 * b * c * d
  have hscaled : 4 * (c * d * (a - 1)) * T = 0 := by
    dsimp [T, n1, n2, H] at *
    linear_combination 4 * n1 * h1 + n2 * h2 + 4 * b * (c + d) * r * hH
  have hscale_ne : 4 * (c * d * (a - 1)) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero (ne_of_gt hc) (ne_of_gt hd)) ha0)
  have hT : T = 0 := (mul_eq_zero.mp hscaled).resolve_left hscale_ne
  simpa [T] using hT

/-- The affine-independence hypotheses supply the nondegeneracy witnesses required to construct
the triangles in the statement.  The notation `∠` denotes the undirected Euclidean angle. -/
theorem result {A B C M N K L O : P} (affineIndependent_ABC : AffineIndependent ℝ ![A, B, C])
    (M_eq_midpoint_AB : M = midpoint ℝ A B) (N_eq_midpoint_AC : N = midpoint ℝ A C)
    (affineIndependent_BMC : AffineIndependent ℝ ![B, M, C])
    (affineIndependent_BNC : AffineIndependent ℝ ![B, N, C])
    (affineIndependent_ABL : AffineIndependent ℝ ![A, B, L])
    (affineIndependent_AKC : AffineIndependent ℝ ![A, K, C])
    (K_mem_interior_BMC : K ∈ (⟨_, affineIndependent_BMC⟩ : Triangle ℝ P).interior)
    (L_mem_interior_BNC : L ∈ (⟨_, affineIndependent_BNC⟩ : Triangle ℝ P).interior)
    (K_mem_interior_ABL : K ∈ (⟨_, affineIndependent_ABL⟩ : Triangle ℝ P).interior)
    (L_mem_interior_AKC : L ∈ (⟨_, affineIndependent_AKC⟩ : Triangle ℝ P).interior)
    (angle_KBA_eq_angle_ACL : ∠ K B A = ∠ A C L)
    (angle_LBK_eq_angle_LNC : ∠ L B K = ∠ L N C)
    (angle_LCK_eq_angle_BMK : ∠ L C K = ∠ B M K)
    (affineIndependent_AKL : AffineIndependent ℝ ![A, K, L])
    (O_eq_circumcenter : O = (⟨_, affineIndependent_AKL⟩ : Triangle ℝ P).circumcenter) :
    dist O M = dist O N := by
  apply (result_reduce_midpoints M_eq_midpoint_AB N_eq_midpoint_AC).2
  apply dist_midpoints_of_antipode_dist_eq
  subst M
  subst N
  rcases exists_positive_ABC_coordinates_of_mem_interior_BmidpointC
      affineIndependent_BMC K_mem_interior_BMC with
    ⟨k, hksum, hkpos, hKcoord⟩
  rcases exists_positive_ABC_coordinates_of_mem_interior_BmidpointAC_C
      affineIndependent_BNC L_mem_interior_BNC with
    ⟨l, hlsum, hlpos, hLcoord⟩
  have hKv : K -ᵥ A = k 1 • (B -ᵥ A) + k 2 • (C -ᵥ A) :=
    normalized_affineCombination_fin3_vsub_first k hksum hKcoord.symm
  have hLv : L -ᵥ A = l 1 • (B -ᵥ A) + l 2 • (C -ᵥ A) :=
    normalized_affineCombination_fin3_vsub_first l hlsum hLcoord.symm
  rcases K_mem_interior_ABL with ⟨w, hwsum, hwi, hwK⟩
  have hwpos : ∀ i, 0 < w i :=
    normalized_coordinates_positive_of_mem_interior affineIndependent_ABL
      ⟨w, hwsum, hwi, hwK⟩ hwsum hwK.symm
  have hkwSum : ∑ i ∈ Finset.univ,
      (![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hlsum hwsum
    linear_combination w 2 * hlsum + hwsum
  have hkw :
      k = ![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2] := by
    apply barycentric_coordinates_unique affineIndependent_ABC hksum hkwSum
    calc
      (Finset.affineCombination ℝ Finset.univ ![A, B, C]) k = K := hKcoord.symm
      _ = (Finset.affineCombination ℝ Finset.univ ![A, B, L]) w := hwK.symm
      _ = (Finset.affineCombination ℝ Finset.univ ![A, B, C])
          ![w 0 + w 2 * l 0, w 1 + w 2 * l 1, w 2 * l 2] :=
        affineCombination_ABL_to_ABC l w hlsum hwsum hLcoord
  rcases L_mem_interior_AKC with ⟨z, hzsum, hzi, hzL⟩
  have hzpos : ∀ i, 0 < z i :=
    normalized_coordinates_positive_of_mem_interior affineIndependent_AKC
      ⟨z, hzsum, hzi, hzL⟩ hzsum hzL.symm
  have hlzSum : ∑ i ∈ Finset.univ,
      (![z 0 + z 1 * k 0, z 1 * k 1, z 2 + z 1 * k 2] : Fin 3 → ℝ) i = 1 := by
    rw [Fin.sum_univ_three]
    simp
    rw [Fin.sum_univ_three] at hksum hzsum
    linear_combination z 1 * hksum + hzsum
  have hlz :
      l = ![z 0 + z 1 * k 0, z 1 * k 1, z 2 + z 1 * k 2] := by
    apply barycentric_coordinates_unique affineIndependent_ABC hlsum hlzSum
    calc
      (Finset.affineCombination ℝ Finset.univ ![A, B, C]) l = L := hLcoord.symm
      _ = (Finset.affineCombination ℝ Finset.univ ![A, K, C]) z := hzL.symm
      _ = (Finset.affineCombination ℝ Finset.univ ![A, B, C])
          ![z 0 + z 1 * k 0, z 1 * k 1, z 2 + z 1 * k 2] :=
        affineCombination_AKC_to_ABC k z hksum hzsum hKcoord
  have hsigns := strict_determinant_signs_of_nested_coordinate_identities
    k l w z hkpos hlpos hwsum hwpos hzsum hzpos hkw hlz
  have hord := strict_ratio_order_of_nested_coordinates
    (hkpos 1) (hkpos 2) (hlpos 1) (hlpos 2)
    hsigns.1 hsigns.2.1 hsigns.2.2
  have hangle1 := angle_eq_metric_cross_identity angle_KBA_eq_angle_ACL
  have hangle2 := angle_eq_metric_cross_identity angle_LBK_eq_angle_LNC
  have hangle3 := angle_eq_metric_cross_identity angle_LCK_eq_angle_BMK
  let e₁ : ℝ :=
    (dist K B ^ 2 + dist A B ^ 2 - dist K A ^ 2) * (dist A C * dist L C) -
      (dist A C ^ 2 + dist L C ^ 2 - dist A L ^ 2) * (dist K B * dist A B)
  let e₂ : ℝ :=
    (dist L B ^ 2 + dist K B ^ 2 - dist L K ^ 2) *
        (dist L (midpoint ℝ A C) * dist C (midpoint ℝ A C)) -
      (dist L (midpoint ℝ A C) ^ 2 + dist C (midpoint ℝ A C) ^ 2 - dist L C ^ 2) *
        (dist L B * dist K B)
  let e₃ : ℝ :=
    (dist L C ^ 2 + dist K C ^ 2 - dist L K ^ 2) * (dist B (midpoint ℝ A B) *
      dist K (midpoint ℝ A B)) -
      (dist B (midpoint ℝ A B) ^ 2 + dist K (midpoint ℝ A B) ^ 2 - dist B K ^ 2) *
        (dist L C * dist K C)
  have he₁ : e₁ = 0 := by
    exact sub_eq_zero.mpr hangle1
  have he₂ : e₂ = 0 := by
    exact sub_eq_zero.mpr hangle2
  have he₃ : e₃ = 0 := by
    exact sub_eq_zero.mpr hangle3
  have hwedges :
      0 < (l 1 - 1) * k 2 - l 2 * (k 1 - 1) ∧
        0 < l 1 * (k 2 - 1) - (l 2 - 1) * k 1 :=
    positive_oriented_wedges_of_nested_determinant_gaps
      (k 1) (k 2) (l 1) (l 2) hsigns.2.1 hsigns.2.2
  have hcos₁ := angle_eq_normalized_inner angle_KBA_eq_angle_ACL
  have hcos₂ := angle_eq_normalized_inner angle_LBK_eq_angle_LNC
  have hcos₃ := angle_eq_normalized_inner angle_LCK_eq_angle_BMK
  subst O
  apply antipode_equidistant_of_apollonius_residual
  let t : Triangle ℝ P := ⟨![A, K, L], affineIndependent_AKL⟩
  have hA : dist t.circumcenter A = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 0
  have hK : dist t.circumcenter K = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 1
  have hL : dist t.circumcenter L = t.circumradius := by
    simpa [t] using t.dist_circumcenter_eq_circumradius' 2
  have hKcirc :
      2 * inner ℝ (K -ᵥ A) (t.circumcenter -ᵥ A) = ‖K -ᵥ A‖ ^ 2 :=
    circumcenter_equidistant_linear_equation (hA.trans hK.symm)
  have hLcirc :
      2 * inner ℝ (L -ᵥ A) (t.circumcenter -ᵥ A) = ‖L -ᵥ A‖ ^ 2 :=
    circumcenter_equidistant_linear_equation (hA.trans hL.symm)
  have hcircumcenterSystem := audit_coordinate_linearizes_circumcenter_equations
    (k 1) (k 2) (l 1) (l 2) hKv hLv hKcirc hLcirc
  have hresidualReduction := positive_determinant_residual_reduction
    (k 1) (k 2) (l 1) (l 2)
    (inner ℝ (B -ᵥ A) (t.circumcenter -ᵥ A))
    (inner ℝ (C -ᵥ A) (t.circumcenter -ᵥ A))
    (‖K -ᵥ A‖ ^ 2) (‖L -ᵥ A‖ ^ 2)
    (‖B -ᵥ A‖ ^ 2) (‖C -ᵥ A‖ ^ 2)
    hsigns.1 hcircumcenterSystem.1 hcircumcenterSystem.2
  have hpower :
      2 * (dist t.circumcenter B ^ 2 - dist t.circumcenter C ^ 2) -
          (dist A B ^ 2 - dist A C ^ 2) =
        4 * (inner ℝ (C -ᵥ A) (t.circumcenter -ᵥ A) -
          inner ℝ (B -ᵥ A) (t.circumcenter -ᵥ A)) +
          (‖B -ᵥ A‖ ^ 2 - ‖C -ᵥ A‖ ^ 2) := by
    simp only [dist_eq_norm_vsub]
    rw [show t.circumcenter -ᵥ B =
          (t.circumcenter -ᵥ A) + (A -ᵥ B) by
        exact (vsub_add_vsub_cancel t.circumcenter A B).symm,
      show t.circumcenter -ᵥ C =
          (t.circumcenter -ᵥ A) + (A -ᵥ C) by
        exact (vsub_add_vsub_cancel t.circumcenter A C).symm]
    rw [norm_add_sq_real, norm_add_sq_real]
    have hAB : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
    have hAC : A -ᵥ C = -(C -ᵥ A) := (neg_vsub_eq_vsub_rev C A).symm
    rw [hAB, hAC]
    simp only [norm_neg, inner_neg_right]
    rw [real_inner_comm (t.circumcenter -ᵥ A) (B -ᵥ A),
      real_inner_comm (t.circumcenter -ᵥ A) (C -ᵥ A)]
    ring
  rw [hpower]
  apply hresidualReduction.mpr
  have hAB : A ≠ B := by
    have h := Function.Injective.ne affineIndependent_ABC.injective
      (show (0 : Fin 3) ≠ 1 by decide)
    simpa using h
  have hBA : B -ᵥ A ≠ 0 := vsub_ne_zero.mpr hAB.symm
  have hp : ‖B -ᵥ A‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hBA)
  have hli := affineIndependent_fin3_vsub_basis affineIndependent_ABC
  have hspan : Submodule.span ℝ (Set.range ![B -ᵥ A, C -ᵥ A]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simpa using (Fact.out : finrank ℝ V = 2).symm)
  let bcBasis : Module.Basis (Fin 2) ℝ V := Module.Basis.mk hli hspan.ge
  let o : Orientation ℝ V (Fin 2) := bcBasis.orientation
  have hvol : o.volumeForm ≠ 0 := orientation_volumeForm_ne_zero o
  have hW : o.areaForm (B -ᵥ A) (C -ᵥ A) ≠ 0 := by
    intro hz
    have heval : o.volumeForm bcBasis = 0 := by
      rw [show bcBasis = ![B -ᵥ A, C -ᵥ A] by
        funext i; fin_cases i <;> simp [bcBasis]]
      rw [← o.areaForm_to_volumeForm]
      exact hz
    have hrep := AlternatingMap.eq_smul_basis_det bcBasis o.volumeForm
    apply hvol
    rw [hrep, heval, zero_smul]
  have hbb : o.areaForm (B -ᵥ A) (B -ᵥ A) = 0 := by
    have h := o.areaForm_swap (B -ᵥ A) (B -ᵥ A)
    linarith
  have hcc : o.areaForm (C -ᵥ A) (C -ᵥ A) = 0 := by
    have h := o.areaForm_swap (C -ᵥ A) (C -ᵥ A)
    linarith
  have hcb : o.areaForm (C -ᵥ A) (B -ᵥ A) =
      -o.areaForm (B -ᵥ A) (C -ᵥ A) := o.areaForm_swap _ _
  have harea₁ : o.areaForm (K -ᵥ B) (A -ᵥ B) =
      k 2 * o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [show K -ᵥ B = (K -ᵥ A) + (A -ᵥ B) by
      exact (vsub_add_vsub_cancel K A B).symm,
      show A -ᵥ B = -(B -ᵥ A) by exact (neg_vsub_eq_vsub_rev B A).symm,
      hKv]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, map_neg, LinearMap.neg_apply]
    rw [hbb, hcb]
    ring
  have harea₁' : o.areaForm (A -ᵥ C) (L -ᵥ C) =
      l 1 * o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [show L -ᵥ C = (L -ᵥ A) + (A -ᵥ C) by
      exact (vsub_add_vsub_cancel L A C).symm,
      show A -ᵥ C = -(C -ᵥ A) by exact (neg_vsub_eq_vsub_rev C A).symm,
      hLv]
    simp only [map_neg, map_add, map_smul, smul_eq_mul, LinearMap.neg_apply]
    rw [hcb, hcc]
    ring
  have hinner₁ :
      l 1 * inner ℝ (K -ᵥ B) (A -ᵥ B) =
        k 2 * inner ℝ (A -ᵥ C) (L -ᵥ C) :=
    scaled_inner_eq_of_normalized_inner_eq o _ _ _ _ _ _ _
      (hkpos 2) (hlpos 1) hW harea₁ harea₁' hcos₁
  have hparametric := parametric_circumcircle_metric_wedge_identity
    (l 2 / l 1) (k 2 / k 1)
  have harea₂ : o.areaForm (L -ᵥ B) (K -ᵥ B) =
      ((l 1 - 1) * k 2 - l 2 * (k 1 - 1)) *
        o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [show L -ᵥ B = (L -ᵥ A) + (A -ᵥ B) by
      exact (vsub_add_vsub_cancel L A B).symm,
      show K -ᵥ B = (K -ᵥ A) + (A -ᵥ B) by
        exact (vsub_add_vsub_cancel K A B).symm,
      show A -ᵥ B = -(B -ᵥ A) by exact (neg_vsub_eq_vsub_rev B A).symm,
      hLv, hKv]
    simp only [map_add, map_smul, map_neg, smul_eq_mul,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply]
    rw [hbb, hcb, hcc]
    ring
  have hLN : L -ᵥ midpoint ℝ A C =
      l 1 • (B -ᵥ A) + (l 2 - 1 / 2 : ℝ) • (C -ᵥ A) := by
    rw [show L -ᵥ midpoint ℝ A C =
          (L -ᵥ A) + (A -ᵥ midpoint ℝ A C) by
        exact (vsub_add_vsub_cancel L A (midpoint ℝ A C)).symm,
      left_vsub_midpoint, hLv,
      show A -ᵥ C = -(C -ᵥ A) by
        exact (neg_vsub_eq_vsub_rev C A).symm]
    rw [smul_neg, ← neg_smul, invOf_eq_inv]
    norm_num
    module
  have hCN : C -ᵥ midpoint ℝ A C = (1 / 2 : ℝ) • (C -ᵥ A) := by
    rw [vsub_midpoint]
    simp
  have harea₂' :
      o.areaForm (L -ᵥ midpoint ℝ A C) (C -ᵥ midpoint ℝ A C) =
        (l 1 / 2) * o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [hLN, hCN]
    simp only [map_add, map_smul, smul_eq_mul,
      LinearMap.add_apply, LinearMap.smul_apply]
    rw [hcc]
    ring
  have hinner₂ :
      (l 1 / 2) * inner ℝ (L -ᵥ B) (K -ᵥ B) =
        ((l 1 - 1) * k 2 - l 2 * (k 1 - 1)) *
          inner ℝ (L -ᵥ midpoint ℝ A C) (C -ᵥ midpoint ℝ A C) :=
    scaled_inner_eq_of_normalized_inner_eq o _ _ _ _ _ _ _
      hwedges.1 (div_pos (hlpos 1) (by norm_num)) hW harea₂ harea₂' hcos₂
  have harea₃ : o.areaForm (L -ᵥ C) (K -ᵥ C) =
      (l 1 * (k 2 - 1) - (l 2 - 1) * k 1) *
        o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [show L -ᵥ C = (L -ᵥ A) + (A -ᵥ C) by
      exact (vsub_add_vsub_cancel L A C).symm,
      show K -ᵥ C = (K -ᵥ A) + (A -ᵥ C) by
        exact (vsub_add_vsub_cancel K A C).symm,
      show A -ᵥ C = -(C -ᵥ A) by exact (neg_vsub_eq_vsub_rev C A).symm,
      hLv, hKv]
    simp only [map_add, map_smul, map_neg, smul_eq_mul,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply]
    rw [hbb, hcb, hcc]
    ring
  have hBM : B -ᵥ midpoint ℝ A B = (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [vsub_midpoint]
    simp
  have hKM : K -ᵥ midpoint ℝ A B =
      (k 1 - 1 / 2 : ℝ) • (B -ᵥ A) + k 2 • (C -ᵥ A) := by
    rw [show K -ᵥ midpoint ℝ A B =
          (K -ᵥ A) + (A -ᵥ midpoint ℝ A B) by
        exact (vsub_add_vsub_cancel K A (midpoint ℝ A B)).symm,
      left_vsub_midpoint, hKv,
      show A -ᵥ B = -(B -ᵥ A) by
        exact (neg_vsub_eq_vsub_rev B A).symm]
    rw [smul_neg, ← neg_smul, invOf_eq_inv]
    norm_num
    module
  have harea₃' :
      o.areaForm (B -ᵥ midpoint ℝ A B) (K -ᵥ midpoint ℝ A B) =
        (k 2 / 2) * o.areaForm (B -ᵥ A) (C -ᵥ A) := by
    rw [hBM, hKM]
    simp only [map_add, map_smul, smul_eq_mul, LinearMap.smul_apply]
    rw [hbb]
    ring
  have hinner₃ :
      (k 2 / 2) * inner ℝ (L -ᵥ C) (K -ᵥ C) =
        (l 1 * (k 2 - 1) - (l 2 - 1) * k 1) *
          inner ℝ (B -ᵥ midpoint ℝ A B) (K -ᵥ midpoint ℝ A B) :=
    scaled_inner_eq_of_normalized_inner_eq o _ _ _ _ _ _ _
      hwedges.2 (div_pos (hkpos 2) (by norm_num)) hW harea₃ harea₃' hcos₃
  have hKB : K -ᵥ B =
      (k 1 - 1) • (B -ᵥ A) + k 2 • (C -ᵥ A) := by
    rw [show K -ᵥ B = (K -ᵥ A) + (A -ᵥ B) by
      exact (vsub_add_vsub_cancel K A B).symm, hKv,
      show A -ᵥ B = -(B -ᵥ A) by exact (neg_vsub_eq_vsub_rev B A).symm]
    module
  have hLB : L -ᵥ B =
      (l 1 - 1) • (B -ᵥ A) + l 2 • (C -ᵥ A) := by
    rw [show L -ᵥ B = (L -ᵥ A) + (A -ᵥ B) by
      exact (vsub_add_vsub_cancel L A B).symm, hLv,
      show A -ᵥ B = -(B -ᵥ A) by exact (neg_vsub_eq_vsub_rev B A).symm]
    module
  have hLC : L -ᵥ C =
      l 1 • (B -ᵥ A) + (l 2 - 1) • (C -ᵥ A) := by
    rw [show L -ᵥ C = (L -ᵥ A) + (A -ᵥ C) by
      exact (vsub_add_vsub_cancel L A C).symm, hLv,
      show A -ᵥ C = -(C -ᵥ A) by exact (neg_vsub_eq_vsub_rev C A).symm]
    module
  have hKC : K -ᵥ C =
      k 1 • (B -ᵥ A) + (k 2 - 1) • (C -ᵥ A) := by
    rw [show K -ᵥ C = (K -ᵥ A) + (A -ᵥ C) by
      exact (vsub_add_vsub_cancel K A C).symm, hKv,
      show A -ᵥ C = -(C -ᵥ A) by exact (neg_vsub_eq_vsub_rev C A).symm]
    module
  have hABv : A -ᵥ B = -(B -ᵥ A) := (neg_vsub_eq_vsub_rev B A).symm
  have hACv : A -ᵥ C = -(C -ᵥ A) := (neg_vsub_eq_vsub_rev C A).symm
  rw [hKB, hABv, hACv, hLC] at hinner₁
  rw [hLB, hKB, hLN, hCN] at hinner₂
  rw [hLC, hKC, hBM, hKM] at hinner₃
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_neg_left, inner_neg_right, real_inner_self_eq_norm_sq,
    starRingEnd_apply, star_trivial] at hinner₁ hinner₂ hinner₃
  rw [← real_inner_comm (C -ᵥ A) (B -ᵥ A)] at hinner₁ hinner₂ hinner₃
  have he1 : l 1 * (1 - k 1) * ‖B -ᵥ A‖ ^ 2 +
      k 2 * (l 2 - 1) * ‖C -ᵥ A‖ ^ 2 = 0 := by
    linear_combination hinner₁
  have he2 : 2 * l 1 * (k 1 - 1) * (l 1 - 1) * ‖B -ᵥ A‖ ^ 2 +
      4 * l 1 * l 2 * (k 1 - 1) * inner ℝ (B -ᵥ A) (C -ᵥ A) +
      (2 * k 1 * l 2 ^ 2 - k 1 * l 2 + k 2 * l 1 + 2 * k 2 * l 2 -
        k 2 - 2 * l 2 ^ 2 + l 2) * ‖C -ᵥ A‖ ^ 2 = 0 := by
    linear_combination 4 * hinner₂
  have he3 :
      (2 * k 1 ^ 2 * l 2 - 2 * k 1 ^ 2 + 2 * k 1 * l 1 - k 1 * l 2 +
        k 1 + k 2 * l 1 - l 1) * ‖B -ᵥ A‖ ^ 2 +
      4 * k 1 * k 2 * (l 2 - 1) * inner ℝ (B -ᵥ A) (C -ᵥ A) +
      2 * k 2 * (k 2 - 1) * (l 2 - 1) * ‖C -ᵥ A‖ ^ 2 = 0 := by
    linear_combination 4 * hinner₃
  have hk1lt : k 1 < 1 := by
    rw [Fin.sum_univ_three] at hksum
    have hk0 := hkpos 0
    have hk2 := hkpos 2
    linarith
  have hl2lt : l 2 < 1 := by
    rw [Fin.sum_univ_three] at hlsum
    have hl0 := hlpos 0
    have hl1 := hlpos 1
    linarith
  rw [hKv, hLv, parametric_two_coordinate_apollonius_expansion]
  convert three_angle_metric_system_implies_apollonius
    (k 1) (k 2) (l 1) (l 2)
    (‖B -ᵥ A‖ ^ 2) (inner ℝ (B -ᵥ A) (C -ᵥ A)) (‖C -ᵥ A‖ ^ 2)
    hp (hkpos 2) (hlpos 1) (hlpos 2) hk1lt hl2lt he1 he2 he3 using 1 <;> ring

end IMO2026P2
