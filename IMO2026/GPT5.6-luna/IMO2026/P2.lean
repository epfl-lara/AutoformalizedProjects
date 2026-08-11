import Mathlib
import IMO2026.P2Helpers

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

open Affine EuclideanGeometry Module

namespace IMO2026P2

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

theorem circumcenter_eq_dist_AK {A K L O : P} (h : AffineIndependent ℝ ![A, K, L])
    (hO : O = (⟨_, h⟩ : Triangle ℝ P).circumcenter) : dist O A = dist O K := by
  subst O
  have hA := (⟨_, h⟩ : Triangle ℝ P).dist_circumcenter_eq_circumradius (0 : Fin 3)
  have hK := (⟨_, h⟩ : Triangle ℝ P).dist_circumcenter_eq_circumradius (1 : Fin 3)
  simpa [dist_comm] using hA.trans hK.symm

private lemma midpoint_vsub_left_half {X Y Z : P} (hZ : Z = midpoint ℝ X Y) :
    Z -ᵥ X = (1 / 2 : ℝ) • (Y -ᵥ X) := by
  subst Z
  rw [midpoint_vsub_left]
  norm_num

private lemma circumcenter_eq_dist_AL {A K L O : P} (h : AffineIndependent ℝ ![A, K, L])
    (hO : O = (⟨_, h⟩ : Triangle ℝ P).circumcenter) : dist O A = dist O L := by
  subst O
  have hA := (⟨_, h⟩ : Triangle ℝ P).dist_circumcenter_eq_circumradius (0 : Fin 3)
  have hL := (⟨_, h⟩ : Triangle ℝ P).dist_circumcenter_eq_circumradius (2 : Fin 3)
  simpa [dist_comm] using hA.trans hL.symm

private lemma triangle_interior_positive_barycentric {X Y Z Q : P}
    (hXYZ : AffineIndependent ℝ ![X, Y, Z])
    (hQ : Q ∈ (⟨![X, Y, Z], hXYZ⟩ : Triangle ℝ P).interior) :
    ∃ w : Fin 3 → ℝ,
      (∀ i, 0 < w i) ∧
      (∑ i, w i = 1) ∧
      Finset.univ.affineCombination ℝ (![X, Y, Z]) w = Q := by
  rcases hQ with ⟨w, hw, hwI, hw_eq⟩
  refine ⟨w, ?_, hw, hw_eq⟩
  intro i
  exact (hwI i).1

private lemma eq_dist_to_sq_inner {A K O : P}
    (hOA : dist O A = dist O K) :
    2 * @inner ℝ V _ (O -ᵥ A) (K -ᵥ A) = ‖K -ᵥ A‖ ^ 2 := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V] at hOA
  have hsq := congrArg (fun x : ℝ => x ^ 2) hOA
  rw [← vsub_sub_vsub_cancel_right O K A, norm_sub_sq_real] at hsq
  nlinarith [hsq]

private lemma midpoint_distance_eq_of_inner_difference {A B C M N O : P}
    (hM : M = midpoint ℝ A B) (hN : N = midpoint ℝ A C)
    (hinner : @inner ℝ V _ (O -ᵥ A) ((C -ᵥ A) - (B -ᵥ A)) =
      (‖C -ᵥ A‖ ^ 2 - ‖B -ᵥ A‖ ^ 2) / 4) :
    dist O M = dist O N := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V,
    ← vsub_sub_vsub_cancel_right O M A, ← vsub_sub_vsub_cancel_right O N A,
    midpoint_vsub_left_half hM, midpoint_vsub_left_half hN]
  have hsq :
      ‖(O -ᵥ A) - (1 / 2 : ℝ) • (B -ᵥ A)‖ ^ 2 =
        ‖(O -ᵥ A) - (1 / 2 : ℝ) • (C -ᵥ A)‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
      real_inner_smul_right, real_inner_smul_right]
    rw [inner_sub_right] at hinner
    norm_num at *
    nlinarith [hinner]
  nlinarith [hsq, norm_nonneg ((O -ᵥ A) - (1 / 2 : ℝ) • (B -ᵥ A)),
    norm_nonneg ((O -ᵥ A) - (1 / 2 : ℝ) • (C -ᵥ A))]

private lemma all_interior_weights {A B C M N K L : P}
    (affineIndependent_BMC : AffineIndependent ℝ ![B, M, C])
    (affineIndependent_BNC : AffineIndependent ℝ ![B, N, C])
    (affineIndependent_ABL : AffineIndependent ℝ ![A, B, L])
    (affineIndependent_AKC : AffineIndependent ℝ ![A, K, C])
    (K_mem_interior_BMC : K ∈ (⟨![B, M, C], affineIndependent_BMC⟩ : Triangle ℝ P).interior)
    (L_mem_interior_BNC : L ∈ (⟨![B, N, C], affineIndependent_BNC⟩ : Triangle ℝ P).interior)
    (K_mem_interior_ABL : K ∈ (⟨![A, B, L], affineIndependent_ABL⟩ : Triangle ℝ P).interior)
    (L_mem_interior_AKC : L ∈ (⟨![A, K, C], affineIndependent_AKC⟩ : Triangle ℝ P).interior) :
    (∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      Finset.univ.affineCombination ℝ (![B, M, C]) w = K) ∧
    (∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      Finset.univ.affineCombination ℝ (![B, N, C]) w = L) ∧
    (∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      Finset.univ.affineCombination ℝ (![A, B, L]) w = K) ∧
    (∃ w : Fin 3 → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i = 1) ∧
      Finset.univ.affineCombination ℝ (![A, K, C]) w = L) := by
  refine ⟨triangle_interior_positive_barycentric affineIndependent_BMC K_mem_interior_BMC, ?_⟩
  refine ⟨triangle_interior_positive_barycentric affineIndependent_BNC L_mem_interior_BNC, ?_⟩
  refine ⟨triangle_interior_positive_barycentric affineIndependent_ABL K_mem_interior_ABL, ?_⟩
  exact triangle_interior_positive_barycentric affineIndependent_AKC L_mem_interior_AKC

private lemma algebraic_target {x y s t B C D qb qc : ℝ}
    (hdet : x * t - y * s ≠ 0) (hx : x ≠ 1) (ht : t ≠ 1)
    (e1 : y * (1 - t) * C - s * (1 - x) * B = 0)
    (e2 : (t * (1 - x) - y * (1 - s)) * (s * D + (t - 1 / 2) * C) - s * ((s - 1) * (x - 1) * B + ((s - 1) * y + t * (x - 1)) * D + t * y * C) = 0)
    (e3 : (x * (1 - t) - s * (1 - y)) * ((x - 1 / 2) * B + y * D) - y * (s * x * B + (s * (y - 1) + (t - 1) * x) * D + (t - 1) * (y - 1) * C) = 0)
    (hk : 2 * (x * qb + y * qc) = x ^ 2 * B + 2 * x * y * D + y ^ 2 * C)
    (hl : 2 * (s * qb + t * qc) = s ^ 2 * B + 2 * s * t * D + t ^ 2 * C) :
    2 * (qc - qb) = (C - B) / 2 := by
  have hpoly :
      2 * (x * t - y * s) * (t - 1) * (x - 1) * (2 * (qc - qb) - (C - B) / 2) =
        (2 * s * x + s * y - s + 3 * t * x + 2 * t * y - t - x - y) * (y * (1 - t) * C - s * (1 - x) * B) +
          (-2 * (x + y) * (t - 1)) * ((t * (1 - x) - y * (1 - s)) * (s * D + (t - 1 / 2) * C) - s * ((s - 1) * (x - 1) * B + ((s - 1) * y + t * (x - 1)) * D + t * y * C)) +
          (2 * (s + t) * (x - 1)) * ((x * (1 - t) - s * (1 - y)) * ((x - 1 / 2) * B + y * D) - y * (s * x * B + (s * (y - 1) + (t - 1) * x) * D + (t - 1) * (y - 1) * C)) +
          (-2 * s * t * x + 2 * s * t + 2 * s * x - 2 * s - 2 * t ^ 2 * x + 2 * t ^ 2 + 2 * t * x - 2 * t) * (2 * (x * qb + y * qc) - (x ^ 2 * B + 2 * x * y * D + y ^ 2 * C)) +
          (2 * t * x ^ 2 + 2 * t * x * y - 2 * t * x - 2 * t * y - 2 * x ^ 2 - 2 * x * y + 2 * x + 2 * y) * (2 * (s * qb + t * qc) - (s ^ 2 * B + 2 * s * t * D + t ^ 2 * C)) := by
    ring_nf
  rw [e1, e2, e3, hk, hl] at hpoly
  have hzero :
      2 * (x * t - y * s) * (t - 1) * (x - 1) * (2 * (qc - qb) - (C - B) / 2) = 0 := by
    simpa using hpoly
  have hfac : 2 * (x * t - y * s) * (t - 1) * (x - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hdet) (sub_ne_zero.mpr ht)) (sub_ne_zero.mpr hx)
  rcases mul_eq_zero.mp hzero with hbad | hgoal
  · exact False.elim (hfac hbad)
  · linarith

set_option maxHeartbeats 1000000

private lemma determinant_positive_of_two_coordinate_cycles
    {x y s t a b : ℝ}
    (hx : 0 < x) (ht : 0 < t)
    (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hb1 : b < 1)
    (hy : y = a * t) (hs : s = b * x) :
    0 < x * t - y * s := by
  have hab_lt : a * b < 1 := by
    have h₁ : a * b < 1 * b := mul_lt_mul_of_pos_right ha1 hb
    have h₂ : 1 * b < 1 := by simpa using hb1
    exact lt_trans h₁ h₂
  rw [hy, hs]
  calc
    0 < (x * t) * (1 - a * b) :=
      mul_pos (mul_pos hx ht) (sub_pos.mpr hab_lt)
    _ = x * t - (a * t) * (b * x) := by ring

private lemma inner_difference_from_quadratic_identity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v z : V} {B C qb qc : ℝ}
    (hB : B = inner ℝ u u) (hC : C = inner ℝ v v)
    (hqb : qb = inner ℝ z u) (hqc : qc = inner ℝ z v)
    (h : 2 * (qc - qb) = (C - B) / 2) :
    inner ℝ z (v - u) = (inner ℝ v v - inner ℝ u u) / 4 := by
  rw [inner_sub_right, ← hqc, ← hqb, ← hC, ← hB]
  linarith

private lemma sq_inner_cross_multiplication
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v p q : V}
    (h : inner ℝ u v * (‖p‖ * ‖q‖) =
      (‖u‖ * ‖v‖) * inner ℝ p q) :
    inner ℝ u v ^ 2 * ‖p‖ ^ 2 * ‖q‖ ^ 2 =
      ‖u‖ ^ 2 * ‖v‖ ^ 2 * inner ℝ p q ^ 2 := by
  have hs := congrArg (fun z : ℝ => z ^ 2) h
  calc
    inner ℝ u v ^ 2 * ‖p‖ ^ 2 * ‖q‖ ^ 2 =
        (inner ℝ u v * (‖p‖ * ‖q‖)) ^ 2 := by ring
    _ = ((‖u‖ * ‖v‖) * inner ℝ p q) ^ 2 := by rw [h]
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 * inner ℝ p q ^ 2 := by ring

private lemma affine_interpolation_distance_eq_of_inner_difference
    {A B C X Y O : P} {r : ℝ}
    (hX : X -ᵥ A = r • (B -ᵥ A))
    (hY : Y -ᵥ A = r • (C -ᵥ A))
    (hinner :
      2 * inner ℝ (O -ᵥ A) ((C -ᵥ A) - (B -ᵥ A)) =
        r * (‖C -ᵥ A‖ ^ 2 - ‖B -ᵥ A‖ ^ 2)) :
    dist O X = dist O Y := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V,
    ← vsub_sub_vsub_cancel_right O X A,
    ← vsub_sub_vsub_cancel_right O Y A, hX, hY]
  have hsq :
      ‖(O -ᵥ A) - r • (B -ᵥ A)‖ ^ 2 =
        ‖(O -ᵥ A) - r • (C -ᵥ A)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [inner_sub_right] at hinner
    rw [← real_inner_self_eq_norm_sq (C -ᵥ A),
      ← real_inner_self_eq_norm_sq (B -ᵥ A)] at hinner
    have hOC : inner ℝ (O -ᵥ A) (C -ᵥ A) =
        inner ℝ (C -ᵥ A) (O -ᵥ A) := real_inner_comm _ _
    have hOB : inner ℝ (O -ᵥ A) (B -ᵥ A) =
        inner ℝ (B -ᵥ A) (O -ᵥ A) := real_inner_comm _ _
    rw [hOC, hOB] at hinner
    rw [hOB, hOC]
    have hinner_r := congrArg (fun q : ℝ => r * q) hinner
    nlinarith [hinner_r]
  nlinarith [hsq, norm_nonneg ((O -ᵥ A) - r • (B -ᵥ A)),
    norm_nonneg ((O -ᵥ A) - r • (C -ᵥ A))]

private lemma finish_midpoint_distance_from_inner
    {A B C O : P}
    (hinner :
      inner ℝ (O -ᵥ A) ((C -ᵥ A) - (B -ᵥ A)) =
        (inner ℝ (C -ᵥ A) (C -ᵥ A) - inner ℝ (B -ᵥ A) (B -ᵥ A)) / 4) :
    dist O (midpoint ℝ A B) = dist O (midpoint ℝ A C) := by
  have hinner' :
      2 * inner ℝ (O -ᵥ A) ((C -ᵥ A) - (B -ᵥ A)) =
        (1 / 2 : ℝ) * (‖C -ᵥ A‖ ^ 2 - ‖B -ᵥ A‖ ^ 2) := by
    rw [← real_inner_self_eq_norm_sq (C -ᵥ A),
      ← real_inner_self_eq_norm_sq (B -ᵥ A)]
    nlinarith [hinner]
  exact affine_interpolation_distance_eq_of_inner_difference
    (hX := midpoint_vsub_left_half rfl)
    (hY := midpoint_vsub_left_half rfl)
    (hinner := hinner')

set_option maxHeartbeats 100000000

private lemma affine_interpolation_norm_sq_sub_general
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v z : V} (r : ℝ) :
    ‖z - r • u‖ ^ 2 - ‖z - r • v‖ ^ 2 =
      r * (2 * inner ℝ z (v - u) - r * (‖v‖ ^ 2 - ‖u‖ ^ 2)) := by
  rw [← real_inner_self_eq_norm_sq (z - r • u),
    ← real_inner_self_eq_norm_sq (z - r • v),
    ← real_inner_self_eq_norm_sq u,
    ← real_inner_self_eq_norm_sq v]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm u z, real_inner_comm v z]
  ring

private lemma gram_det_pos_of_two_coordinate_injective
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V}
    (hcoord : ∀ {a b : ℝ}, a • u + b • v = 0 → a = 0 ∧ b = 0) :
    0 < inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
  have hu : u ≠ 0 := by
    intro hu
    have h := hcoord (a := 1) (b := 0) (by simp [hu])
    norm_num at h
  have hv : v ≠ 0 := by
    intro hv
    have h := hcoord (a := 0) (b := 1) (by simp [hv])
    norm_num at h
  have hunorm : ‖u‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hu
  have hvnorm : ‖v‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hv
  have hposu : 0 < inner ℝ u u := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero hunorm
  have hposv : 0 < inner ℝ v v := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero hvnorm
  let w : V := inner ℝ v v • u - inner ℝ u v • v
  have hwinner : inner ℝ w w =
      (inner ℝ v v) ^ 2 * inner ℝ u u -
        2 * inner ℝ v v * (inner ℝ u v) ^ 2 +
          (inner ℝ u v) ^ 2 * inner ℝ v v := by
    dsimp [w]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm v u]
    ring
  have hwnorm : ‖w‖ ^ 2 = inner ℝ v v *
      (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) := by
    calc
      ‖w‖ ^ 2 = inner ℝ w w := (real_inner_self_eq_norm_sq w).symm
      _ = (inner ℝ v v) ^ 2 * inner ℝ u u -
          2 * inner ℝ v v * (inner ℝ u v) ^ 2 +
            (inner ℝ u v) ^ 2 * inner ℝ v v := hwinner
      _ = inner ℝ v v *
          (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) := by ring
  have hdet_ne : inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 ≠ 0 := by
    intro hdet
    have hwinner0 : inner ℝ w w = 0 := by
      rw [hwinner]
      calc
        (inner ℝ v v) ^ 2 * inner ℝ u u -
              2 * inner ℝ v v * (inner ℝ u v) ^ 2 +
                (inner ℝ u v) ^ 2 * inner ℝ v v =
            inner ℝ v v *
              (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) := by ring
        _ = 0 := by rw [hdet, mul_zero]
    have hwnorm0 : ‖w‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hwinner0
    have hwzero : w = 0 := by
      have : ‖w‖ = 0 := (sq_eq_zero_iff).mp hwnorm0
      exact norm_eq_zero.mp this
    have hc := hcoord (a := inner ℝ v v) (b := - inner ℝ u v) (by
      simpa [w, sub_eq_add_neg] using hwzero)
    exact (ne_of_gt hposv) hc.1
  have hdet_nonneg : 0 ≤ inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
    have hnonneg : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
    rw [hwnorm] at hnonneg
    nlinarith [hposv]
  exact lt_of_le_of_ne hdet_nonneg (Ne.symm hdet_ne)

private lemma zero_pair_of_positive_cross_relation
    {u v s y p q : ℝ}
    (hs : 0 < s) (hy : 0 < y) (hp : 0 < p) (hq : 0 < q)
    (hlin : s * u + y * v = 0)
    (hcross : u * p = q * v) :
    y * v - s * u = 0 := by
  have hdet : 0 < s * q + y * p := by positivity
  have hu_mul : u * (s * q + y * p) = 0 := by
    calc
      u * (s * q + y * p) = q * (s * u + y * v) + y * (u * p - q * v) := by ring
      _ = 0 := by rw [hlin, sub_eq_zero.mpr hcross]; ring
  have hu : u = 0 := by
    exact (mul_eq_zero.mp hu_mul).resolve_right (ne_of_gt hdet)
  have hv_mul : v * (s * q + y * p) = 0 := by
    calc
      v * (s * q + y * p) = p * (s * u + y * v) - s * (u * p - q * v) := by ring
      _ = 0 := by rw [hlin, sub_eq_zero.mpr hcross]; ring
  have hv : v = 0 := by
    exact (mul_eq_zero.mp hv_mul).resolve_right (ne_of_gt hdet)
  rw [hu, hv]
  ring

private lemma angle_scalar_cut
    {x y s t B C D U₁ V₁ W₁ Z₁ U₂ V₂ W₂ Z₂ U₃ V₃ W₃ Z₃ : ℝ}
    (hy : 0 < y) (hs : 0 < s)
    (hd₂ : 0 < t * (1 - x) - y * (1 - s))
    (hd₃ : 0 < x * (1 - t) - s * (1 - y))
    (hG : B * C - D ^ 2 ≠ 0)
    (hU₁ : 0 < U₁) (hV₁ : 0 < V₁) (hW₁ : 0 < W₁) (hZ₁ : 0 < Z₁)
    (hU₂ : 0 < U₂) (hV₂ : 0 < V₂) (hW₂ : 0 < W₂) (hZ₂ : 0 < Z₂)
    (hU₃ : 0 < U₃) (hV₃ : 0 < V₃) (hW₃ : 0 < W₃) (hZ₃ : 0 < Z₃)
    (hcos₁ : ((1 - x) * B - y * D) * U₁ * V₁ =
      W₁ * Z₁ * ((1 - t) * C - s * D))
    (heq₁ : ((1 - x) * B - y * D) ^ 2 * C *
          (s ^ 2 * B + 2 * s * (t - 1) * D + (t - 1) ^ 2 * C) =
        ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) * B *
          ((1 - t) * C - s * D) ^ 2)
    (hcos₂ : ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) * U₂ * V₂ =
        W₂ * Z₂ * (s * D + (t - 1 / 2) * C))
    (heq₂ : ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) ^ 2 *
          (s ^ 2 * B + 2 * s * (t - 1 / 2) * D +
            (t - 1 / 2) ^ 2 * C) * C =
        ((s - 1) ^ 2 * B + 2 * (s - 1) * t * D + t ^ 2 * C) *
          ((x - 1) ^ 2 * B + 2 * (x - 1) * y * D + y ^ 2 * C) *
          (s * D + (t - 1 / 2) * C) ^ 2)
    (hcos₃ : (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) * U₃ * V₃ =
        W₃ * Z₃ * ((x - 1 / 2) * B + y * D))
    (heq₃ : (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) ^ 2 * B *
          ((x - 1 / 2) ^ 2 * B + 2 * (x - 1 / 2) * y * D +
            y ^ 2 * C) =
        (s ^ 2 * B + 2 * s * (t - 1) * D +
            (t - 1) ^ 2 * C) *
          (x ^ 2 * B + 2 * x * (y - 1) * D +
            (y - 1) ^ 2 * C) *
          ((x - 1 / 2) * B + y * D) ^ 2) :
    (y * (1 - t) * C - s * (1 - x) * B = 0) ∧
      ((t * (1 - x) - y * (1 - s)) * (s * D + (t - 1 / 2) * C) -
        s * ((s - 1) * (x - 1) * B +
          ((s - 1) * y + t * (x - 1)) * D + t * y * C) = 0) ∧
      ((x * (1 - t) - s * (1 - y)) * ((x - 1 / 2) * B + y * D) -
        y * (s * x * B + (s * (y - 1) + (t - 1) * x) * D +
          (t - 1) * (y - 1) * C) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact scalar_equation_one hy hs hG hU₁ hV₁ hW₁ hZ₁ hcos₁ heq₁
  · exact scalar_equation_two hd₂ hs hG hU₂ hV₂ hW₂ hZ₂ hcos₂ heq₂
  · exact scalar_equation_three hd₃ hy hG hU₃ hV₃ hW₃ hZ₃ hcos₃ heq₃

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
  have hOA : dist O A = dist O K :=
    circumcenter_eq_dist_AK affineIndependent_AKL O_eq_circumcenter
  have hOL : dist O A = dist O L :=
    circumcenter_eq_dist_AL affineIndependent_AKL O_eq_circumcenter
  have hOK := eq_dist_to_sq_inner hOA
  have hOL' := eq_dist_to_sq_inner hOL
  have hweights := all_interior_weights affineIndependent_BMC affineIndependent_BNC
    affineIndependent_ABL affineIndependent_AKC K_mem_interior_BMC L_mem_interior_BNC
    K_mem_interior_ABL L_mem_interior_AKC
  rcases hweights with ⟨⟨w, hw, hw_sum, hK⟩, ⟨w₁, hw₁, hw₁_sum, hL⟩,
    ⟨w₂, hw₂, hw₂_sum, hK₂⟩, ⟨w₃, hw₃, hw₃_sum, hL₃⟩⟩
  subst M
  subst N
  have hcos₁ := congrArg Real.cos angle_KBA_eq_angle_ACL
  simp [EuclideanGeometry.angle, InnerProductGeometry.cos_angle] at hcos₁
  have hcos₂ := congrArg Real.cos angle_LBK_eq_angle_LNC
  simp [EuclideanGeometry.angle, InnerProductGeometry.cos_angle] at hcos₂
  have hcos₃ := congrArg Real.cos angle_LCK_eq_angle_BMK
  simp [EuclideanGeometry.angle, InnerProductGeometry.cos_angle] at hcos₃
  have hKB : (Finset.affineCombination ℝ Finset.univ ![B, midpoint ℝ A B, C]) w ≠ B := by
    intro h
    apply (Affine.Simplex.point_notMem_interior
      (s := (⟨![B, midpoint ℝ A B, C], affineIndependent_BMC⟩)) (i := (0 : Fin 3)))
    have h' : K = B := hK.symm.trans h
    simpa [h'] using K_mem_interior_BMC
  have hKB' : K ≠ B := by
    intro h
    exact hKB (hK.trans h)
  have hnormKB : ‖K -ᵥ B‖ ≠ 0 := by
    simpa [norm_ne_zero_iff] using hKB'
  have hAB : A ≠ B := by
    intro h
    have h' : (0 : Fin 3) = 1 := affineIndependent_ABC.injective (by simpa using h)
    exact Fin.zero_ne_one h'
  have hAC : A ≠ C := by
    intro h
    have h' : (0 : Fin 3) = 2 := affineIndependent_ABC.injective (by simpa using h)
    omega
  have hLC : L ≠ C := by
    have hLC₀ : (Finset.affineCombination ℝ Finset.univ ![B, midpoint ℝ A C, C]) w₁ ≠ C := by
      intro h
      apply (Affine.Simplex.point_notMem_interior
        (s := (⟨![B, midpoint ℝ A C, C], affineIndependent_BNC⟩)) (i := (2 : Fin 3)))
      have h' : L = C := hL.symm.trans h
      simpa [h'] using L_mem_interior_BNC
    intro h
    exact hLC₀ (hL.trans h)
  have hL_B : L ≠ B := by
    intro h
    apply (Affine.Simplex.point_notMem_interior
      (s := (⟨![B, midpoint ℝ A C, C], affineIndependent_BNC⟩)) (i := (0 : Fin 3)))
    have h' : L = B := h
    simpa [h'] using L_mem_interior_BNC
  have hL_N : L ≠ midpoint ℝ A C := by
    intro h
    apply (Affine.Simplex.point_notMem_interior
      (s := (⟨![B, midpoint ℝ A C, C], affineIndependent_BNC⟩)) (i := (1 : Fin 3)))
    have h' : L = midpoint ℝ A C := h
    simpa [h'] using L_mem_interior_BNC
  have hK_C : K ≠ C := by
    intro h
    apply (Affine.Simplex.point_notMem_interior
      (s := (⟨![B, midpoint ℝ A B, C], affineIndependent_BMC⟩)) (i := (2 : Fin 3)))
    have h' : K = C := h
    simpa [h'] using K_mem_interior_BMC
  have hK_M : K ≠ midpoint ℝ A B := by
    intro h
    apply (Affine.Simplex.point_notMem_interior
      (s := (⟨![B, midpoint ℝ A B, C], affineIndependent_BMC⟩)) (i := (1 : Fin 3)))
    have h' : K = midpoint ℝ A B := h
    simpa [h'] using K_mem_interior_BMC
  have hnormAB : ‖A -ᵥ B‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hAB
  have hnormAC : ‖A -ᵥ C‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hAC
  have hnormLC : ‖L -ᵥ C‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hLC
  have hnormLB : ‖L -ᵥ B‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hL_B
  have hnormLN : ‖L -ᵥ midpoint ℝ A C‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr (vsub_ne_zero.mpr hL_N)
  have hnormKC : ‖K -ᵥ C‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hK_C
  have hnormKM : ‖K -ᵥ midpoint ℝ A B‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hK_M
  have hCA : C ≠ A := by intro h; exact hAC h.symm
  have hBA : B ≠ A := by intro h; exact hAB h.symm
  have hnormCA : ‖C -ᵥ A‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hCA
  have hnormBA : ‖B -ᵥ A‖ ≠ 0 := by simpa [norm_ne_zero_iff] using hBA
  field_simp [hnormKB, hnormAB, hnormAC, hnormLC] at hcos₁
  field_simp [hnormLB, hnormKB, hnormLN, hnormCA] at hcos₂
  field_simp [hnormLC, hnormKC, hnormBA, hnormKM] at hcos₃
  have hK' := hK
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) (w := w) (p := ![B, midpoint ℝ A B, C]) hw_sum A] at hK'
  have hK'' := congrArg (fun X : P => X -ᵥ A) hK'
  rw [Finset.weightedVSubOfPoint_apply] at hK''
  norm_num [Fin.sum_univ_succ] at hK''
  have hL' := hL
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) (w := w₁) (p := ![B, midpoint ℝ A C, C]) hw₁_sum A] at hL'
  have hL'' := congrArg (fun X : P => X -ᵥ A) hL'
  rw [Finset.weightedVSubOfPoint_apply] at hL''
  norm_num [Fin.sum_univ_succ] at hL''
  have hKBv : K -ᵥ B = (K -ᵥ A) - (B -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_right]
  have hLCv : L -ᵥ C = (L -ᵥ A) - (C -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_right]
  have hLBv : L -ᵥ B = (L -ᵥ A) - (B -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_right]
  have hKCv : K -ᵥ C = (K -ᵥ A) - (C -ᵥ A) := by
    rw [vsub_sub_vsub_cancel_right]
  have hABv : A -ᵥ B = -(B -ᵥ A) := by
    rw [← neg_vsub_eq_vsub_rev]
  have hACv : A -ᵥ C = -(C -ᵥ A) := by
    rw [← neg_vsub_eq_vsub_rev]
  have hMCv : midpoint ℝ A C -ᵥ A = (1 / 2 : ℝ) • (C -ᵥ A) := by
    rw [midpoint_vsub_left]
    norm_num
  have hMBv : midpoint ℝ A B -ᵥ A = (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [midpoint_vsub_left]
    norm_num
  have hLNv : L -ᵥ midpoint ℝ A C =
      (L -ᵥ A) - (1 / 2 : ℝ) • (C -ᵥ A) := by
    rw [← hMCv, vsub_sub_vsub_cancel_right]
  have hKMv : K -ᵥ midpoint ℝ A B =
      (K -ᵥ A) - (1 / 2 : ℝ) • (B -ᵥ A) := by
    rw [← hMBv, vsub_sub_vsub_cancel_right]
  have hc1 := congrArg (fun x : ℝ => x ^ 2) hcos₁
  have hc2 := congrArg (fun x : ℝ => x ^ 2) hcos₂
  have hc3 := congrArg (fun x : ℝ => x ^ 2) hcos₃
  ring_nf at hc1 hc2 hc3
  have norm_sq_eq_inner (x : V) : ‖x‖ ^ 2 = inner ℝ x x := by
    symm
    exact real_inner_self_eq_norm_sq x
  simp only [norm_sq_eq_inner] at hc1 hc2 hc3
  rw [hKBv, hABv, hACv, hLCv] at hc1
  rw [hLBv, hKBv, hLNv] at hc2
  rw [hLCv, hKCv, hKMv] at hc3
  rw [← hK'', ← hL''] at hc1 hc2 hc3
  have hKform :
      w 0 • (B -ᵥ A) + (w 1 • (1 / 2 : ℝ) • (B -ᵥ A) + w 2 • (C -ᵥ A)) =
        (w 0 + w 1 / 2) • (B -ᵥ A) + w 2 • (C -ᵥ A) := by
    rw [smul_smul]
    module
  have hLform :
      w₁ 0 • (B -ᵥ A) + (w₁ 1 • (1 / 2 : ℝ) • (C -ᵥ A) + w₁ 2 • (C -ᵥ A)) =
        w₁ 0 • (B -ᵥ A) + (w₁ 1 / 2 + w₁ 2) • (C -ᵥ A) := by
    rw [smul_smul]
    module
  have hKsubB :
      (w 0 • (B -ᵥ A) + (w 1 • (1 / 2 : ℝ) • (B -ᵥ A) + w 2 • (C -ᵥ A))) - (B -ᵥ A) =
        (w 0 + w 1 / 2 - 1) • (B -ᵥ A) + w 2 • (C -ᵥ A) := by
    rw [hKform]
    module
  have hKsubC :
      (w 0 • (B -ᵥ A) + (w 1 • (1 / 2 : ℝ) • (B -ᵥ A) + w 2 • (C -ᵥ A))) - (C -ᵥ A) =
        (w 0 + w 1 / 2) • (B -ᵥ A) + (w 2 - 1) • (C -ᵥ A) := by
    rw [hKform]
    module
  have hKsubM :
      (w 0 • (B -ᵥ A) + (w 1 • (1 / 2 : ℝ) • (B -ᵥ A) + w 2 • (C -ᵥ A))) -
          (1 / 2 : ℝ) • (B -ᵥ A) =
        (w 0 + w 1 / 2 - 1 / 2) • (B -ᵥ A) + w 2 • (C -ᵥ A) := by
    rw [hKform]
    module
  have hLsubB :
      (w₁ 0 • (B -ᵥ A) + (w₁ 1 • (1 / 2 : ℝ) • (C -ᵥ A) + w₁ 2 • (C -ᵥ A))) - (B -ᵥ A) =
        (w₁ 0 - 1) • (B -ᵥ A) + (w₁ 1 / 2 + w₁ 2) • (C -ᵥ A) := by
    rw [hLform]
    module
  have hLsubC :
      (w₁ 0 • (B -ᵥ A) + (w₁ 1 • (1 / 2 : ℝ) • (C -ᵥ A) + w₁ 2 • (C -ᵥ A))) - (C -ᵥ A) =
        w₁ 0 • (B -ᵥ A) + (w₁ 1 / 2 + w₁ 2 - 1) • (C -ᵥ A) := by
    rw [hLform]
    module
  have hLsubN :
      (w₁ 0 • (B -ᵥ A) + (w₁ 1 • (1 / 2 : ℝ) • (C -ᵥ A) + w₁ 2 • (C -ᵥ A))) -
          (1 / 2 : ℝ) • (C -ᵥ A) =
        w₁ 0 • (B -ᵥ A) + (w₁ 1 / 2 + w₁ 2 - 1 / 2) • (C -ᵥ A) := by
    rw [hLform]
    module
  rw [hKsubB, hLsubC] at hc1
  rw [hLsubB, hKsubB, hLsubN] at hc2
  rw [hLsubC, hKsubC, hKsubM] at hc3
  have inner_left (a b : ℝ) (x y z : V) :
      inner ℝ (a • x + b • y) z =
        a * inner ℝ x z + b * inner ℝ y z := by
    simp only [inner_add_left, real_inner_smul_left]
  have inner_right (a b : ℝ) (x y z : V) :
      inner ℝ z (a • x + b • y) =
        a * inner ℝ z x + b * inner ℝ z y := by
    simp only [inner_add_right, real_inner_smul_right]
  repeat rw [inner_left] at hc1
  repeat rw [inner_left] at hc2
  repeat rw [inner_left] at hc3
  repeat rw [inner_right] at hc1
  repeat rw [inner_right] at hc2
  repeat rw [inner_right] at hc3
  have hsym : inner ℝ (C -ᵥ A) (B -ᵥ A) = inner ℝ (B -ᵥ A) (C -ᵥ A) := by
    rw [real_inner_comm]
  rw [hsym] at hc1 hc2 hc3
  generalize hbb : inner ℝ (B -ᵥ A) (B -ᵥ A) = bb at hc1 hc2 hc3
  generalize hcc : inner ℝ (C -ᵥ A) (C -ᵥ A) = cc at hc1 hc2 hc3
  generalize hbc : inner ℝ (B -ᵥ A) (C -ᵥ A) = bc at hc1 hc2 hc3
  let x : ℝ := w 0 + w 1 / 2
  let y : ℝ := w 2
  let s : ℝ := w₁ 0
  let t : ℝ := w₁ 1 / 2 + w₁ 2
  let Bq : ℝ := inner ℝ (B -ᵥ A) (B -ᵥ A)
  let Cq : ℝ := inner ℝ (C -ᵥ A) (C -ᵥ A)
  let Dq : ℝ := inner ℝ (B -ᵥ A) (C -ᵥ A)
  let qb : ℝ := inner ℝ (O -ᵥ A) (B -ᵥ A)
  let qc : ℝ := inner ℝ (O -ᵥ A) (C -ᵥ A)
  have hKcoord : K -ᵥ A = x • (B -ᵥ A) + y • (C -ᵥ A) := by
    rw [← hK'']
    dsimp [x, y]
    rw [smul_smul]
    module
  have hLcoord : L -ᵥ A = s • (B -ᵥ A) + t • (C -ᵥ A) := by
    rw [← hL'']
    dsimp [s, t]
    rw [smul_smul]
    module
  have hKsubBq : K -ᵥ B = (x - 1) • (B -ᵥ A) + y • (C -ᵥ A) := by
    rw [hKBv, hKcoord]
    module
  have hKsubCq : K -ᵥ C = x • (B -ᵥ A) + (y - 1) • (C -ᵥ A) := by
    rw [hKCv, hKcoord]
    module
  have hLsubBq : L -ᵥ B = (s - 1) • (B -ᵥ A) + t • (C -ᵥ A) := by
    rw [hLBv, hLcoord]
    module
  have hLsubCq : L -ᵥ C = s • (B -ᵥ A) + (t - 1) • (C -ᵥ A) := by
    rw [hLCv, hLcoord]
    module
  have hKsubMq : K -ᵥ midpoint ℝ A B = (x - 1 / 2) • (B -ᵥ A) + y • (C -ᵥ A) := by
    rw [hKMv, hKcoord]
    module
  have hLsubNq : L -ᵥ midpoint ℝ A C = s • (B -ᵥ A) + (t - 1 / 2) • (C -ᵥ A) := by
    rw [hLNv, hLcoord]
    module
  have hnorm_KB : ‖K -ᵥ B‖ ^ 2 =
      (x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq := by
    rw [hKsubBq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LC : ‖L -ᵥ C‖ ^ 2 =
      s ^ 2 * Bq + 2 * s * (t - 1) * Dq + (t - 1) ^ 2 * Cq := by
    rw [hLsubCq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LB : ‖L -ᵥ B‖ ^ 2 =
      (s - 1) ^ 2 * Bq + 2 * (s - 1) * t * Dq + t ^ 2 * Cq := by
    rw [hLsubBq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_KC : ‖K -ᵥ C‖ ^ 2 =
      x ^ 2 * Bq + 2 * x * (y - 1) * Dq + (y - 1) ^ 2 * Cq := by
    rw [hKsubCq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_KM : ‖K -ᵥ midpoint ℝ A B‖ ^ 2 =
      (x - 1 / 2) ^ 2 * Bq + 2 * (x - 1 / 2) * y * Dq + y ^ 2 * Cq := by
    rw [hKsubMq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_LN : ‖L -ᵥ midpoint ℝ A C‖ ^ 2 =
      s ^ 2 * Bq + 2 * s * (t - 1 / 2) * Dq +
        (t - 1 / 2) ^ 2 * Cq := by
    rw [hLsubNq]
    dsimp [Bq, Cq, Dq]
    rw [real_inner_self_eq_norm_sq]
    simp only [norm_sq_eq_inner, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hnorm_AB : ‖A -ᵥ B‖ ^ 2 = Bq := by
    rw [hABv, norm_sq_eq_inner]
    dsimp [Bq]
    simp only [inner_neg_left, inner_neg_right]
    ring
  have hnorm_AC : ‖A -ᵥ C‖ ^ 2 = Cq := by
    rw [hACv, norm_sq_eq_inner]
    dsimp [Cq]
    simp only [inner_neg_left, inner_neg_right]
    ring
  have hi1 : inner ℝ (K -ᵥ B) (A -ᵥ B) = (1 - x) * Bq - y * Dq := by
    rw [hKsubBq, hABv]
    dsimp [Bq, Dq]
    simp only [inner_add_left, real_inner_smul_left, inner_neg_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hi2 : inner ℝ (A -ᵥ C) (L -ᵥ C) = (1 - t) * Cq - s * Dq := by
    rw [hACv, hLsubCq]
    dsimp [Cq, Dq]
    simp only [inner_add_right, real_inner_smul_right, inner_neg_left]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hc1sq :
      inner ℝ (K -ᵥ B) (A -ᵥ B) ^ 2 * ‖A -ᵥ C‖ ^ 2 * ‖L -ᵥ C‖ ^ 2 =
        ‖K -ᵥ B‖ ^ 2 * ‖A -ᵥ B‖ ^ 2 * inner ℝ (A -ᵥ C) (L -ᵥ C) ^ 2 := by
    apply sq_inner_cross_multiplication
    convert hcos₁ using 1 <;> ring
  have hc1c :
      ((1 - x) * Bq - y * Dq) ^ 2 * Cq *
          (s ^ 2 * Bq + 2 * s * (t - 1) * Dq + (t - 1) ^ 2 * Cq) =
        ((x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq) * Bq *
          ((1 - t) * Cq - s * Dq) ^ 2 := by
    rw [hi1, hi2, hnorm_AB, hnorm_AC, hnorm_KB, hnorm_LC] at hc1sq
    exact hc1sq
  have hBqpos : 0 < Bq := by
    dsimp [Bq]
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero hnormBA
  have hCqpos : 0 < Cq := by
    dsimp [Cq]
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_ne_zero hnormCA
  have hGne : Bq * Cq - Dq ^ 2 ≠ 0 := by
    intro hG
    let v : V := Cq • (B -ᵥ A) - Dq • (C -ᵥ A)
    have hvinner : inner ℝ v v =
        Cq ^ 2 * Bq - 2 * Cq * Dq ^ 2 + Dq ^ 2 * Cq := by
      dsimp [v, Bq, Cq, Dq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right]
      rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
      ring
    have hvinner0 : inner ℝ v v = 0 := by
      rw [hvinner]
      calc
        Cq ^ 2 * Bq - 2 * Cq * Dq ^ 2 + Dq ^ 2 * Cq =
            Cq * (Bq * Cq - Dq ^ 2) := by ring
        _ = 0 := by rw [hG, mul_zero]
    have hvnorm : ‖v‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hvinner0
    have hvzero : v = 0 := by
      have : ‖v‖ = 0 := (sq_eq_zero_iff).mp hvnorm
      exact norm_eq_zero.mp this
    let r : Fin 3 → ℝ := ![-Cq + Dq, Cq, -Dq]
    have hrsum : ∑ i, r i = 0 := by
      norm_num [r, Fin.sum_univ_succ] <;> ring
    have hrsum' : ∑ i ∈ (Finset.univ : Finset (Fin 3)), r i = 0 := by
      simpa using hrsum
    have hrs : Finset.univ.weightedVSub ![A, B, C] r = (0 : V) := by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
        (s := Finset.univ) r ![A, B, C] hrsum' A]
      rw [Finset.weightedVSubOfPoint_apply]
      simpa [Fin.sum_univ_succ, r, v, sub_eq_add_neg] using hvzero
    have hri : r 1 = 0 := by
      exact affineIndependent_ABC Finset.univ r hrsum' hrs 1 (by simp)
    dsimp [r] at hri
    exact (ne_of_gt hCqpos) hri
  have hcoord_zero : ∀ {a b : ℝ},
      a • (B -ᵥ A) + b • (C -ᵥ A) = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    let r : Fin 3 → ℝ := ![-a - b, a, b]
    have hrsum : ∑ i, r i = 0 := by
      norm_num [r, Fin.sum_univ_succ]
    have hrsum' : ∑ i ∈ (Finset.univ : Finset (Fin 3)), r i = 0 := by
      simpa using hrsum
    have hrs : Finset.univ.weightedVSub ![A, B, C] r = (0 : V) := by
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero
        (s := Finset.univ) r ![A, B, C] hrsum' A]
      rw [Finset.weightedVSubOfPoint_apply]
      simpa [Fin.sum_univ_succ, r, sub_eq_add_neg] using hab
    have hri1 : r 1 = 0 :=
      affineIndependent_ABC Finset.univ r hrsum' hrs 1 (by simp)
    have hri2 : r 2 = 0 :=
      affineIndependent_ABC Finset.univ r hrsum' hrs 2 (by simp)
    dsimp [r] at hri1 hri2
    exact ⟨hri1, hri2⟩
  have hK₂' := hK₂
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) (w := w₂) (p := ![A, B, L]) hw₂_sum A] at hK₂'
  have hK₂'' := congrArg (fun X : P => X -ᵥ A) hK₂'
  rw [Finset.weightedVSubOfPoint_apply] at hK₂''
  norm_num [Fin.sum_univ_succ] at hK₂''
  have hL₃' := hL₃
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (s := Finset.univ) (w := w₃) (p := ![A, K, C]) hw₃_sum A] at hL₃'
  have hL₃'' := congrArg (fun X : P => X -ᵥ A) hL₃'
  rw [Finset.weightedVSubOfPoint_apply] at hL₃''
  norm_num [Fin.sum_univ_succ] at hL₃''
  have hKcoord₂' :
      (w₂ 1 + w₂ 2 * s) • (B -ᵥ A) +
          (w₂ 2 * t) • (C -ᵥ A) =
        x • (B -ᵥ A) + y • (C -ᵥ A) := by
    rw [hKcoord, hLcoord] at hK₂''
    simpa [smul_add, smul_smul, add_smul, add_assoc] using hK₂''
  have hKcoord₂ :
      (x - (w₂ 1 + w₂ 2 * s)) • (B -ᵥ A) +
          (y - w₂ 2 * t) • (C -ᵥ A) = 0 := by
    calc
      _ = (x • (B -ᵥ A) + y • (C -ᵥ A)) -
          ((w₂ 1 + w₂ 2 * s) • (B -ᵥ A) +
            (w₂ 2 * t) • (C -ᵥ A)) := by module
      _ = 0 := by rw [hKcoord₂']; module
  have hLcoord₃' :
      (w₃ 1 * x) • (B -ᵥ A) +
          (w₃ 1 * y + w₃ 2) • (C -ᵥ A) =
        s • (B -ᵥ A) + t • (C -ᵥ A) := by
    rw [hLcoord, hKcoord] at hL₃''
    simpa [smul_add, smul_smul, add_smul, add_assoc] using hL₃''
  have hLcoord₃ :
      (s - w₃ 1 * x) • (B -ᵥ A) +
          (t - (w₃ 1 * y + w₃ 2)) • (C -ᵥ A) = 0 := by
    calc
      _ = (s • (B -ᵥ A) + t • (C -ᵥ A)) -
          ((w₃ 1 * x) • (B -ᵥ A) +
            (w₃ 1 * y + w₃ 2) • (C -ᵥ A)) := by module
      _ = 0 := by rw [hLcoord₃']; module
  have hxcoord : x = w₂ 1 + w₂ 2 * s := by
    have hh := hcoord_zero hKcoord₂
    exact sub_eq_zero.mp hh.1
  have hycoord : y = w₂ 2 * t := by
    have hh := hcoord_zero hKcoord₂
    exact sub_eq_zero.mp hh.2
  have hscoord : s = w₃ 1 * x := by
    have hh := hcoord_zero hLcoord₃
    exact sub_eq_zero.mp hh.1
  have htcoord : t = w₃ 1 * y + w₃ 2 := by
    have hh := hcoord_zero hLcoord₃
    exact sub_eq_zero.mp hh.2
  have hcoords := coordinate_cycle_positivity
    (w := w) (w₁ := w₁) (w₂ := w₂) (w₃ := w₃)
    hw hw₁ hw₂ hw₃ hw_sum hw₁_sum hw₂_sum hw₃_sum
    (by rfl) (by rfl) hxcoord hycoord hscoord htcoord
  rcases hcoords with ⟨hxpos, htpos, hypos, hspos, h1xpos, h1tpos,
    hd2pos, hd3pos, hdetpos, hx, ht⟩
  have hdet : x * t - y * s ≠ 0 := ne_of_gt hdetpos
  have hi2b : inner ℝ (L -ᵥ B) (K -ᵥ B) =
      (s - 1) * (x - 1) * Bq +
        ((s - 1) * y + t * (x - 1)) * Dq + t * y * Cq := by
    rw [hLsubBq, hKsubBq]
    dsimp [Bq, Cq, Dq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hi2n : inner ℝ (L -ᵥ midpoint ℝ A C) (C -ᵥ A) =
      s * Dq + (t - 1 / 2) * Cq := by
    rw [hLsubNq]
    dsimp [Bq, Cq, Dq]
    simp only [inner_add_left, real_inner_smul_left]
  have hi3c : inner ℝ (L -ᵥ C) (K -ᵥ C) =
      s * x * Bq + (s * (y - 1) + (t - 1) * x) * Dq +
        (t - 1) * (y - 1) * Cq := by
    rw [hLsubCq, hKsubCq]
    dsimp [Bq, Cq, Dq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [real_inner_comm (C -ᵥ A) (B -ᵥ A)]
    ring
  have hi3m : inner ℝ (B -ᵥ A) (K -ᵥ midpoint ℝ A B) =
      (x - 1 / 2) * Bq + y * Dq := by
    rw [hKsubMq]
    dsimp [Bq, Cq, Dq]
    simp only [inner_add_right, real_inner_smul_right]
  have he1 : y * (1 - t) * Cq - s * (1 - x) * Bq = 0 := by
    have hfac :
        (y * (1 - t) * Cq - s * (1 - x) * Bq) *
            (Bq * Cq - Dq ^ 2) *
            (s * (x - 1) * Bq + y * (t - 1) * Cq + 2 * s * y * Dq) = 0 := by
      exact scalar_factor_one hc1c
    rcases mul_eq_zero.mp hfac with hfac | hq
    · rcases mul_eq_zero.mp hfac with he | hG
      · exact he
      · exact (hGne hG).elim
    · have hnormACpos : 0 < ‖A -ᵥ C‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormAC)
      have hnormLCpos : 0 < ‖L -ᵥ C‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLC)
      have hnormKBpos : 0 < ‖K -ᵥ B‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKB)
      have hnormABpos : 0 < ‖A -ᵥ B‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormAB)
      have hcos1' := hcos₁
      rw [hi1, hi2] at hcos1'
      let u : ℝ := (1 - x) * Bq - y * Dq
      let v : ℝ := (1 - t) * Cq - s * Dq
      have huq : s * u + y * v = 0 := by
        dsimp [u, v]
        calc
          _ = -(s * (x - 1) * Bq + y * (t - 1) * Cq + 2 * s * y * Dq) := by ring
          _ = 0 := by rw [hq]; ring
      have hcos1'' :
          u * ‖A -ᵥ C‖ * ‖L -ᵥ C‖ =
            ‖K -ᵥ B‖ * ‖A -ᵥ B‖ * v := by
        simpa [u, v] using hcos1'
      have hcross :
          u * (‖A -ᵥ C‖ * ‖L -ᵥ C‖) =
            (‖K -ᵥ B‖ * ‖A -ᵥ B‖) * v := by
        simpa [mul_assoc] using hcos1''
      calc
        y * (1 - t) * Cq - s * (1 - x) * Bq = y * v - s * u := by
          dsimp [u, v]
          ring
        _ = 0 := zero_pair_of_positive_cross_relation
          hspos hypos (mul_pos hnormACpos hnormLCpos)
          (mul_pos hnormKBpos hnormABpos) huq hcross
  have hc2c :
      ((s - 1) * (x - 1) * Bq +
          ((s - 1) * y + t * (x - 1)) * Dq + t * y * Cq) ^ 2 *
          (s ^ 2 * Bq + 2 * s * (t - 1 / 2) * Dq +
            (t - 1 / 2) ^ 2 * Cq) * Cq =
        ((s - 1) ^ 2 * Bq + 2 * (s - 1) * t * Dq + t ^ 2 * Cq) *
          ((x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq) *
          (s * Dq + (t - 1 / 2) * Cq) ^ 2 := by
    rw [← hbb, ← hcc, ← hbc] at hc2
    convert hc2 using 1 <;> dsimp [x, y, s, t, Bq, Cq, Dq] <;> ring
  have he2 :
      (t * (1 - x) - y * (1 - s)) * (s * Dq + (t - 1 / 2) * Cq) -
        s * ((s - 1) * (x - 1) * Bq +
          ((s - 1) * y + t * (x - 1)) * Dq + t * y * Cq) = 0 := by
    let p : ℝ := (s - 1) * (x - 1) * Bq +
      ((s - 1) * y + t * (x - 1)) * Dq + t * y * Cq
    let n : ℝ := s * Dq + (t - 1 / 2) * Cq
    let d : ℝ := t * (1 - x) - y * (1 - s)
    have hfac :
        (d * n - s * p) * (Bq * Cq - Dq ^ 2) *
            (d * n + s * p) = 0 := by
      calc
        _ = -(
          p ^ 2 *
              (s ^ 2 * Bq + 2 * s * (t - 1 / 2) * Dq +
                (t - 1 / 2) ^ 2 * Cq) * Cq -
            ((s - 1) ^ 2 * Bq + 2 * (s - 1) * t * Dq + t ^ 2 * Cq) *
              ((x - 1) ^ 2 * Bq + 2 * (x - 1) * y * Dq + y ^ 2 * Cq) *
              n ^ 2) := by
                dsimp [p, n, d]
                ring
        _ = 0 := by rw [hc2c]; ring
    by_cases he : d * n - s * p = 0
    · dsimp [p, n, d] at he
      exact he
    · have hq : d * n + s * p = 0 := by
        rcases mul_eq_zero.mp hfac with hAG | hq
        · have hG : Bq * Cq - Dq ^ 2 = 0 :=
            (mul_eq_zero.mp hAG).resolve_left he
          exact (hGne hG).elim
        · exact hq
      have hnormLNpos : 0 < ‖L -ᵥ midpoint ℝ A C‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLN)
      have hnormCApos : 0 < ‖C -ᵥ A‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormCA)
      have hnormLBpos : 0 < ‖L -ᵥ B‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLB)
      have hnormKBpos : 0 < ‖K -ᵥ B‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKB)
      have hcos2' := hcos₂
      rw [hi2b, hi2n] at hcos2'
      have hcos2'' :
          p * ‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖ =
            ‖L -ᵥ B‖ * ‖K -ᵥ B‖ * n := by
        simpa [p, n] using hcos2'
      have hcos2''' :
          p * (‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖) -
              ‖L -ᵥ B‖ * ‖K -ᵥ B‖ * n = 0 := by
        calc
          _ = p * ‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖ -
              ‖L -ᵥ B‖ * ‖K -ᵥ B‖ * n := by ring
          _ = 0 := sub_eq_zero.mpr hcos2''
      have hposfac :
          0 < d * (‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖) +
            (‖L -ᵥ B‖ * ‖K -ᵥ B‖) * s := by
        positivity
      have hp0 : p = 0 := by
        have hp_mul :
            p * (d * (‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖) +
              (‖L -ᵥ B‖ * ‖K -ᵥ B‖) * s) = 0 := by
          calc
            _ = d * (p * (‖L -ᵥ midpoint ℝ A C‖ * ‖C -ᵥ A‖) -
                  (‖L -ᵥ B‖ * ‖K -ᵥ B‖) * n) +
                (‖L -ᵥ B‖ * ‖K -ᵥ B‖) * (d * n + s * p) := by ring
            _ = 0 := by rw [hcos2''', hq]; ring
        exact (mul_eq_zero.mp hp_mul).resolve_right (ne_of_gt hposfac)
      have hn0 : n = 0 := by
        have hdn : d * n = 0 := by
          calc
            d * n = (d * n + s * p) - s * p := by ring
            _ = 0 := by rw [hq, hp0]; ring
        exact (mul_eq_zero.mp hdn).resolve_left (ne_of_gt hd2pos)
      change d * n - s * p = 0
      rw [hp0, hn0]
      ring
  have hc3c :
      (s * x * Bq + (s * (y - 1) + (t - 1) * x) * Dq +
          (t - 1) * (y - 1) * Cq) ^ 2 * Bq *
          ((x - 1 / 2) ^ 2 * Bq + 2 * (x - 1 / 2) * y * Dq +
            y ^ 2 * Cq) =
        (s ^ 2 * Bq + 2 * s * (t - 1) * Dq +
            (t - 1) ^ 2 * Cq) *
          (x ^ 2 * Bq + 2 * x * (y - 1) * Dq +
            (y - 1) ^ 2 * Cq) *
          ((x - 1 / 2) * Bq + y * Dq) ^ 2 := by
    rw [← hbb, ← hcc, ← hbc] at hc3
    convert hc3 using 1 <;> dsimp [x, y, s, t, Bq, Cq, Dq] <;> ring
  have he3 :
      (x * (1 - t) - s * (1 - y)) * ((x - 1 / 2) * Bq + y * Dq) -
        y * (s * x * Bq + (s * (y - 1) + (t - 1) * x) * Dq +
          (t - 1) * (y - 1) * Cq) = 0 := by
    let p : ℝ := s * x * Bq + (s * (y - 1) + (t - 1) * x) * Dq +
      (t - 1) * (y - 1) * Cq
    let n : ℝ := (x - 1 / 2) * Bq + y * Dq
    let d : ℝ := x * (1 - t) - s * (1 - y)
    have hfac :
        (d * n - y * p) * (Bq * Cq - Dq ^ 2) *
            (d * n + y * p) = 0 := by
      calc
        _ = -(
          p ^ 2 * Bq *
              ((x - 1 / 2) ^ 2 * Bq + 2 * (x - 1 / 2) * y * Dq +
                y ^ 2 * Cq) -
            (s ^ 2 * Bq + 2 * s * (t - 1) * Dq + (t - 1) ^ 2 * Cq) *
              (x ^ 2 * Bq + 2 * x * (y - 1) * Dq +
                (y - 1) ^ 2 * Cq) * n ^ 2) := by
                dsimp [p, n, d]
                ring
        _ = 0 := by rw [hc3c]; ring
    by_cases he : d * n - y * p = 0
    · dsimp [p, n, d] at he
      exact he
    · have hq : d * n + y * p = 0 := by
        rcases mul_eq_zero.mp hfac with hAG | hq
        · have hG : Bq * Cq - Dq ^ 2 = 0 :=
            (mul_eq_zero.mp hAG).resolve_left he
          exact (hGne hG).elim
        · exact hq
      have hnormBApos : 0 < ‖B -ᵥ A‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormBA)
      have hnormKMpos : 0 < ‖K -ᵥ midpoint ℝ A B‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKM)
      have hnormLCpos : 0 < ‖L -ᵥ C‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLC)
      have hnormKCpos : 0 < ‖K -ᵥ C‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKC)
      have hcos3' := hcos₃
      rw [hi3c] at hcos3'
      rw [hi3m] at hcos3'
      have hcos3'' :
          p * ‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖ =
            ‖L -ᵥ C‖ * ‖K -ᵥ C‖ * n := by
        convert hcos3' using 1
      have hcos3''' :
          p * (‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖) -
              ‖L -ᵥ C‖ * ‖K -ᵥ C‖ * n = 0 := by
        calc
          _ = p * ‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖ -
              ‖L -ᵥ C‖ * ‖K -ᵥ C‖ * n := by ring
          _ = 0 := sub_eq_zero.mpr hcos3''
      have hposfac :
          0 < d * (‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖) +
            (‖L -ᵥ C‖ * ‖K -ᵥ C‖) * y := by
        positivity
      have hp0 : p = 0 := by
        have hp_mul :
            p * (d * (‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖) +
              (‖L -ᵥ C‖ * ‖K -ᵥ C‖) * y) = 0 := by
          calc
            _ = d * (p * (‖B -ᵥ A‖ * ‖K -ᵥ midpoint ℝ A B‖) -
                  (‖L -ᵥ C‖ * ‖K -ᵥ C‖) * n) +
                (‖L -ᵥ C‖ * ‖K -ᵥ C‖) * (d * n + y * p) := by ring
            _ = 0 := by rw [hcos3''', hq]; ring
        exact (mul_eq_zero.mp hp_mul).resolve_right (ne_of_gt hposfac)
      have hn0 : n = 0 := by
        have hdn : d * n = 0 := by
          calc
            d * n = (d * n + y * p) - y * p := by ring
            _ = 0 := by rw [hq, hp0]; ring
        exact (mul_eq_zero.mp hdn).resolve_left (ne_of_gt hd3pos)
      change d * n - y * p = 0
      rw [hp0, hn0]
      ring
  have hcos1alg := hcos₁
  rw [hi1, hi2] at hcos1alg
  have hcos2alg := hcos₂
  rw [hi2b, hi2n] at hcos2alg
  have hcos3alg := hcos₃
  rw [hi3c, hi3m] at hcos3alg
  have hcut := angle_scalar_cut
    (x := x) (y := y) (s := s) (t := t) (B := Bq) (C := Cq) (D := Dq)
    (U₁ := ‖A -ᵥ C‖) (V₁ := ‖L -ᵥ C‖) (W₁ := ‖K -ᵥ B‖) (Z₁ := ‖A -ᵥ B‖)
    (U₂ := ‖L -ᵥ midpoint ℝ A C‖) (V₂ := ‖C -ᵥ A‖)
    (W₂ := ‖L -ᵥ B‖) (Z₂ := ‖K -ᵥ B‖)
    (U₃ := ‖B -ᵥ A‖) (V₃ := ‖K -ᵥ midpoint ℝ A B‖)
    (W₃ := ‖L -ᵥ C‖) (Z₃ := ‖K -ᵥ C‖)
    hypos hspos hd2pos hd3pos hGne
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormAC))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLC))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKB))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormAB))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLN))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormCA))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLB))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKB))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormBA))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKM))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormLC))
    (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnormKC))
    hcos1alg hc1c hcos2alg hc2c hcos3alg hc3c
  rcases hcut with ⟨he1, he2, he3⟩
  have hw₂2lt : w₂ 2 < 1 := by
    have hpos : 0 < w₂ 0 + w₂ 1 := add_pos (hw₂ 0) (hw₂ 1)
    calc
      w₂ 2 < w₂ 0 + w₂ 1 + w₂ 2 := by linarith only [hpos]
      _ = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hw₂_sum
  have hw₃1lt : w₃ 1 < 1 := by
    have hpos : 0 < w₃ 0 + w₃ 2 := add_pos (hw₃ 0) (hw₃ 2)
    calc
      w₃ 1 < w₃ 0 + w₃ 1 + w₃ 2 := by linarith only [hpos]
      _ = 1 := by simpa [Fin.sum_univ_succ, add_assoc] using hw₃_sum
  have hdetpos : 0 < x * t - y * s := by
    exact determinant_positive_of_two_coordinate_cycles hxpos htpos
      (hw₂ 2) hw₂2lt (hw₃ 1) hw₃1lt hycoord hscoord
  have hdet : x * t - y * s ≠ 0 := ne_of_gt hdetpos
  have hx : x ≠ 1 := by linarith
  have ht : t ≠ 1 := by linarith
  have hk :
      2 * (x * qb + y * qc) = x ^ 2 * Bq + 2 * x * y * Dq + y ^ 2 * Cq := by
    exact quadratic_identity_of_inner_eq_norm hKcoord hOK rfl rfl rfl rfl rfl
  have hl :
      2 * (s * qb + t * qc) = s ^ 2 * Bq + 2 * s * t * Dq + t ^ 2 * Cq := by
    exact quadratic_identity_of_inner_eq_norm hLcoord hOL' rfl rfl rfl rfl rfl
  have hscalar : 2 * (qc - qb) = (Cq - Bq) / 2 :=
    algebraic_target hdet hx ht he1 he2 he3 hk hl
  have hinner :
      inner ℝ (O -ᵥ A) ((C -ᵥ A) - (B -ᵥ A)) =
        (inner ℝ (C -ᵥ A) (C -ᵥ A) - inner ℝ (B -ᵥ A) (B -ᵥ A)) / 4 :=
    inner_difference_from_quadratic_identity rfl rfl rfl rfl hscalar
  exact finish_midpoint_distance_from_inner hinner


end IMO2026P2
