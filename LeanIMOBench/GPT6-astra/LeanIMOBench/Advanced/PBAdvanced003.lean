import LeanFlowProofs.PB003CoefficientCollinearity
import LeanFlowProofs.PB003ForwardBisector
import LeanFlowProofs.PB003NegativePowerSecant
import LeanFlowProofs.PB003ScalarData
import Mathlib

/-
Let $ ABC $ be an acute triangle which is not an isosceles.Let $ I $ be the incenter and let $ \omega $ be the circumcircle of $ABC$. Let the intersections of lines $ AI $, $ BI $, and $ CI $ with $ BC $, $ CA $, and $ AB $ be $ D $, $ E $, and $ F $ respectively. Also, let $ \omega_A $ be the circle that lies inside $\angle BAC$, tangent to lines $ AB $ and $ AC $, and internally tangent to the circumcircle $ \omega $ at $ T_A $. Similarly, define $ T_B $ and $ T_C $ for points $ B $ and $ C $ respectively. Prove that there exist two points $ X $ and $ Y $ such that the circumcircles of triangles $ ADT_A $, $ BET_B $, and $ CFT_C $ all pass through $ X $ and $ Y $.
-/

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
open EuclideanGeometry Real InnerProductSpace Set Affine Simplex

/--
A helper predicate to define the point of tangency `T` of the `A`-mixtilinear incircle
with the circumcircle `ω`.
The `A`-mixtilinear incircle is the circle lying inside angle `A`, tangent to sides `AB` and `AC`,
and internally tangent to the circumcircle `ω`.
-/
def IsMixtilinearTouchPoint (A B C T : ℝ²) (ω : Sphere ℝ²) : Prop :=
  ∃ (c : Sphere ℝ²),
    -- The circle c is tangent to lines AB and AC
    c.IsTangent (affineSpan ℝ {A, B}) ∧
    c.IsTangent (affineSpan ℝ {A, C}) ∧
    c.IsIntTangentAt ω T

/--
The main statement
-/
theorem PBAdvanced003
  (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
  -- Triangle ABC is acute
  (h_acute : AcuteAngled ⟨![A, B, C], tri⟩)
  -- Triangle ABC is not isosceles (scalene)
  (h_not_iso : dist A B ≠ dist B C ∧ dist B C ≠ dist C A ∧ dist C A ≠ dist A B)
  (I : ℝ²) (hI : I = incenter ⟨![A, B, C], tri⟩)
  (ω : Sphere ℝ²) (hω : ω = circumsphere ⟨![A, B, C], tri⟩)
  -- D, E, F are intersections of angle bisectors with opposite sides
  (D : ℝ²) (hD : D ∈ affineSegment ℝ B C ∩ affineSpan ℝ {A, I})
  (E : ℝ²) (hE : E ∈ affineSegment ℝ C A ∩ affineSpan ℝ {B, I})
  (F : ℝ²) (hF : F ∈ affineSegment ℝ A B ∩ affineSpan ℝ {C, I})
  -- T_A, T_B, T_C are the mixtilinear touch points
  (T_A : ℝ²) (hT_A : IsMixtilinearTouchPoint A B C T_A ω)
  (T_B : ℝ²) (hT_B : IsMixtilinearTouchPoint B C A T_B ω)
  (T_C : ℝ²) (hT_C : IsMixtilinearTouchPoint C A B T_C ω) :
  -- Conclusion: There exist two distinct points X and Y common to the circumcircles
  ∃ X Y : ℝ², X ≠ Y ∧
    Cospherical {A, D, T_A, X} ∧ Cospherical {A, D, T_A, Y} ∧
    Cospherical {B, E, T_B, X} ∧ Cospherical {B, E, T_B, Y} ∧
    Cospherical {C, F, T_C, X} ∧ Cospherical {C, F, T_C, Y} := by   set_option maxRecDepth 10000 in
  set_option hygiene false in
  run_tac
    withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := 1600000000 }) do
      Lean.Elab.Tactic.evalTactic (← `(tactic| (classical
  let S : Affine.Triangle ℝ ℝ² := ⟨![A, B, C], tri⟩
  have hA : A ∈ ω := by
    rw [hω]
    exact S.mem_circumsphere 0
  have hB : B ∈ ω := by
    rw [hω]
    exact S.mem_circumsphere 1
  have hC : C ∈ ω := by
    rw [hω]
    exact S.mem_circumsphere 2
  obtain ⟨cA, hcA_AB, hcA_AC, hcA_T⟩ := hT_A
  have hcA := LeanFlowProofs.PB003.forwardBisectorOfInternalTangency
    A B C T_A tri ω cA hA hB hC hcA_AB hcA_AC hcA_T
  letI : Fact (Module.finrank ℝ ℝ² = 2) := ⟨by simp⟩
  let P := S.touchpoint ∅ 2
  let Q := S.touchpoint ∅ 0
  let U := S.touchpoint ∅ 1
  have htAB : S.insphere.IsTangentAt P (affineSpan ℝ {A, B}) := by
    change S.insphere.IsTangentAt (S.touchpoint ∅ 2)
      (affineSpan ℝ {S.points 0, S.points 1})
    rw [S.affineSpan_pair_eq_orthRadius_insphere (i₁ := 2)
      (by decide) (by decide) (by decide)]
    exact Sphere.isTangentAt_orthRadius_iff_mem.mpr (S.touchpoint_mem_insphere 2)
  have htBC : S.insphere.IsTangentAt Q (affineSpan ℝ {B, C}) := by
    change S.insphere.IsTangentAt (S.touchpoint ∅ 0)
      (affineSpan ℝ {S.points 1, S.points 2})
    rw [S.affineSpan_pair_eq_orthRadius_insphere (i₁ := 0)
      (by decide) (by decide) (by decide)]
    exact Sphere.isTangentAt_orthRadius_iff_mem.mpr (S.touchpoint_mem_insphere 0)
  have htAC : S.insphere.IsTangentAt U (affineSpan ℝ {A, C}) := by
    change S.insphere.IsTangentAt (S.touchpoint ∅ 1)
      (affineSpan ℝ {S.points 0, S.points 2})
    rw [S.affineSpan_pair_eq_orthRadius_insphere (i₁ := 1)
      (by decide) (by decide) (by decide)]
    exact Sphere.isTangentAt_orthRadius_iff_mem.mpr (S.touchpoint_mem_insphere 1)
  have hP : Sbtw ℝ A P B := S.sbtw_touchpoint_empty
    (i₁ := 0) (i₂ := 2) (i₃ := 1) (by decide) (by decide) (by decide)
  have hQ : Sbtw ℝ B Q C := S.sbtw_touchpoint_empty
    (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have hU : Sbtw ℝ A U C := S.sbtw_touchpoint_empty
    (i₁ := 0) (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)
  let x := dist A P
  let y := dist B P
  let z := dist C U
  let r := S.inradius
  have hr : 0 < r := S.inradius_pos
  have hx : 0 < x := dist_pos.mpr hP.left_ne
  have hy : 0 < y := dist_pos.mpr hP.right_ne
  have hz : 0 < z := dist_pos.mpr hU.right_ne
  have hAx : dist A U = x := htAC.dist_eq_of_mem_of_mem htAB
    (left_mem_affineSpan_pair ℝ A C) (left_mem_affineSpan_pair ℝ A B)
  have hBy : dist B Q = y := htBC.dist_eq_of_mem_of_mem htAB
    (left_mem_affineSpan_pair ℝ B C) (right_mem_affineSpan_pair ℝ A B)
  have hCz : dist C Q = z := htBC.dist_eq_of_mem_of_mem htAC
    (right_mem_affineSpan_pair ℝ B C) (right_mem_affineSpan_pair ℝ A C)
  have hAB : dist A B = x + y := by
    simpa [x, y, dist_comm] using hP.wbtw.dist_add_dist.symm
  have hBC : dist B C = y + z := by
    simpa [hBy, hCz, dist_comm] using hQ.wbtw.dist_add_dist.symm
  have hCA : dist C A = z + x := by
    simpa [hAx, dist_comm, add_comm, z] using hU.wbtw.dist_add_dist.symm
  have hAI : ‖A - I‖ ^ 2 = x ^ 2 + r ^ 2 := by
    have h := htAB.dist_sq_eq_of_mem (left_mem_affineSpan_pair ℝ A B)
    simpa [hI, dist_eq_norm, x, r, add_comm] using h
  have hBI : ‖B - I‖ ^ 2 = y ^ 2 + r ^ 2 := by
    have h := htAB.dist_sq_eq_of_mem (right_mem_affineSpan_pair ℝ A B)
    simpa [hI, dist_eq_norm, y, r, add_comm] using h
  have hCI : ‖C - I‖ ^ 2 = z ^ 2 + r ^ 2 := by
    have h := htAC.dist_sq_eq_of_mem (right_mem_affineSpan_pair ℝ A C)
    simpa [hI, dist_eq_norm, z, r, add_comm] using h
  let a := A - I
  let b := B - I
  let c := C - I
  have haa : inner ℝ a a = x ^ 2 + r ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; exact hAI
  have hbb : inner ℝ b b = y ^ 2 + r ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; exact hBI
  have hcc : inner ℝ c c = z ^ 2 + r ^ 2 := by
    rw [real_inner_self_eq_norm_sq]; exact hCI
  have hab : inner ℝ a b = r ^ 2 - x * y := by
    have hd : ‖a - b‖ ^ 2 = (x + y) ^ 2 := by
      simpa [a, b, sub_sub_sub_cancel_right, ← dist_eq_norm] using congrArg (fun t : ℝ => t ^ 2) hAB
    rw [norm_sub_sq_real] at hd
    nlinarith only [hd, hAI, hBI]
  have hbc : inner ℝ b c = r ^ 2 - y * z := by
    have hd : ‖b - c‖ ^ 2 = (y + z) ^ 2 := by
      simpa [b, c, sub_sub_sub_cancel_right, ← dist_eq_norm] using congrArg (fun t : ℝ => t ^ 2) hBC
    rw [norm_sub_sq_real] at hd
    nlinarith only [hd, hBI, hCI]
  have hca : inner ℝ c a = r ^ 2 - z * x := by
    have hd : ‖c - a‖ ^ 2 = (z + x) ^ 2 := by
      simpa [a, c, sub_sub_sub_cancel_right, ← dist_eq_norm] using congrArg (fun t : ℝ => t ^ 2) hCA
    rw [norm_sub_sq_real] at hd
    nlinarith only [hd, hCI, hAI]
  have hgram : inner ℝ a a * inner ℝ b b * inner ℝ c c +
      2 * inner ℝ a b * inner ℝ b c * inner ℝ c a -
      inner ℝ a a * (inner ℝ b c) ^ 2 -
      inner ℝ b b * (inner ℝ c a) ^ 2 -
      inner ℝ c c * (inner ℝ a b) ^ 2 = 0 := by
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  rw [haa, hbb, hcc, hab, hbc, hca] at hgram
  have hrad : r ^ 2 * (x + y + z) = x * y * z := by
    have hh : 4 * x * y * z * (r ^ 2 * (x + y + z) - x * y * z) = 0 := by
      nlinarith only [hgram]
    have hpos : 0 < 4 * x * y * z := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hpos.ne')
  have hxy : x ≠ y := by
    intro h
    apply h_not_iso.2.1
    rw [hBC, hCA, h]
    ring
  have hyz : y ≠ z := by
    intro h
    apply h_not_iso.2.2
    rw [hCA, hAB, h]
    ring
  have hzx : z ≠ x := by
    intro h
    apply h_not_iso.1
    rw [hAB, hBC, h]
    ring
  have hba : inner ℝ b a = r ^ 2 - x * y := (real_inner_comm a b).trans hab
  have hac : inner ℝ a c = r ^ 2 - z * x := (real_inner_comm c a).trans hca
  have hcb : inner ℝ c b = r ^ 2 - y * z := (real_inner_comm b c).trans hbc
  have hbalance : (y + z) • a + (z + x) • b + (x + y) • c = 0 := by
    let w := (y + z) • a + (z + x) • b + (x + y) • c
    have hwa : inner ℝ w a = 0 := by
      simp only [w, inner_add_left, real_inner_smul_left, haa, hba, hca]
      nlinarith only [hrad]
    have hwb : inner ℝ w b = 0 := by
      simp only [w, inner_add_left, real_inner_smul_left, hab, hbb, hcb]
      nlinarith only [hrad]
    have hwc : inner ℝ w c = 0 := by
      simp only [w, inner_add_left, real_inner_smul_left, hac, hbc, hcc]
      nlinarith only [hrad]
    change w = 0
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    change inner ℝ w ((y + z) • a + (z + x) • b + (x + y) • c) = 0
    rw [inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, hwa, hwb, hwc]
    ring
  let o := ω.center - I
  let R := ω.radius
  let k := R ^ 2 - ‖o‖ ^ 2
  let s := x + y + z
  have hs : 0 < s := by dsimp [s]; positivity
  have hR : 0 < R := by
    change 0 < ω.radius
    rw [hω]
    exact S.circumradius_pos
  have hoa : inner ℝ o a = (x ^ 2 + r ^ 2 - k) / 2 := by
    have hd : ‖o - a‖ ^ 2 = R ^ 2 := by
      simpa [o, a, R, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using
        congrArg (fun t : ℝ => t ^ 2) (show dist A ω.center = ω.radius from hA)
    rw [norm_sub_sq_real] at hd
    dsimp [k]
    nlinarith only [hd, hAI]
  have hob : inner ℝ o b = (y ^ 2 + r ^ 2 - k) / 2 := by
    have hd : ‖o - b‖ ^ 2 = R ^ 2 := by
      simpa [o, b, R, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using
        congrArg (fun t : ℝ => t ^ 2) (show dist B ω.center = ω.radius from hB)
    rw [norm_sub_sq_real] at hd
    dsimp [k]
    nlinarith only [hd, hBI]
  have hoc : inner ℝ o c = (z ^ 2 + r ^ 2 - k) / 2 := by
    have hd : ‖o - c‖ ^ 2 = R ^ 2 := by
      simpa [o, c, R, sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm] using
        congrArg (fun t : ℝ => t ^ 2) (show dist C ω.center = ω.radius from hC)
    rw [norm_sub_sq_real] at hd
    dsimp [k]
    nlinarith only [hd, hCI]
  have hk : 2 * s * k = (y + z) * (z + x) * (x + y) := by
    have hh := congrArg (fun v => inner ℝ o v) hbalance
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right, hoa, hob, hoc] at hh
    dsimp [s]
    nlinarith only [hh, hrad]
  have hkpos : 0 < k := by
    have hp : 0 < (y + z) * (z + x) * (x + y) := by positivity
    nlinarith only [hk, hs, hp]
  have hmetric : ‖o‖ ^ 2 * (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2) =
      inner ℝ b b * (inner ℝ o a) ^ 2 + inner ℝ a a * (inner ℝ o b) ^ 2 -
        2 * inner ℝ a b * inner ℝ o a * inner ℝ o b := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  have haux : 2 * k * (x * y - r ^ 2) = (x ^ 2 + r ^ 2) * (y ^ 2 + r ^ 2) := by
    have hk' : k = (y + z) * (z + x) * (x + y) / (2 * s) := by
      apply (eq_div_iff (by positivity : 2 * s ≠ 0)).mpr
      nlinarith only [hk]
    have hr' : r ^ 2 = x * y * z / s := (eq_div_iff hs.ne').mpr hrad
    rw [hk', hr']
    dsimp [s]
    field_simp
    ring
  have hkR : k = 2 * R * r := by
    rw [haa, hbb, hab, hoa, hob] at hmetric
    have hh : (x + y) ^ 2 * (k ^ 2 - 4 * r ^ 2 * R ^ 2) = 0 := by
      dsimp [k] at hmetric haux ⊢
      linear_combination -4 * hmetric + (x + y) ^ 2 * haux
    have heq : k ^ 2 = (2 * R * r) ^ 2 := by
      have hp : (x + y) ^ 2 ≠ 0 := by positivity
      have he := (mul_eq_zero.mp hh).resolve_left hp
      nlinarith only [he]
    exact (sq_eq_sq₀ hkpos.le (by positivity)).mp heq
  have hcircum : 4 * R * r * (x + y + z) = (y + z) * (z + x) * (x + y) := by
    rw [hkR] at hk
    dsimp [s] at hk
    nlinarith only [hk]
  have heuler : ‖o‖ ^ 2 = R * (R - 2 * r) := by
    dsimp [k] at hkR
    nlinarith only [hkR]
  have hscalar := LeanFlowProofs.PB003.scalarData x y z r R hx hy hz hr hxy hyz hzx hrad hcircum
  have hinter : ∀ (A' B' C' D' : ℝ²) (x' y' z' : ℝ),
      0 < x' → 0 < y' → 0 < z' →
      r ^ 2 * (x' + y' + z') = x' * y' * z' →
      inner ℝ (B' - I) (A' - I) = r ^ 2 - x' * y' →
      inner ℝ (C' - I) (A' - I) = r ^ 2 - z' * x' →
      inner ℝ (B' - I) (B' - I) = y' ^ 2 + r ^ 2 →
      inner ℝ (C' - I) (C' - I) = z' ^ 2 + r ^ 2 →
      inner ℝ (B' - I) (C' - I) = r ^ 2 - y' * z' →
      D' ∈ affineSegment ℝ B' C' → D' ∈ affineSpan ℝ {A', I} →
      D' - I = -((y' + z') / (2 * x' + y' + z')) • (A' - I) := by
    intro A' B' C' D' x' y' z' hx' hy' hz' hr' hba' hca' hbb' hcc' hbc' hdseg hdline
    obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hdline
    have hdu : D' - I = (1 - u) • (A' - I) := by
      rw [← hu, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
      abel
    obtain ⟨t, ht, hdt⟩ := hdseg
    have hdt' : D' - I = (1 - t) • (B' - I) + t • (C' - I) := by
      rw [← hdt, AffineMap.lineMap_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]
      module
    let w := z' • (B' - I) + y' • (C' - I)
    have hcb' : inner ℝ (C' - I) (B' - I) = r ^ 2 - y' * z' :=
      (real_inner_comm (B' - I) (C' - I)).trans hbc'
    have hwa : inner ℝ w (A' - I) = -(r ^ 2 * (2 * x' + y' + z')) := by
      simp only [w, inner_add_left, real_inner_smul_left, hba', hca']
      nlinarith only [hr']
    have hwb : inner ℝ w (B' - I) = r ^ 2 * (y' + z') := by
      simp only [w, inner_add_left, real_inner_smul_left, hbb', hcb']; ring
    have hwc : inner ℝ w (C' - I) = r ^ 2 * (y' + z') := by
      simp only [w, inner_add_left, real_inner_smul_left, hbc', hcc']; ring
    have hh := congrArg (fun v => inner ℝ w v) (hdu.symm.trans hdt')
    simp only [inner_add_right, real_inner_smul_right, hwa, hwb, hwc] at hh
    have hh2 : (1 - u) * (2 * x' + y' + z') = -(y' + z') := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
      nlinarith only [hh]
    have hv : 1 - u = -((y' + z') / (2 * x' + y' + z')) := by
      rw [← neg_div]
      exact (eq_div_iff (by positivity : 2 * x' + y' + z' ≠ 0)).mpr hh2
    rw [hdu, hv]
  have hdcoord : D - I = -((y + z) / (2 * x + y + z)) • a :=
    hinter A B C D x y z hx hy hz hrad hba hca hbb hcc hbc hD.1 hD.2
  have hecoord : E - I = -((z + x) / (2 * y + z + x)) • b := by
    apply hinter B C A E y z x hy hz hx
    · nlinarith only [hrad]
    · simpa [mul_comm] using hcb
    · simpa [mul_comm] using hab
    · exact hcc
    · exact haa
    · exact hca
    · exact hE.1
    · exact hE.2
  have hfcoord : F - I = -((x + y) / (2 * z + x + y)) • c := by
    apply hinter C A B F z x y hz hx hy
    · nlinarith only [hrad]
    · simpa [mul_comm] using hac
    · simpa [mul_comm] using hbc
    · exact haa
    · exact hbb
    · exact hab
    · exact hF.1
    · exact hF.2
  have hscale : ∀ (A' B' : ℝ²) (c' : Sphere ℝ²) (u : ℝ),
      0 ≤ u → c'.IsTangent (affineSpan ℝ {A', B'}) →
      S.insphere.IsTangent (affineSpan ℝ {A', B'}) →
      c'.center = A' + u • (I - A') → c'.radius = u * r := by
    intro A' B' c' u hu ht hi hc
    let L := affineSpan ℝ ({A', B'} : Set ℝ²)
    let f := orthogonalProjection L
    have hfa : (f A' : ℝ²) = A' :=
      orthogonalProjection_eq_self_iff.mpr (left_mem_affineSpan_pair ℝ A' B')
    have hfi : dist I (f I) = r := by
      have hh := Sphere.dist_orthogonalProjection_eq_radius_iff_isTangent.mpr hi
      simpa [f, L, S, ← hI, r] using hh
    have hfc : dist c'.center (f c'.center) = c'.radius :=
      Sphere.dist_orthogonalProjection_eq_radius_iff_isTangent.mpr ht
    have hmap := f.toAffineMap.apply_lineMap A' I u
    have hp : (f c'.center : ℝ²) = A' + u • ((f I : ℝ²) - A') := by
      have hh := congrArg (fun p : L => (p : ℝ²)) hmap
      simpa [AffineMap.lineMap_apply, hc, add_comm, hfa] using hh
    rw [← hfc, dist_eq_norm, hp, hc]
    have he : A' + u • (I - A') - (A' + u • ((f I : ℝ²) - A')) =
        u • (I - (f I : ℝ²)) := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu, ← dist_eq_norm, hfi]
  have hdir : ∀ (A' B' C' : ℝ²) (x' y' z' : ℝ),
      0 < x' → 0 < y' → 0 < z' →
      dist A' B' = x' + y' → dist C' A' = z' + x' →
      (y' + z') • (A' - I) + (z' + x') • (B' - I) +
        (x' + y') • (C' - I) = 0 →
      ‖B' - A'‖⁻¹ • (B' - A') + ‖C' - A'‖⁻¹ • (C' - A') =
        (2 * (x' + y' + z') / ((x' + y') * (z' + x'))) • (I - A') := by
    intro A' B' C' x' y' z' hx' hy' hz' hab' hca' hb'
    rw [← dist_eq_norm, dist_comm B' A', hab', ← dist_eq_norm, hca']
    ext i
    have hh := congrArg (fun v : ℝ² => v i) hb'
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, PiLp.zero_apply,
      smul_eq_mul] at hh ⊢
    field_simp [ne_of_gt (add_pos hx' hy'), ne_of_gt (add_pos hz' hx')]
    linear_combination hh
  have htriB : AffineIndependent ℝ ![B, C, A] := tri.comm_left.comm_right
  have htriC : AffineIndependent ℝ ![C, A, B] := tri.comm_right.comm_left
  have htouch : ∀ (A' B' C' T' : ℝ²) (x' y' z' : ℝ),
      0 < x' → 0 < y' → 0 < z' →
      AffineIndependent ℝ ![A', B', C'] →
      A' ∈ ω → B' ∈ ω → C' ∈ ω →
      dist A' B' = x' + y' → dist C' A' = z' + x' →
      (y' + z') • (A' - I) + (z' + x') • (B' - I) +
        (x' + y') • (C' - I) = 0 →
      S.insphere.IsTangent (affineSpan ℝ {A', B'}) →
      inner ℝ (A' - I) (A' - I) = x' ^ 2 + r ^ 2 →
      inner ℝ o (A' - I) = (x' ^ 2 + r ^ 2 - 2 * R * r) / 2 →
      r * (1 + r ^ 2 / x' ^ 2) < R →
      IsMixtilinearTouchPoint A' B' C' T' ω →
      ∀ (v : ℝ²) (m : ℝ), inner ℝ v (A' - I) = -2 * R * r * m →
      inner ℝ v o = 2 * R * (R - r) * m →
      inner ℝ v (T' - I) = -2 * R * r * m := by
    intro A' B' C' T' x' y' z' hx' hy' hz' htri' hA' hB' hC' hab' hca' hb' hi' haa' hoa' hbound' ht' v m hva hvo
    obtain ⟨c', hcAB, hcAC, hcT⟩ := ht'
    rcases LeanFlowProofs.PB003.forwardBisectorOfInternalTangency
      A' B' C' T' htri' ω c' hA' hB' hC' hcAB hcAC hcT with hzero | ⟨hpos, t, ht, hc⟩
    · simpa [hzero.2.2] using hva
    rw [hdir A' B' C' x' y' z' hx' hy' hz' hab' hca' hb', smul_smul] at hc
    let u := t * (2 * (x' + y' + z') / ((x' + y') * (z' + x')))
    have hu : 0 < u := by dsimp [u]; positivity
    have hradius : c'.radius = u * r := hscale A' B' c' u hu.le hcAB hi' hc
    have hcenter : c'.center - I = (1 - u) • (A' - I) := by rw [hc]; module
    have hd := hcT.isIntTangent.dist_center
    have hn : ‖(1 - u) • (A' - I) - o‖ ^ 2 = (R - u * r) ^ 2 := by
      have he : c'.center - ω.center = (1 - u) • (A' - I) - o := by rw [← hcenter]; dsimp [o]; abel
      rw [dist_eq_norm, he, hradius] at hd
      exact congrArg (fun q : ℝ => q ^ 2) hd
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      ← real_inner_self_eq_norm_sq, haa', real_inner_smul_left,
      real_inner_comm o (A' - I), hoa', heuler] at hn
    have huval : u * x' ^ 2 = x' ^ 2 + r ^ 2 := by
      have hh : u * (u * x' ^ 2 - (x' ^ 2 + r ^ 2)) = 0 := by nlinarith only [hn]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hu.ne')
    have hueq : u = 1 + r ^ 2 / x' ^ 2 := by
      apply (eq_div_iff (ne_of_gt (sq_pos_of_pos hx'))).2 at huval
      rw [huval]; field_simp
    have hproper : R - u * r ≠ 0 := by rw [hueq]; nlinarith only [hbound']
    obtain ⟨q, hq, heq⟩ := hcT.wbtw
    have hcq : c'.center = q • (T' - ω.center) + ω.center := by
      simpa [AffineMap.lineMap_apply] using heq.symm
    have hdistq : dist c'.center ω.center = q * R := by
      rw [hcq, dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hq.1, ← dist_eq_norm]
      exact congrArg (q * ·) hcT.mem_right
    have hqr : q * R = R - u * r := by rw [← hdistq]; exact hd.trans (by rw [hradius])
    have hvq := congrArg (fun w : ℝ² => inner ℝ v (w - I)) hcq
    have he : q • (T' - ω.center) + ω.center - I = q • (T' - I) + (1 - q) • o := by dsimp [o]; module
    rw [hcenter, he, real_inner_smul_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, hva, hvo] at hvq
    have hqne : q ≠ 0 := by intro hh; apply hproper; simpa [hh] using hqr.symm
    apply (mul_left_cancel₀ hqne)
    have hRne : R ≠ 0 := hR.ne'
    apply (mul_left_cancel₀ hRne)
    linear_combination -R * hvq + 2 * R ^ 2 * m * hqr
  let det : ℝ² → ℝ² → ℝ := fun u v => u 0 * v 1 - u 1 * v 0
  let rot : ℝ² → ℝ² := fun u => !₂[-u 1, u 0]
  have hdet_sq : ∀ u v : ℝ², det u v ^ 2 =
      inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
    intro u v
    simp only [det, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  have hdet_dot : ∀ u v w : ℝ², det u v * det v w =
      inner ℝ u v * inner ℝ v w - inner ℝ v v * inner ℝ u w := by
    intro u v w
    simp only [det, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
    ring
  have hdet_ab : det a b ^ 2 = r ^ 2 * (x + y) ^ 2 := by
    rw [hdet_sq, haa, hbb, hab]; ring
  have hdne : det a b ≠ 0 := by
    intro hd
    have hh := mul_pos (sq_pos_of_pos hr) (sq_pos_of_pos (add_pos hx hy))
    rw [hd] at hdet_ab
    nlinarith only [hh, hdet_ab]
  have hdet_gen : ∀ (a' b' : ℝ²) (x' y' z' : ℝ),
      0 < x' → 0 < y' → 0 < z' →
      r ^ 2 * (x' + y' + z') = x' * y' * z' →
      4 * R * r * (x' + y' + z') = (y' + z') * (z' + x') * (x' + y') →
      inner ℝ a' a' = x' ^ 2 + r ^ 2 →
      inner ℝ a' b' = r ^ 2 - x' * y' →
      inner ℝ o a' = (x' ^ 2 + r ^ 2 - 2 * R * r) / 2 →
      inner ℝ o b' = (y' ^ 2 + r ^ 2 - 2 * R * r) / 2 →
      det o a' * det a' b' = R * r * x' * (z' - y') * (x' + y') / (y' + z') := by
    intro a' b' x' y' z' hx' hy' hz' hrad' hcir' haa' hab' hoa' hob'
    rw [hdet_dot, hoa', hab', haa', hob']
    field_simp [ne_of_gt (add_pos hy' hz')]
    apply (mul_left_cancel₀ (ne_of_gt (show 0 < x' + y' + z' by positivity)))
    linear_combination -(x' + y') * y' * (y' + z') * hrad' + x' * y' * (x' + y') * hcir'
  rw [hkR] at hoa hob hoc
  have hbalB : (z + x) • b + (x + y) • c + (y + z) • a = 0 := by
    simpa only [add_comm, add_left_comm, add_assoc] using hbalance
  have hbalC : (x + y) • c + (y + z) • a + (z + x) • b = 0 := by
    simpa only [add_comm, add_left_comm, add_assoc] using hbalance
  have hdb : det b c * (x + y) = det a b * (y + z) := by
    have hh := congrArg (fun v : ℝ² => det b v) hbalance
    dsimp [det] at hh ⊢
    nlinarith only [hh]
  have hdc : det c a * (x + y) = det a b * (z + x) := by
    have hh := congrArg (fun v : ℝ² => det a v) hbalance
    dsimp [det] at hh ⊢
    nlinarith only [hh]
  let δ := det a b / (x + y)
  have hδ : δ ≠ 0 := div_ne_zero hdne (ne_of_gt (add_pos hx hy))
  have hdab : det a b = δ * (x + y) := by dsimp [δ]; field_simp
  have hdbc : det b c = δ * (y + z) := by
    apply (mul_right_cancel₀ (ne_of_gt (add_pos hx hy)))
    rw [hdb, hdab]; ring
  have hdca : det c a = δ * (z + x) := by
    apply (mul_right_cancel₀ (ne_of_gt (add_pos hx hy)))
    rw [hdc, hdab]; ring
  have hda := hdet_gen a b x y z hx hy hz hrad hcircum haa hab hoa hob
  have hdb' := hdet_gen b c y z x hy hz hx (by nlinarith only [hrad])
    (by nlinarith only [hcircum]) hbb hbc hob hoc
  have hdc' := hdet_gen c a z x y hz hx hy (by nlinarith only [hrad])
    (by nlinarith only [hcircum]) hcc hca hoc hoa
  rw [hdab] at hda
  rw [hdbc] at hdb'
  rw [hdca] at hdc'
  have hda' : det o a = R * r * x * (z - y) / ((y + z) * δ) := by
    field_simp [hδ, ne_of_gt (add_pos hy hz)] at hda ⊢
    nlinarith only [hda]
  have hdb'' : det o b = R * r * y * (x - z) / ((z + x) * δ) := by
    field_simp [hδ, ne_of_gt (add_pos hz hx)] at hdb' ⊢
    nlinarith only [hdb']
  have hdc'' : det o c = R * r * z * (y - x) / ((x + y) * δ) := by
    field_simp [hδ, ne_of_gt (add_pos hx hy)] at hdc' ⊢
    nlinarith only [hdc']
  let p := x * y * z
  let q := x * y + y * z + z * x
  let N : ℝ → ℝ := fun t => (s * q + 3 * p) * p - (s * q - 5 * p) * s * t ^ 2
  let m : ℝ → ℝ := fun t => (s - t) / (s + t)
  let n : ℝ → ℝ → ℝ → ℝ := fun t u v => (s - t) ^ 2 * N t / ((s + t) * t * (v - u))
  have hradp : r ^ 2 * s = p := hrad
  have hcircp : 4 * R * r * s = s * q - p := by
    dsimp [s, q, p]; linear_combination hcircum
  have hN : ∀ t : ℝ, N t = 4 * r * s ^ 2 * ((R + r) * r ^ 2 - (R - r) * t ^ 2) := by
    intro t; dsimp [N]
    linear_combination -(s * q + 3 * p + 4 * s * r ^ 2 + 4 * s * t ^ 2) * hradp -
      s * (r ^ 2 - t ^ 2) * hcircp
  have hRm : R - 2 * r ≠ 0 := ne_of_gt (sub_pos.mpr hscalar.1)
  let α := 2 * (R - r) / (R - 2 * r)
  let β := δ / (4 * R * r ^ 2 * (R - 2 * r) * s ^ 2)
  let vv : ℝ → ℝ → ℝ → ℝ² := fun t u v => (α * m t) • o + (β * n t u v) • rot o
  have hroto : inner ℝ (rot o) o = 0 := by
    simp [rot, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]; ring
  have hrot : ∀ w : ℝ², inner ℝ (rot o) w = det o w := by
    intro w; simp [rot, det, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply]; ring
  have hvvo : ∀ t u v : ℝ, inner ℝ (vv t u v) o = 2 * R * (R - r) * m t := by
    intro t u v
    simp only [vv, inner_add_left, real_inner_smul_left, hroto, mul_zero, add_zero,
      real_inner_self_eq_norm_sq, heuler]
    dsimp [α]; field_simp [hRm]
  have hvva : ∀ (w : ℝ²) (t u v : ℝ),
      0 < t → 0 < u → 0 < v → v ≠ u → s = t + u + v →
      inner ℝ o w = (t ^ 2 + r ^ 2 - 2 * R * r) / 2 →
      det o w = R * r * t * (v - u) / ((u + v) * δ) →
      inner ℝ (vv t u v) w = -2 * R * r * m t := by
    intro w t u v ht hu hv hvu hs' how hdw
    simp only [vv, inner_add_left, real_inner_smul_left, how, hrot, hdw]
    dsimp [α, β, n, m]
    rw [hN]
    rw [hs']
    field_simp [hRm, hδ, hR.ne', hr.ne', ht.ne', sub_ne_zero.mpr hvu,
      ne_of_gt (add_pos hu hv), ne_of_gt (show 0 < t + u + v by positivity),
      ne_of_gt (show 0 < t + u + v + t by positivity)]
    <;> ring
  have hvA := hvva a x y z hx hy hz hyz.symm rfl hoa hda'
  have hvB := hvva b y z x hy hz hx hzx.symm (by dsimp [s]; ring) hob hdb''
  have hvC := hvva c z x y hz hx hy hxy.symm (by dsimp [s]; ring) hoc hdc''
  have hmn : (m y - m x) * (n z x y - n x y z) =
      (m z - m x) * (n y z x - n x y z) :=
    LeanFlowProofs.PB003.cyclicCoefficientCollinearity x y z hx hy hz hxy hyz hzx
  have hmne : m y - m x ≠ 0 := sub_ne_zero.mpr hscalar.2.2.symm
  let τ := (m z - m x) / (m y - m x)
  have hτm : m z - m x = τ * (m y - m x) := by dsimp [τ]; field_simp
  have hτn : n z x y - n x y z = τ * (n y z x - n x y z) := by
    dsimp [τ]; rw [div_mul_eq_mul_div]; apply (eq_div_iff hmne).mpr
    nlinarith only [hmn]
  have hvcol : vv z x y - vv x y z = τ • (vv y z x - vv x y z) := by
    dsimp only [vv]
    rw [add_sub_add_comm, ← sub_smul, ← sub_smul, add_sub_add_comm,
      ← sub_smul, ← sub_smul, smul_add, smul_smul, smul_smul]
    congr 1 <;> congr 1
    · linear_combination α * hτm
    · linear_combination β * hτn
  have hRr : 0 < R - r := by linarith only [hscalar.1, hr]
  have hvne : vv y z x ≠ vv x y z := by
    intro hh
    have hh' := congrArg (fun w => inner ℝ w o) hh
    rw [hvvo, hvvo] at hh'
    apply hmne
    nlinarith only [hh', mul_pos hR hRr]
  let ell : Fin 3 → ℝ² := ![vv x y z - 2 • o, vv y z x - 2 • o, vv z x y - 2 • o]
  let kk : Fin 3 → ℝ := ![-2 * R * r + 2 * R * r * m x,
    -2 * R * r + 2 * R * r * m y, -2 * R * r + 2 * R * r * m z]
  let J : ℝ² := (-r / (R - r)) • o
  have htwo : ∀ w : ℝ², inner ℝ (2 • o) w = 2 * inner ℝ o w := by
    intro w; simp only [two_smul, inner_add_left, two_mul]
  have hJ : ∀ t u v : ℝ,
      ‖J‖ ^ 2 + inner ℝ (vv t u v - 2 • o) J +
        (-2 * R * r + 2 * R * r * m t) = -(R * r / (R - r)) ^ 2 := by
    intro t u v
    simp only [J, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_sub_left, real_inner_smul_left, real_inner_smul_right, htwo,
      real_inner_self_eq_norm_sq, hvvo, heuler]
    field_simp [hRr.ne'] <;> ring
  have hneg : -(R * r / (R - r)) ^ 2 < 0 := by
    have hp : 0 < R * r / (R - r) := div_pos (mul_pos hR hr) hRr
    nlinarith only [sq_pos_of_pos hp]
  obtain ⟨X, Y, hXY, hroots, hspheres⟩ :=
    LeanFlowProofs.PB003.negativePowerCoaxialSecant ell kk J
      (by change vv y z x - 2 • o ≠ vv x y z - 2 • o; exact fun hh => hvne (sub_left_injective hh))
      (by refine ⟨τ, ?_⟩; change (vv z x y - 2 • o) - (vv x y z - 2 • o) =
          τ • ((vv y z x - 2 • o) - (vv x y z - 2 • o))
          simpa only [sub_sub_sub_cancel_right] using hvcol)
      (by intro i; fin_cases i
          · exact (hJ x y z).trans (hJ x y z).symm
          · exact (hJ y z x).trans (hJ x y z).symm
          · exact (hJ z x y).trans (hJ x y z).symm)
      (by simpa only [ell, kk, Matrix.cons_val_zero, hJ] using hneg)
  have hzero : ∀ (P' : ℝ²) (w : ℝ²) (t : ℝ), P' ∈ ω →
      inner ℝ w (P' - I) = -2 * R * r * m t →
      ‖P' - I‖ ^ 2 + inner ℝ (w - 2 • o) (P' - I) +
        (-2 * R * r + 2 * R * r * m t) = 0 := by
    intro P' w t hP' hw
    have hh : ‖(P' - I) - o‖ ^ 2 = R ^ 2 := by
      have hh : dist P' ω.center = R := hP'
      simpa only [o, sub_sub_sub_cancel_right, ← dist_eq_norm] using congrArg (fun t : ℝ => t ^ 2) hh
    rw [norm_sub_sq_real, heuler] at hh
    simp only [inner_sub_left, real_inner_smul_left, htwo, hw]
    rw [real_inner_comm (P' - I) o]
    nlinarith only [hh]
  have hTA := htouch A B C T_A x y z hx hy hz tri hA hB hC hAB hCA hbalance
    htAB.isTangent haa hoa (hscalar.2.1 x (by simp)).1 ⟨cA, hcA_AB, hcA_AC, hcA_T⟩
    (vv x y z) (m x) hvA (hvvo x y z)
  have hTB := htouch B C A T_B y z x hy hz hx htriB hB hC hA hBC hAB hbalB
    htBC.isTangent hbb hob (hscalar.2.1 y (by simp)).1 hT_B
    (vv y z x) (m y) hvB (hvvo y z x)
  have hTC := htouch C A B T_C z x y hz hx hy htriC hC hA hB hCA hBC hbalC
    (by simpa only [Set.pair_comm] using htAC.isTangent) hcc hoc
    (hscalar.2.1 z (by simp)).1 hT_C (vv z x y) (m z) hvC (hvvo z x y)
  have hTAω : T_A ∈ ω := hcA_T.mem_right
  have hTBω : T_B ∈ ω := by obtain ⟨_, _, _, hh⟩ := hT_B; exact hh.mem_right
  have hTCω : T_C ∈ ω := by obtain ⟨_, _, _, hh⟩ := hT_C; exact hh.mem_right
  have hdzero : ∀ (w v : ℝ²) (t : ℝ),
      inner ℝ w w = t ^ 2 + r ^ 2 →
      inner ℝ o w = (t ^ 2 + r ^ 2 - 2 * R * r) / 2 →
      inner ℝ v w = -2 * R * r * m t →
      m t * (t ^ 2 + r ^ 2) = 2 * R * r * (1 - m t) →
      ‖(-m t) • w‖ ^ 2 + inner ℝ (v - 2 • o) ((-m t) • w) +
        (-2 * R * r + 2 * R * r * m t) = 0 := by
    intro w v t hww how hvw hm
    rw [← real_inner_self_eq_norm_sq]
    simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, htwo, hww, how, hvw]
    linear_combination (m t + 1) * hm
  have hd : D - I = (-m x) • a := by
    rw [hdcoord]; congr 2; dsimp [m, s]; congr 1 <;> ring
  have he : E - I = (-m y) • b := by
    rw [hecoord]; congr 2; dsimp [m, s]; congr 1 <;> ring
  have hf : F - I = (-m z) • c := by
    rw [hfcoord]; congr 2; dsimp [m, s]; congr 1 <;> ring
  have hd0 := hdzero a (vv x y z) x haa hoa hvA (hscalar.2.1 x (by simp)).2
  have he0 := hdzero b (vv y z x) y hbb hob hvB (hscalar.2.1 y (by simp)).2
  have hf0 := hdzero c (vv z x y) z hcc hoc hvC (hscalar.2.1 z (by simp)).2
  have hfinish : ∀ (i : Fin 3) (A' D' T' : ℝ²),
      ‖A' - I‖ ^ 2 + inner ℝ (ell i) (A' - I) + kk i = 0 →
      ‖D' - I‖ ^ 2 + inner ℝ (ell i) (D' - I) + kk i = 0 →
      ‖T' - I‖ ^ 2 + inner ℝ (ell i) (T' - I) + kk i = 0 →
      Cospherical {A', D', T', X + I} ∧ Cospherical {A', D', T', Y + I} := by
    intro i A' D' T' ha hd ht
    obtain ⟨O', r', hs'⟩ := hspheres i
    have hdist : ∀ P' : ℝ²,
        ‖P' - I‖ ^ 2 + inner ℝ (ell i) (P' - I) + kk i = 0 →
        dist P' (O' + I) = r' := by
      intro P' hp
      have hh := hs' (P' - I) hp
      simpa only [dist_eq_norm, sub_sub, add_comm I O'] using hh
    constructor
    · refine ⟨O' + I, r', ?_⟩
      intro P' hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hdist _ ha
      · exact hdist _ hd
      · exact hdist _ ht
      · exact hdist _ (by simpa only [add_sub_cancel_right] using (hroots i).1)
    · refine ⟨O' + I, r', ?_⟩
      intro P' hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact hdist _ ha
      · exact hdist _ hd
      · exact hdist _ ht
      · exact hdist _ (by simpa only [add_sub_cancel_right] using (hroots i).2)
  have hfinalA := hfinish 0 A D T_A (hzero A (vv x y z) x hA hvA)
    (by change ‖D - I‖ ^ 2 + inner ℝ (vv x y z - 2 • o) (D - I) +
          (-2 * R * r + 2 * R * r * m x) = 0; rw [hd]; exact hd0)
    (hzero T_A (vv x y z) x hTAω hTA)
  have hfinalB := hfinish 1 B E T_B (hzero B (vv y z x) y hB hvB)
    (by change ‖E - I‖ ^ 2 + inner ℝ (vv y z x - 2 • o) (E - I) +
          (-2 * R * r + 2 * R * r * m y) = 0; rw [he]; exact he0)
    (hzero T_B (vv y z x) y hTBω hTB)
  have hfinalC := hfinish 2 C F T_C (hzero C (vv z x y) z hC hvC)
    (by change ‖F - I‖ ^ 2 + inner ℝ (vv z x y - 2 • o) (F - I) +
          (-2 * R * r + 2 * R * r * m z) = 0; rw [hf]; exact hf0)
    (hzero T_C (vv z x y) z hTCω hTC)
  exact ⟨X + I, Y + I, fun hh => hXY (add_right_cancel hh),
    hfinalA.1, hfinalA.2, hfinalB.1, hfinalB.2, hfinalC.1, hfinalC.2⟩)))

