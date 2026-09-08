import LeanFlowProofs.PBAdvanced010CosphericalCoordinates
import LeanFlowProofs.PBAdvanced010EqualPower
import LeanFlowProofs.PBAdvanced010EulerParameters
import LeanFlowProofs.PBAdvanced010Frame
import LeanFlowProofs.PBAdvanced010RadicalAxis
import LeanFlowProofs.PBAdvanced010SecantLocus
import Mathlib

/-
Let $O$ and $G$ be the circumcenter and centroid of a non-isosceles triangle $ABC$, respectively. Let $H$ be the foot of the perpendicular from $A$ to $BC$, and let $M$ be the midpoint of $BC$. For a point $X$ on the line $OG$, not lying on any of the side lines $AB$, $BC$, $CA$, let the line $BX$ intersect $AC$ at $P$, and let the line $CX$ intersect $AB$ at $Q$. Let $H_1$ be the foot of the perpendicular from $P$ to the line $AB$, and let $K$ be the reflection of $A$ about $H_1$, with $K \neq Q$. Let $T$ be the second intersection of the circumcircle of triangle $KPQ$ and the circumcircle of triangle $PHM$, assuming the two circumcircles are distinct. Prove that as $X$ moves along the line $OG$, $T$ moves along a fixed circle.
-/
open Affine.Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem PBAdvanced010
    -- a triangle ABC
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    -- ABC is non-isosceles
    (n_isosceles : [dist A B, dist A C, dist B C].Nodup )
    (O : ℝ²) (hO : O = circumcenter ⟨![A, B, C], tri⟩) -- O is the circumcenter
    (G : ℝ²) (hG : G = Finset.centroid ℝ .univ ![A, B, C]) -- G is the centroid
    (H : ℝ²) (hH : H = altitudeFoot ⟨![A, B, C], tri⟩ 0) -- H is the foot from A
    (M : ℝ²) (hM : M = midpoint ℝ B C) : -- $M$ is the midpoint of $B C$
    -- There is a sphere ω independent of the point `X`
    ∃ ω : Sphere ℝ²,
    -- For a point $X$ on the line $OG$, not on any side line,
    ∀ (X : ℝ²) (hX : Collinear ℝ {X, O, G} ∧ X ∉ (affineSpan ℝ {A, B} : Set ℝ²) ∪ (affineSpan ℝ {A, C} : Set ℝ²) ∪ (affineSpan ℝ {B, C} : Set ℝ²))
    -- let the line $BX$ intersect $AC$ at $P$,
    (P : ℝ²) (hP : Collinear ℝ {P, B, X} ∧ Collinear ℝ {P, A, C})
    -- let the line $CX$ intersect $AB$ at $Q$.
    (Q : ℝ²) (hQ : Collinear ℝ {Q, C, X} ∧ Collinear ℝ {Q, A, B})
    -- Let $H_1$ be the foot of the perpendicular from $P$ to the line $AB$,
    (H₁ : ℝ²) (hH₁ : H₁ = orthogonalProjection (affineSpan ℝ {A, B}) P)
    -- let $K$ be the reflection of $A$ about $H_1$.
    (K : ℝ²) (hK : K = reflection (affineSpan ℝ {H₁}) A)
    -- K ≠ Q (non-degeneracy: prevents 3-point trivial cosphericality)
    (hK_ne_Q : K ≠ Q)
    -- The two circumcircles are distinct (non-degeneracy: prevents coincidence at X = G)
    (hCircles_ne : ¬ Cospherical ({K, P, Q, H, M} : Set ℝ²))
    -- Let $T$ be the second intersection of the circumcircle of triangle $KPQ$ and the circumcircle of triangle $PHM$.
    (T : ℝ²) (hT : T ≠ P ∧ Cospherical {T, K, P, Q} ∧ Cospherical {T, P, H, M}),
    -- Prove that as $X$ moves along the line $OG$, $T$ moves along a fixed circle.
    T ∈ ω := by set_option maxHeartbeats 5000000 in
  have hne : dist A B ≠ dist A C := by
    have hn := n_isosceles
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or] at hn
    exact hn.1.1
  obtain ⟨f, ρ, a, b, hρ, ha, hb, hA0, hA1, hB0, hB1, hC0, hC1, hscale⟩ :=
    LeanFlowProofs.PBAdvanced010.normalizedFrame A B C tri hne
  have hlm (U V : ℝ²) (t : ℝ) (i : Fin 2) :
      (f (AffineMap.lineMap U V t)) i = (f U) i + t * ((f V) i - (f U) i) := by
    rw [show f (AffineMap.lineMap U V t) = AffineMap.lineMap (f U) (f V) t from
      f.toAffineMap.apply_lineMap U V t]
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
  have hdist (U V : ℝ²) :
      ((f U) 0 - (f V) 0)^2 + ((f U) 1 - (f V) 1)^2 = ρ^2 * dist U V ^2 := by
    rw [← mul_pow, ← hscale, dist_eq_norm, EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have hdet (U V Z : ℝ²) (hc : Collinear ℝ {Z,U,V}) :
      ((f Z) 0 - (f U) 0) * ((f V) 1 - (f U) 1) -
      ((f Z) 1 - (f U) 1) * ((f V) 0 - (f U) 0) = 0 := by
    by_cases huv : U = V
    · simp [huv]
    obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
      (hc.mem_affineSpan_of_mem_of_ne (p₃ := Z) (by simp) (by simp) (by simp) huv)
    rw [← ht, hlm, hlm]
    ring
  have hM0 : (f M) 0 = 0 := by
    rw [hM, f.map_midpoint, midpoint_eq_smul_add]
    simp [hB0, hC0]
  have hM1 : (f M) 1 = 0 := by
    rw [hM, f.map_midpoint, midpoint_eq_smul_add]
    simp [hB1, hC1]
  have hdAB : dist A O = dist B O := by
    rw [hO]
    exact (dist_circumcenter_eq_circumradius ⟨![A,B,C],tri⟩ 0).trans
      (dist_circumcenter_eq_circumradius ⟨![A,B,C],tri⟩ 1).symm
  have hdBC : dist B O = dist C O := by
    rw [hO]
    exact (dist_circumcenter_eq_circumradius ⟨![A,B,C],tri⟩ 1).trans
      (dist_circumcenter_eq_circumradius ⟨![A,B,C],tri⟩ 2).symm
  have hO0 : (f O) 0 = 0 := by
    have h₁ := hdist B O
    have h₂ := hdist C O
    rw [hdBC] at h₁
    simp only [hB0, hB1, hC0, hC1] at h₁ h₂
    nlinarith only [h₁,h₂]
  have hO1 : 2*b*(f O) 1 = a^2+b^2-1 := by
    have h₁ := hdist A O
    have h₂ := hdist B O
    rw [hdAB] at h₁
    simp only [hA0, hA1, hB0, hB1, hO0] at h₁ h₂
    nlinarith only [h₁,h₂]
  have hGcoord (i : Fin 2) : (f G) i = ((f A) i + (f B) i + (f C) i) / 3 := by
    have hw : (Finset.univ : Finset (Fin 3)).sum
        (Finset.centroidWeights ℝ Finset.univ) = (1 : ℝ) := by
      norm_num [Finset.centroidWeights, Fin.sum_univ_succ]
    rw [hG, Finset.centroid_def,
      show f ((Finset.affineCombination ℝ Finset.univ ![A,B,C])
          (Finset.centroidWeights ℝ Finset.univ)) = _ from
        Finset.map_affineCombination _ _ _ hw f.toAffineMap,
      Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp [Fin.sum_univ_succ, Finset.centroidWeights, Function.comp_def]
    ring
  have hG0 : (f G) 0 = a/3 := by simpa [hA0,hB0,hC0] using hGcoord 0
  have hG1 : (f G) 1 = b/3 := by simpa [hA1,hB1,hC1] using hGcoord 1
  have hface : Set.range ((⟨![A,B,C],tri⟩ : Affine.Triangle ℝ ℝ²).faceOpposite 0).points = {B,C} := by
    rw [range_faceOpposite_points]
    ext Z
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      fin_cases i <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
  have hHproj : H = orthogonalProjection (affineSpan ℝ {B,C}) A := by
    simpa only [altitudeFoot, orthogonalProjectionSpan, hface, Matrix.cons_val_zero] using hH
  have hHmem : H ∈ affineSpan ℝ {B,C} := by
    rw [hHproj]
    exact orthogonalProjection_mem A
  have hH1 : (f H) 1 = 0 := by
    obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hHmem
    rw [← hu, hlm, hB1, hC1]
    ring
  have hpyth (U V Y Z : ℝ²) (hZ : Z = orthogonalProjection (affineSpan ℝ {U,V}) Y) :
      dist U Y ^2 = dist U Z ^2 + dist Y Z ^2 ∧
      dist V Y ^2 = dist V Z ^2 + dist Y Z ^2 := by
    rw [hZ]
    constructor
    · simpa only [pow_two] using
        dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq Y
          (left_mem_affineSpan_pair ℝ U V)
    · simpa only [pow_two] using
        dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq Y
          (right_mem_affineSpan_pair ℝ U V)
  have hH0 : (f H) 0 = a := by
    obtain ⟨h₁,h₂⟩ := hpyth B C A H hHproj
    have hd₁ := hdist B A
    have hd₂ := hdist C A
    have hd₃ := hdist B H
    have hd₄ := hdist C H
    rw [h₁] at hd₁
    rw [h₂] at hd₂
    simp only [hA0,hA1,hB0,hB1,hC0,hC1,hH1] at hd₁ hd₂ hd₃ hd₄
    nlinarith only [hd₁, hd₂, hd₃, hd₄]
  let S : Set ℝ² := {Z | a*b*((f Z) 0 ^ 2 + (f Z) 1 ^ 2) +
    b*(a-1)*(f Z) 0 + (1-a^2)*(f Z) 1 - b = 0}
  have hS : Cospherical S := by
    apply (LeanFlowProofs.PBAdvanced010.cosphericalCoordinateQuadratic f ρ hρ hscale S).2
    refine ⟨(a-1)/a, (1-a^2)/(a*b), -1/a, ?_⟩
    intro Z hZ
    change a*b*((f Z) 0 ^ 2 + (f Z) 1 ^ 2) + b*(a-1)*(f Z) 0 + (1-a^2)*(f Z) 1 - b = 0 at hZ
    field_simp
    nlinarith only [hZ]
  rcases hS with ⟨W, r, hr⟩
  refine ⟨⟨W, r⟩, ?_⟩
  intro X hX P hP Q hQ H₁ hH₁ K hK hK_ne_Q hCircles_ne T hT
  have hAB : A ≠ B := by
    intro h
    have := congrArg (fun Z => (f Z) 1) h
    simp only [hA1,hB1] at this
    exact hb this
  have hAC : A ≠ C := by
    intro h
    have := congrArg (fun Z => (f Z) 1) h
    simp only [hA1,hC1] at this
    exact hb this
  have hBC : B ≠ C := by
    intro h
    have := congrArg (fun Z => (f Z) 0) h
    simp only [hB0,hC0] at this
    norm_num at this
  obtain ⟨s, hsP⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hP.2.mem_affineSpan_of_mem_of_ne (p₃ := P) (by simp) (by simp) (by simp) hAC)
  obtain ⟨t, htQ⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hQ.2.mem_affineSpan_of_mem_of_ne (p₃ := Q) (by simp) (by simp) (by simp) hAB)
  have hP0 : (f P) 0 = a+s*(1-a) := by rw [←hsP,hlm,hA0,hC0]
  have hP1 : (f P) 1 = b*(1-s) := by rw [←hsP,hlm,hA1,hC1]; ring
  have hQ0 : (f Q) 0 = a-t*(a+1) := by rw [←htQ,hlm,hA0,hB0]; ring
  have hQ1 : (f Q) 1 = b*(1-t) := by rw [←htQ,hlm,hA1,hB1]; ring
  have hs0 : s ≠ 0 := by
    intro hs
    have hpa : P = A := by simpa [hs] using hsP.symm
    have hc := hP.1
    rw [hpa] at hc
    apply hX.2
    exact Or.inl (Or.inl (hc.mem_affineSpan_of_mem_of_ne
      (p₃ := X) (by simp) (by simp) (by simp) hAB))
  have hs1 : s ≠ 1 := by
    intro hs
    have hpc : P = C := by simpa [hs] using hsP.symm
    have hc := hP.1
    rw [hpc] at hc
    apply hX.2
    exact Or.inr (hc.mem_affineSpan_of_mem_of_ne
      (p₃ := X) (by simp) (by simp) (by simp) hBC)
  have hPynz : (f P) 1 ≠ 0 := by rw [hP1]; exact mul_ne_zero hb (sub_ne_zero.mpr (Ne.symm hs1))
  have heuler : (3-3*a^2-b^2)*(f X) 0 - 2*a*b*(f X) 1 + a*(a^2+b^2-1) = 0 := by
    have hd := hdet O G X hX.1
    simp only [hO0,hG0,hG1] at hd
    linear_combination 6*b*hd + (3*(f X) 0-a)*hO1
  let r₀ := (1-(f X) 0+(a-1)*(f X) 1/b)/2
  let w₀ := (1+(f X) 0-(a+1)*(f X) 1/b)/2
  have hr₀ : r₀ = t*(1-w₀) := by
    have hd := hdet C X Q hQ.1
    simp only [hQ0,hQ1,hC0,hC1] at hd
    dsimp [r₀,w₀]
    field_simp
    nlinarith only [hd]
  have hw₀ : w₀ = s*(1-r₀) := by
    have hd := hdet B X P hP.1
    simp only [hP0,hP1,hB0,hB1] at hd
    dsimp [r₀,w₀]
    field_simp
    nlinarith only [hd]
  have hx₀ : a-(a+1)*r₀+(1-a)*w₀ = (f X) 0 := by
    dsimp [r₀,w₀]
    field_simp
    ring
  have hy₀ : b*(1-r₀-w₀) = (f X) 1 := by
    dsimp [r₀,w₀]
    field_simp
    ring
  have he : 4*a*(a^2+b^2-1)*s*t -
      ((3-3*a^2-b^2)+3*a*(a^2+b^2-1))*s +
      ((3-3*a^2-b^2)-3*a*(a^2+b^2-1))*t + 2*a*(a^2+b^2-1) = 0 := by
    apply LeanFlowProofs.PBAdvanced010.eulerParameters a b s t r₀ w₀ hr₀ hw₀
    rw [hx₀,hy₀]
    exact heuler
  have hUmem : H₁ ∈ affineSpan ℝ {A,B} := by rw [hH₁]; exact orthogonalProjection_mem P
  obtain ⟨u, hu⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hUmem
  have hU0 : (f H₁) 0 = a-u*(a+1) := by rw [←hu,hlm,hA0,hB0]; ring
  have hU1 : (f H₁) 1 = b*(1-u) := by rw [←hu,hlm,hA1,hB1]; ring
  let c := (a+1)^2+b^2
  let n := a^2+b^2-1
  have hc : c ≠ 0 := by dsimp [c]; nlinarith only [sq_pos_of_ne_zero hb, sq_nonneg (a+1)]
  have huval : c*u = s*n := by
    obtain ⟨h₁,h₂⟩ := hpyth A B P H₁ hH₁
    have hd₁ := hdist A P
    have hd₂ := hdist B P
    have hd₃ := hdist A H₁
    have hd₄ := hdist B H₁
    rw [h₁] at hd₁
    rw [h₂] at hd₂
    simp only [hA0,hA1,hB0,hB1,hP0,hP1,hU0,hU1] at hd₁ hd₂ hd₃ hd₄
    dsimp [c,n]
    linear_combination (hd₂-hd₁-hd₄+hd₃)/2
  have hsing : (orthogonalProjection (affineSpan ℝ {H₁}) A : ℝ²) = H₁ := by
    have hh := orthogonalProjection_mem (s := affineSpan ℝ {H₁}) A
    simpa using hh
  have hKline : K = AffineMap.lineMap A H₁ (2 : ℝ) := by
    rw [hK, reflection_apply', hsing, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  have hK0 : (f K) 0 = a-(2*s*n/c)*(a+1) := by
    rw [hKline,hlm,hA0,hU0]
    field_simp
    linear_combination -2*(a+1)*huval
  have hK1 : (f K) 1 = b*(1-2*s*n/c) := by
    rw [hKline,hlm,hA1,hU1]
    field_simp
    linear_combination -2*huval
  have hkq : 2*s*n ≠ c*t := by
    intro heq
    apply hK_ne_Q
    apply f.injective
    ext i
    fin_cases i
    · change (f K) 0 = (f Q) 0
      rw [hK0,hQ0,heq, mul_div_cancel_left₀ _ hc]
    · change (f K) 1 = (f Q) 1
      rw [hK1,hQ1,heq, mul_div_cancel_left₀ _ hc]
  obtain ⟨α, β, γ, hq₁⟩ :=
    (LeanFlowProofs.PBAdvanced010.cosphericalCoordinateQuadratic f ρ hρ hscale _).1 hT.2.1
  obtain ⟨α₂, β₂, γ₂, hq₂⟩ :=
    (LeanFlowProofs.PBAdvanced010.cosphericalCoordinateQuadratic f ρ hρ hscale _).1 hT.2.2
  have hg₂ : γ₂ = 0 := by
    simpa only [hM0,hM1,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,zero_add]
      using hq₂ M (by simp)
  subst γ₂
  have ha₂ : α₂ = -a := by
    have hh := hq₂ H (by simp)
    simp only [hH0,hH1,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hh
    have hz : a*(a+α₂) = 0 := by nlinarith only [hh]
    have hh' := (mul_eq_zero.mp hz).resolve_left ha
    linarith only [hh']
  subst α₂
  have hcircle₂ (Z : ℝ²) (hZ : Z ∈ ({T,P,H,M} : Set ℝ²)) :
      (f Z) 0 ^2 + (f Z) 1 ^2 - a*(f Z) 0 + β₂*(f Z) 1 = 0 := by
    simpa only [neg_mul, ←sub_eq_add_neg, add_zero] using hq₂ Z hZ
  have hpower : (1/a)^2+α*(1/a)+γ = (1-a^2)/a^2 := by
    have hp := LeanFlowProofs.PBAdvanced010.equalPower a b s t α β γ ha hb hs0 hkq
      (by simpa only [hK0,hK1] using hq₁ K (by simp))
      (by simpa only [hP0,hP1] using hq₁ P (by simp))
      (by simpa only [hQ0,hQ1] using hq₁ Q (by simp))
    dsimp only at hp
    simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at hp
    rw [he] at hp
    have hh := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero (by norm_num) ha)
    exact sub_eq_zero.mp hh
  have hcoeff : α+a ≠ 0 ∨ β-β₂ ≠ 0 ∨ γ ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hCircles_ne
    apply (LeanFlowProofs.PBAdvanced010.cosphericalCoordinateQuadratic f ρ hρ hscale _).2
    refine ⟨α,β,γ,?_⟩
    intro Z hZ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
    rcases hZ with (hZ | hZ | hZ | hZ | hZ)
    · rw [hZ]; exact hq₁ K (by simp)
    · rw [hZ]; exact hq₁ P (by simp)
    · rw [hZ]; exact hq₁ Q (by simp)
    · have hh := hq₂ H (by simp)
      have haa : α = -a := by linarith only [hn.1]
      rw [hZ,haa,sub_eq_zero.mp hn.2.1,hn.2.2]
      exact hh
    · have hh := hq₂ M (by simp)
      have haa : α = -a := by linarith only [hn.1]
      rw [hZ,haa,sub_eq_zero.mp hn.2.1,hn.2.2]
      exact hh
  have haxis (Z : ℝ²) (h₁ : Z ∈ ({T,K,P,Q} : Set ℝ²))
      (h₂ : Z ∈ ({T,P,H,M} : Set ℝ²)) :
      (α+a)*(f Z) 0 + (β-β₂)*(f Z) 1 + γ = 0 := by
    linear_combination hq₁ Z h₁ - hcircle₂ Z h₂
  have hJ : (α+a)*(1/a)+(β-β₂)*0+γ = 0 := by
    have hκ : (1/a)^2-a*(1/a) = (1-a^2)/a^2 := by field_simp
    linear_combination hpower - hκ
  have hrad := LeanFlowProofs.PBAdvanced010.radicalAxisDet
    ((f P) 0) ((f P) 1) ((f T) 0) ((f T) 1) (1/a) 0
    (α+a) (β-β₂) γ hcoeff
    (haxis P (by simp) (by simp)) (haxis T (by simp) (by simp)) hJ
  have hcol : (a*(f P) 0-1)*(f T) 1-(f P) 1*(a*(f T) 0-1) = 0 := by
    convert congrArg (fun z : ℝ => a*z) hrad using 1 <;> field_simp <;> ring
  have hside : b*((f P) 0-1)+(1-a)*(f P) 1 = 0 := by rw [hP0,hP1]; ring
  have hTP : ((f T) 0,(f T) 1) ≠ ((f P) 0,(f P) 1) := by
    intro heq
    apply hT.1
    apply f.injective
    ext i
    fin_cases i
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq
  apply hr
  change a*b*((f T) 0 ^ 2 + (f T) 1 ^ 2) + b*(a-1)*(f T) 0 + (1-a^2)*(f T) 1 - b = 0
  exact LeanFlowProofs.PBAdvanced010.secantLocus a b β₂
    ((f P) 0) ((f P) 1) ((f T) 0) ((f T) 1) ha hb hPynz hside
    (hcircle₂ P (by simp)) (hcircle₂ T (by simp)) hcol hTP

