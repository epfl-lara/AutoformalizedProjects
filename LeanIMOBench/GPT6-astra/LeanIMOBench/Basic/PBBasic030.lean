import LeanFlowProofs.PBBasic030.DiscriminantSwap
import Mathlib

/-
Given a trapezoid $ABCD$ with $AB,CD$ as the two legs. Circle $(W_{1})$ passes through $A,B$, and $(W_{2})$ passes through $C,D$ so that they are tangent to each other. The inscribed angle on circle $W_1$ corresponding to the arc AB on the side opposite to C and D is alpha, and the inscribed angle on circle $W_2$ corresponding to the arc CD on the side opposite to  A and B is beta. Construct $(W_{3})$ passing through $A,B$, $(W_{4})$ passing through $C,D$ such that the inscribed angle on circle W3 corresponding to the arc AB on the side opposite to C and D is $\beta$, and the inscribed angle on circle $W_4$ corresponding to the arc CD on the side opposite to  A and B is b $\alpha$. Prove that $(W_{3}),(W_{4})$ are tangent to each other.
-/
open Real Affine Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

-- A predicate that ABCD is a trapezoid with legs AB, CD
structure IsTrapezoid (A B C D : ℝ²) : Prop where
  nodup : [A,B,C,D].Nodup
  ncoll : ¬ Collinear ℝ {A,B,C,D}
  para : (affineSpan ℝ {B, C}) ∥ (affineSpan ℝ {D, A})
  order : (affineSpan ℝ {A, B}).WSameSide C D

-- A predicate that two sphere are tangent somehow (externally or internally)
def SphereTangent (s1 s2 : Sphere ℝ²) :=
  s1.IsExtTangent s2 ∨ s1.IsIntTangent s2 ∨ s2.IsIntTangent s1

theorem PBBasic030 (A B C D : ℝ²) (trapezoid : IsTrapezoid A B C D)
    (W₁ W₂ W₃ W₄ : Sphere ℝ²)
    (h_AW₁ : A ∈ W₁) (h_BW₁ : B ∈ W₁) (h_CW₂ : C ∈ W₂) (h_DW₂ : D ∈ W₂)
    (h_AW₃ : A ∈ W₃) (h_BW₃ : B ∈ W₃) (h_CW₄ : C ∈ W₄) (h_DW₄ : D ∈ W₄)
    (tangent_W : SphereTangent W₁ W₂) (α β : Angle)
    (X₁ X₂ X₃ X₄ : ℝ²) -- X₁ ... X₄ will be the points to measure the inscribed angles
    (h_XW₁ : X₁ ∈ W₁) (h_XW₂ : X₂ ∈ W₂) (h_XW₃ : X₃ ∈ W₃) (h_XW₄ : X₄ ∈ W₄)
    -- since a point measures inscribed angle of an arc opposite to the given point,
    -- X₁, X₃ should be on the same side as AB, and X₂, X₄ on the same side as CD
    (h_side_X₁ : (affineSpan ℝ {A, B}).SSameSide X₁ C)
    (h_side_X₂ : (affineSpan ℝ {C, D}).SSameSide X₂ A)
    (h_side_X₃ : (affineSpan ℝ {A, B}).SSameSide X₃ C)
    (h_side_X₄ : (affineSpan ℝ {C, D}).SSameSide X₄ A)
    (angle_X₁ : ∠ A X₁ B = α) (angle_X₂ : ∠ C X₂ D = β)
    (angle_X₃ : ∠ A X₃ B = β) (angle_X₄ : ∠ C X₄ D = α) :
    SphereTangent W₃ W₄ := by run_tac withTheReader Lean.Core.Context (fun ctx => { ctx with maxHeartbeats := 4000000000 }) do
    let stx ← `(tactic| (
  classical
  have hdist (P Q : ℝ²) : dist P Q ^ 2 = (P 0-Q 0)^2+(P 1-Q 1)^2 := by
    rw [EuclideanSpace.dist_eq]
    simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    rw [Real.sq_sqrt (by positivity)]
  have htang (S T : Sphere ℝ²) (hs : 0 ≤ S.radius) (ht : 0 ≤ T.radius) : SphereTangent S T ↔ (dist S.center T.center ^ 2-S.radius^2-T.radius^2)^2-4*S.radius^2*T.radius^2=0 := by
    rw [SphereTangent, Sphere.isExtTangent_iff_dist_center, Sphere.isIntTangent_iff_dist_center, Sphere.isIntTangent_iff_dist_center]
    simp only [hs, ht, and_true, dist_comm T.center S.center]
    have hd : 0 ≤ dist S.center T.center := dist_nonneg
    constructor
    · rintro (h | h | h) <;> rw [h] <;> ring
    · intro h
      have hf : (dist S.center T.center ^ 2-(S.radius+T.radius)^2)*(dist S.center T.center ^ 2-(T.radius-S.radius)^2)=0 := by nlinarith [h]
      rcases mul_eq_zero.mp hf with h | h
      · left; nlinarith
      · rcases le_total S.radius T.radius with hr | hr
        · right; left; nlinarith
        · right; right; nlinarith
  let det := fun P Q X : ℝ² => (Q 0-P 0)*(X 1-P 1)-(Q 1-P 1)*(X 0-P 0)
  have hline (P Q X : ℝ²) (hpq : P ≠ Q) : X ∈ affineSpan ℝ {P,Q} ↔ det P Q X=0 := by
    have hl : X ∈ affineSpan ℝ {P,Q} ↔ ∃ t : ℝ, X=t • (Q-P)+P := by
      constructor
      · intro h
        have hv := (affineSpan ℝ {P,Q}).vsub_mem_direction h (left_mem_affineSpan_pair ℝ P Q)
        rw [direction_affineSpan, Set.pair_comm, vectorSpan_pair, Submodule.mem_span_singleton] at hv
        rcases hv with ⟨t,ht⟩
        exact ⟨t,sub_eq_iff_eq_add.mp ht.symm⟩
      · rintro ⟨t,rfl⟩
        exact (affineSpan ℝ {P,Q}).smul_vsub_vadd_mem t (right_mem_affineSpan_pair ℝ P Q) (left_mem_affineSpan_pair ℝ P Q) (left_mem_affineSpan_pair ℝ P Q)
    rw [hl]
    dsimp only [det]
    constructor
    · rintro ⟨t,rfl⟩
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      ring
    · intro hd
      by_cases h₀ : Q 0-P 0=0
      · have h₁ : Q 1-P 1 ≠ 0 := by
          intro h₁
          apply hpq
          apply PiLp.ext
          intro i
          fin_cases i
          · exact (sub_eq_zero.mp h₀).symm
          · exact (sub_eq_zero.mp h₁).symm
        refine ⟨(X 1-P 1)/(Q 1-P 1),?_⟩
        apply PiLp.ext
        intro i
        fin_cases i
        · change X 0=(X 1-P 1)/(Q 1-P 1)*(Q 0-P 0)+P 0
          rw [h₀,mul_zero,zero_add]
          have h : (Q 1-P 1)*(X 0-P 0)=0 := by simpa [h₀] using hd
          exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h₁)
        · change X 1=(X 1-P 1)/(Q 1-P 1)*(Q 1-P 1)+P 1
          rw [div_mul_cancel₀ _ h₁,sub_add_cancel]
      · refine ⟨(X 0-P 0)/(Q 0-P 0),?_⟩
        apply PiLp.ext
        intro i
        fin_cases i
        · change X 0=(X 0-P 0)/(Q 0-P 0)*(Q 0-P 0)+P 0
          rw [div_mul_cancel₀ _ h₀,sub_add_cancel]
        · change X 1=(X 0-P 0)/(Q 0-P 0)*(Q 1-P 1)+P 1
          apply (mul_left_cancel₀ h₀)
          field_simp
          nlinarith only [hd]
  have hside (P Q X Y : ℝ²) (hpq : P ≠ Q) (hs : (affineSpan ℝ {P,Q}).WSameSide X Y) : 0 ≤ det P Q X*det P Q Y := by
    rcases hs with ⟨U,hU,V,hV,hr⟩
    have hU' := (hline P Q U hpq).mp hU
    have hV' := (hline P Q V hpq).mp hV
    by_cases hx : X -ᵥ U=0
    · have hxu : X=U := vsub_eq_zero_iff_eq.mp hx
      rw [hxu,hU',zero_mul]
    · obtain ⟨t,ht,he⟩ := hr.exists_nonneg_left hx
      have he₀ := congrArg (fun Z : ℝ² => Z 0) he
      have he₁ := congrArg (fun Z : ℝ² => Z 1) he
      simp only [vsub_eq_sub,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] at he₀ he₁
      have hd : det P Q Y=t*det P Q X := by
        dsimp [det] at hU' hV' ⊢
        linear_combination -(Q 0-P 0)*he₁+(Q 1-P 1)*he₀+hV'-t*hU'
      rw [hd]
      nlinarith [mul_nonneg ht (sq_nonneg (det P Q X))]
  have hstrict (P Q X Y : ℝ²) (hpq : P ≠ Q) (hs : (affineSpan ℝ {P,Q}).SSameSide X Y) : 0 < det P Q X*det P Q Y := by
    exact lt_of_le_of_ne (hside P Q X Y hpq hs.1) (Ne.symm (mul_ne_zero ((hline P Q X hpq).not.mp hs.2.1) ((hline P Q Y hpq).not.mp hs.2.2)))
  have hcot (P Q X : ℝ²) (α : Angle) (ha : ∠ P X Q=α) (hd : det P Q X ≠ 0) : α.cos/α.sin*|det P Q X|=(P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1) := by
    have hi (a b : ℝ²) : inner ℝ a b=a 0*b 0+a 1*b 1 := by
      simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Fin.sum_univ_two,mul_comm]
    have hc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (P-X) (Q-X)
    have hs := InnerProductGeometry.sin_angle_mul_norm_mul_norm (P-X) (Q-X)
    have ha' : (InnerProductGeometry.angle (P-X) (Q-X) : Angle)=α := ha
    have hc' := congrArg Angle.cos ha'
    have hs' := congrArg Angle.sin ha'
    simp only [Angle.cos_coe] at hc'
    simp only [Angle.sin_coe] at hs'
    rw [hc',hi] at hc
    rw [hs',hi,hi,hi] at hs
    simp only [PiLp.sub_apply] at hc hs
    have hh : ((P 0-X 0)*(P 0-X 0)+(P 1-X 1)*(P 1-X 1))*((Q 0-X 0)*(Q 0-X 0)+(Q 1-X 1)*(Q 1-X 1))-((P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1))*((P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1))=(det P Q X)^2 := by dsimp [det]; ring
    rw [hh,Real.sqrt_sq_eq_abs] at hs
    have hn : α.sin ≠ 0 := by intro h; rw [h,zero_mul] at hs; exact hd (abs_eq_zero.mp hs.symm)
    rw [← hs,div_mul_eq_mul_div,mul_div_assoc,mul_div_cancel_left₀ _ hn]
    exact hc
  have hchord (P Q X : ℝ²) (W : Sphere ℝ²) (z : ℝ) (hp : P ∈ W) (hq : Q ∈ W) (hx : X ∈ W) (hd : det P Q X ≠ 0) (hz : z*det P Q X= -((P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1))) :
      W.center 0=(P 0+Q 0+z*(Q 1-P 1))/2 ∧ W.center 1=(P 1+Q 1-z*(Q 0-P 0))/2 ∧ W.radius^2=((Q 0-P 0)^2+(Q 1-P 1)^2)*(1+z^2)/4 := by
    have hp' : (P 0-W.center 0)^2+(P 1-W.center 1)^2=W.radius^2 := by rw [← hdist, (show dist P W.center=W.radius from hp)]
    have hq' : (Q 0-W.center 0)^2+(Q 1-W.center 1)^2=W.radius^2 := by rw [← hdist, (show dist Q W.center=W.radius from hq)]
    have hx' : (X 0-W.center 0)^2+(X 1-W.center 1)^2=W.radius^2 := by rw [← hdist, (show dist X W.center=W.radius from hx)]
    have hq'' : 2*(Q 0-P 0)*W.center 0+2*(Q 1-P 1)*W.center 1=Q 0^2+Q 1^2-P 0^2-P 1^2 := by nlinarith only [hq',hp']
    have hx'' : 2*(X 0-P 0)*W.center 0+2*(X 1-P 1)*W.center 1=X 0^2+X 1^2-P 0^2-P 1^2 := by nlinarith only [hx',hp']
    have h₀ : W.center 0=(P 0+Q 0+z*(Q 1-P 1))/2 := by
      apply (mul_left_cancel₀ hd)
      dsimp [det] at hz ⊢
      linear_combination (X 1-P 1)/2*hq''-(Q 1-P 1)/2*hx''-(Q 1-P 1)/2*hz
    have h₁ : W.center 1=(P 1+Q 1-z*(Q 0-P 0))/2 := by
      apply (mul_left_cancel₀ hd)
      dsimp [det] at hz ⊢
      linear_combination -(X 0-P 0)/2*hq''+(Q 0-P 0)/2*hx''+(Q 0-P 0)/2*hz
    refine ⟨h₀,h₁,?_⟩
    rw [h₀,h₁] at hp'
    nlinarith only [hp']
  have hswap (a b u v k t s : ℝ) (hn : u^2+v^2 ≠ 0) :
      let U := a^2+b^2
      let V := (a+(k-1)*u)^2+(b+(k-1)*v)^2
      let H := fun z w : ℝ => ((k+1)*u-b*z-(b+(k-1)*v)*w)^2+((k+1)*v+a*z+(a+(k-1)*u)*w)^2
      (H t s-U*(1+t^2)-V*(1+s^2))^2-4*U*V*(1+t^2)*(1+s^2)=(H s t-U*(1+s^2)-V*(1+t^2))^2-4*U*V*(1+s^2)*(1+t^2) := by
    dsimp only
    let N := u^2+v^2
    let B := u*a+v*b
    let h := u*b-v*a
    have hU : B^2+h^2=N*(a^2+b^2) := by dsimp [B,h,N]; ring
    have hV : (B+k*N-N)^2+h^2=N*((a+(k-1)*u)^2+(b+(k-1)*v)^2) := by dsimp [B,h,N]; ring
    have hH (z w : ℝ) : (N+k*N-h*(z+w))^2+(B*z+(B+k*N-N)*w)^2=N*(((k+1)*u-b*z-(b+(k-1)*v)*w)^2+((k+1)*v+a*z+(a+(k-1)*u)*w)^2) := by dsimp [B,h,N]; ring
    have hh := LeanFlowProofs.PBBasic030.discriminantSwap B N (k*N) h t s
    dsimp only at hh
    rw [hU,hV,hH,hH] at hh
    have hn' : N^2 ≠ 0 := pow_ne_zero 2 hn
    apply (mul_left_cancel₀ hn')
    linear_combination hh
  have hn := trapezoid.nodup
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.nodup_nil, and_true] at hn
  have hAB : A ≠ B := hn.1.1
  have hCD : C ≠ D := hn.2.2.1.1
  have hAD : A ≠ D := hn.1.2.2.1
  obtain ⟨k,hk⟩ : ∃ k : ℝ, C=k • (D-A)+B := by
    have hd := trapezoid.para.direction_eq
    rw [direction_affineSpan,direction_affineSpan] at hd
    have hv := vsub_rev_mem_vectorSpan_pair ℝ B C
    rw [hd,vectorSpan_pair,Submodule.mem_span_singleton] at hv
    obtain ⟨k,hk⟩ := hv
    exact ⟨k,sub_eq_iff_eq_add.mp hk.symm⟩
  have hk₀ : C 0=k*(D 0-A 0)+B 0 := by simpa only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] using congrArg (fun Z : ℝ² => Z 0) hk
  have hk₁ : C 1=k*(D 1-A 1)+B 1 := by simpa only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul] using congrArg (fun Z : ℝ² => Z 1) hk
  have hdC : det A B C=k*det A B D := by dsimp [det]; rw [hk₀,hk₁]; ring
  have hdA : det C D A=det A B D := by dsimp [det]; rw [hk₀,hk₁]; ring
  have hdCne : det A B C ≠ 0 := (hline A B C hAB).not.mp h_side_X₁.2.2
  have hdDne : det A B D ≠ 0 := by intro h; apply hdCne; rw [hdC,h,mul_zero]
  have hkpos : 0 < k := by
    have hord := hside A B C D hAB trapezoid.order
    rw [hdC] at hord
    have hkne : k ≠ 0 := by intro h; apply hdCne; rw [hdC,h,zero_mul]
    have hs : 0 < (det A B D)^2 := sq_pos_of_ne_zero hdDne
    have hkn : 0 ≤ k := by nlinarith
    exact lt_of_le_of_ne hkn (Ne.symm hkne)
  have hN : (D 0-A 0)^2+(D 1-A 1)^2 ≠ 0 := by
    intro h
    have h₀ : D 0-A 0=0 := by nlinarith [sq_nonneg (D 1-A 1)]
    have h₁ : D 1-A 1=0 := by nlinarith [sq_nonneg (D 0-A 0)]
    apply hAD
    apply PiLp.ext
    intro i
    fin_cases i
    · exact (sub_eq_zero.mp h₀).symm
    · exact (sub_eq_zero.mp h₁).symm
  obtain ⟨ε,hε⟩ : ∃ ε : ℝ, ∀ x : ℝ, 0 < x*det A B D → ε*x = -|x| := by
    rcases lt_or_gt_of_ne hdDne with hdneg | hdpos
    · refine ⟨1,?_⟩
      intro x hx
      have hxn : x < 0 := by nlinarith only [hx, hdneg]
      rw [one_mul,abs_of_neg hxn,neg_neg]
    · refine ⟨-1,?_⟩
      intro x hx
      have hxp : 0 < x := (mul_pos_iff_of_pos_right hdpos).mp hx
      rw [neg_one_mul,abs_of_pos hxp]
  have habsign (X : ℝ²) (hs : (affineSpan ℝ {A,B}).SSameSide X C) : ε*det A B X = -|det A B X| := by
    apply hε
    have h := hstrict A B X C hAB hs
    rw [hdC] at h
    have h' : 0 < (det A B X*det A B D)*k := by nlinarith only [h]
    exact (mul_pos_iff_of_pos_right hkpos).mp h'
  have hcdsign (X : ℝ²) (hs : (affineSpan ℝ {C,D}).SSameSide X A) : ε*det C D X = -|det C D X| := by
    apply hε
    rw [← hdA]
    exact hstrict C D X A hCD hs
  let t := ε*(α.cos/α.sin)
  let s := ε*(β.cos/β.sin)
  have hz (P Q X : ℝ²) (γ : Angle) (ha : ∠ P X Q=γ) (hpq : P ≠ Q) (hnl : X ∉ affineSpan ℝ {P,Q}) (hsign : ε*det P Q X = -|det P Q X|) :
      (ε*(γ.cos/γ.sin))*det P Q X = -((P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1)) := by
    have hc := hcot P Q X γ ha ((hline P Q X hpq).not.mp hnl)
    calc
      (ε*(γ.cos/γ.sin))*det P Q X = (γ.cos/γ.sin)*(ε*det P Q X) := by ring
      _ = -((P 0-X 0)*(Q 0-X 0)+(P 1-X 1)*(Q 1-X 1)) := by rw [hsign,mul_neg,hc]
  have hc₁ := hchord A B X₁ W₁ t h_AW₁ h_BW₁ h_XW₁ ((hline A B X₁ hAB).not.mp h_side_X₁.2.1) (hz A B X₁ α angle_X₁ hAB h_side_X₁.2.1 (habsign X₁ h_side_X₁))
  have hc₂ := hchord C D X₂ W₂ s h_CW₂ h_DW₂ h_XW₂ ((hline C D X₂ hCD).not.mp h_side_X₂.2.1) (hz C D X₂ β angle_X₂ hCD h_side_X₂.2.1 (hcdsign X₂ h_side_X₂))
  have hc₃ := hchord A B X₃ W₃ s h_AW₃ h_BW₃ h_XW₃ ((hline A B X₃ hAB).not.mp h_side_X₃.2.1) (hz A B X₃ β angle_X₃ hAB h_side_X₃.2.1 (habsign X₃ h_side_X₃))
  have hc₄ := hchord C D X₄ W₄ t h_CW₄ h_DW₄ h_XW₄ ((hline C D X₄ hCD).not.mp h_side_X₄.2.1) (hz C D X₄ α angle_X₄ hCD h_side_X₄.2.1 (hcdsign X₄ h_side_X₄))
  let a := B 0 - A 0
  let b := B 1 - A 1
  let u := D 0 - A 0
  let v := D 1 - A 1
  let U := a^2+b^2
  let V := (a+(k-1)*u)^2+(b+(k-1)*v)^2
  let H := fun z w : ℝ => ((k+1)*u-b*z-(b+(k-1)*v)*w)^2+((k+1)*v+a*z+(a+(k-1)*u)*w)^2
  let F := fun z w : ℝ => (H z w-U*(1+z^2)-V*(1+w^2))^2-4*(U*(1+z^2))*(V*(1+w^2))
  have hFaux (z w : ℝ) : F z w = (H z w-U*(1+z^2)-V*(1+w^2))^2-4*U*V*(1+z^2)*(1+w^2) := by dsimp only [F]; ring
  have hF : F t s = F s t := by
    rw [hFaux,hFaux]
    exact hswap a b u v k t s hN
  have hCDlen : (D 0-C 0)^2+(D 1-C 1)^2=V := by
    dsimp [V,a,b,u,v]
    rw [hk₀,hk₁]
    ring
  have hrad₁ : 4*W₁.radius^2=U*(1+t^2) := by rw [hc₁.2.2]; dsimp [U,a,b]; ring
  have hrad₂ : 4*W₂.radius^2=V*(1+s^2) := by rw [hc₂.2.2,hCDlen]; ring
  have hrad₃ : 4*W₃.radius^2=U*(1+s^2) := by rw [hc₃.2.2]; dsimp [U,a,b]; ring
  have hrad₄ : 4*W₄.radius^2=V*(1+t^2) := by rw [hc₄.2.2,hCDlen]; ring
  have hcen (S T : Sphere ℝ²) (z w : ℝ)
      (hs₀ : S.center 0=(A 0+B 0+z*(B 1-A 1))/2)
      (hs₁ : S.center 1=(A 1+B 1-z*(B 0-A 0))/2)
      (ht₀ : T.center 0=(C 0+D 0+w*(D 1-C 1))/2)
      (ht₁ : T.center 1=(C 1+D 1-w*(D 0-C 0))/2) : 4*dist S.center T.center^2=H z w := by
    have h₀ : 2*(S.center 0-T.center 0) = -((k+1)*u-b*z-(b+(k-1)*v)*w) := by
      rw [hs₀,ht₀]
      dsimp [u,v,b]
      rw [hk₀,hk₁]
      ring
    have h₁ : 2*(S.center 1-T.center 1) = -((k+1)*v+a*z+(a+(k-1)*u)*w) := by
      rw [hs₁,ht₁]
      dsimp [u,v,a]
      rw [hk₀,hk₁]
      ring
    calc
      4*dist S.center T.center^2 = (2*(S.center 0-T.center 0))^2+(2*(S.center 1-T.center 1))^2 := by rw [hdist]; ring
      _ = H z w := by rw [h₀,h₁]; dsimp only [H]; ring
  have hcen₁₂ := hcen W₁ W₂ t s hc₁.1 hc₁.2.1 hc₂.1 hc₂.2.1
  have hcen₃₄ := hcen W₃ W₄ s t hc₃.1 hc₃.2.1 hc₄.1 hc₄.2.1
  have hdelta₁₂ : 16*((dist W₁.center W₂.center^2-W₁.radius^2-W₂.radius^2)^2-4*W₁.radius^2*W₂.radius^2)=F t s := by
    dsimp only [F]
    rw [← hcen₁₂,← hrad₁,← hrad₂]
    ring
  have hdelta₃₄ : 16*((dist W₃.center W₄.center^2-W₃.radius^2-W₄.radius^2)^2-4*W₃.radius^2*W₄.radius^2)=F s t := by
    dsimp only [F]
    rw [← hcen₃₄,← hrad₃,← hrad₄]
    ring
  have hr₁ : 0 ≤ W₁.radius := by rw [← (show dist A W₁.center=W₁.radius from h_AW₁)]; exact dist_nonneg
  have hr₂ : 0 ≤ W₂.radius := by rw [← (show dist C W₂.center=W₂.radius from h_CW₂)]; exact dist_nonneg
  have hr₃ : 0 ≤ W₃.radius := by rw [← (show dist A W₃.center=W₃.radius from h_AW₃)]; exact dist_nonneg
  have hr₄ : 0 ≤ W₄.radius := by rw [← (show dist C W₄.center=W₄.radius from h_CW₄)]; exact dist_nonneg
  apply (htang W₃ W₄ hr₃ hr₄).mpr
  have hd₁₂ := (htang W₁ W₂ hr₁ hr₂).mp tangent_W
  rw [hd₁₂,mul_zero] at hdelta₁₂
  rw [← hF,← hdelta₁₂] at hdelta₃₄
  exact (mul_eq_zero.mp hdelta₃₄).resolve_left (by norm_num)
  ))
    Lean.Elab.Tactic.evalTactic (stx.raw.rewriteBottomUp fun s => match s with
      | .ident info raw val _ => .ident info raw val.eraseMacroScopes []
      | _ => s)

