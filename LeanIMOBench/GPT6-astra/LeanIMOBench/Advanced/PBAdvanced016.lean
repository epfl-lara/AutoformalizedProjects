import LeanFlowProofs.PBAdvanced016.CrossedLines
import LeanFlowProofs.PBAdvanced016.InitialCoordinates
import LeanFlowProofs.PBAdvanced016.SecondIntersection
import LeanFlowProofs.PBAdvanced016.WeightedCircle
import LeanFlowProofs.PBAdvanced016.WeightedFrame
import Mathlib

/-
Let $ABC$ be a non-isosceles triangle with incenter $I$. Let line $BI$ intersect $AC$ at $E$, and line $CI$ intersect $AB$ at $F$. Two Points $U$ and $V$ are on segments $AB$ and $AC$ respectively, such that $AU = AE$ and $AV = AF$. Let the line passing through $I$ and perpendicular to $AI$ intersect line $BC$ at $L$. The circumcircle of $\triangle ILC$ intersects line $LU$ at $X$ (other than $L$), and the circumcircle of triangle $\triangle ILB$ intersects line $LV$ at $Y$ (other than $L$). Prove that if $P$ is the intersection of lines $YB$ and $XC$, then line $IP$ is parallel to line $XY$.
-/
open Affine.Simplex EuclideanGeometry Real
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem PBAdvanced016
    -- a triangle ABC
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    -- ABC is non-isosceles
    (n_isosceles : [dist A B, dist A C, dist B C].Nodup )
    (I : ℝ²) (hI : I = incenter ⟨![A, B, C], tri⟩) -- I is the incenter
    (E : ℝ²) (hE : Collinear ℝ {E, B, I} ∧ Collinear ℝ {E, A, C}) -- BI intersect AC at E
    (F : ℝ²) (hF : Collinear ℝ {F, C, I} ∧ Collinear ℝ {F, A, B}) -- CI intersect AB at E
    -- Two Points $U$ and $V$ are on segments $AB$ and $AC$ respectively, such that $AU = AE$ and $AV = AF$.
    (U : ℝ²) (hU : Sbtw ℝ A U B ∧ dist A U = dist A E)
    (V : ℝ²) (hV : Sbtw ℝ A V C ∧ dist A V = dist A F)
    -- the line passing through $I$ and perpendicular to $AI$ intersect line $BC$ at $L$.
    (L : ℝ²) (hL : ∠ A I L = π / 2 ∧ Collinear ℝ {L, B, C})
    -- The circumcircle of ILC intersects line LU at X (other than L),
    (X : ℝ²) (hX : X ≠ L ∧ Cospherical {X, I, L, C} ∧ Collinear ℝ {X, L, U})
    -- the circumcircle of ILB intersects line LV at Y (other than L).
    (Y : ℝ²) (hY : Y ≠ L ∧ Cospherical {Y, I, L, B} ∧ Collinear ℝ {Y, L, V})
    -- P is the intersection of lines YB and XC
    (P : ℝ²) (hP : Collinear ℝ {P, Y, B} ∧ Collinear ℝ {P, X, C}) :
    -- Prove that line $IP$ is parallel to line $XY$.
    (affineSpan ℝ {I, P}).Parallel (affineSpan ℝ {X, Y}) := by set_option maxHeartbeats 800000 in
  have hab : dist A B ≠ dist A C := by simpa using (List.nodup_cons.mp n_isosceles).1 |> fun h => (show dist A B ≠ dist A C from by intro he; exact h (by simp [he]))
  obtain ⟨r,q,κ,e,hr,hq,hrq,hrne,hκ,ha,hi,hb,hc,hmetric⟩ :=
    LeanFlowProofs.PB016.weighted_frame A B C I tri hab hI
  obtain ⟨hu,hv,hl⟩ := LeanFlowProofs.PB016.initial_coordinates r q κ hr hq hrq hrne hκ e hmetric E F U V L
    (by simpa [ha,hi,hb,hc] using hE) (by simpa [ha,hi,hb,hc] using hF)
    (by simpa [ha,hi,hb,hc] using hU) (by simpa [ha,hi,hb,hc] using hV)
    (by simpa [ha,hi,hb,hc] using hL)
  have det : ∀ a b c : ℝ × ℝ, Collinear ℝ {a,b,c} →
      (b.1-c.1)*(a.2-c.2)-(b.2-c.2)*(a.1-c.1)=0 := by
    intro a b c h
    obtain ⟨v,hh⟩ := (collinear_iff_of_mem (show c ∈ ({a,b,c} : Set (ℝ × ℝ)) by simp)).mp h
    obtain ⟨s,hs⟩ := hh a (by simp)
    obtain ⟨t,ht⟩ := hh b (by simp)
    rw [hs,ht]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, vadd_eq_add]
    ring
  have pull : ∀ a b c : ℝ × ℝ, Collinear ℝ {e a,e b,e c} → Collinear ℝ {a,b,c} := by
    intro a b c h
    obtain ⟨v,hh⟩ := (collinear_iff_of_mem (show e c ∈ ({e a,e b,e c} : Set ℝ²) by simp)).mp h
    apply (collinear_iff_of_mem (show c ∈ ({a,b,c} : Set (ℝ × ℝ)) by simp)).mpr
    refine ⟨e.symm.linear v, ?_⟩
    intro p hp
    have hep : e p ∈ ({e a,e b,e c} : Set ℝ²) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
      rcases hp with rfl | rfl | rfl <;> simp
    obtain ⟨t,ht⟩ := hh (e p) hep
    refine ⟨t, ?_⟩
    have hh := congrArg e.symm ht
    simpa only [AffineEquiv.map_vadd, map_smul, e.symm_apply_apply] using hh
  let l := (r+q+2*r*q)/(q-r)
  change L = e (0,l) at hl
  let m := (2+3*r+3*q+4*r*q)/(q-r)
  have hqr : q-r ≠ 0 := sub_ne_zero.mpr hrne.symm
  have hrd : 1+2*r ≠ 0 := ne_of_gt (by linarith)
  have hqd : 1+2*q ≠ 0 := ne_of_gt (by linarith)
  have hln : l ≠ 0 := div_ne_zero (ne_of_gt (by positivity)) hqr
  have hm : m ≠ -(2+r+q)/(q-r) := by
    dsimp [m]
    intro h
    have hh := (div_left_inj' hqr).mp h
    nlinarith [mul_pos hr hq]
  have hum : (1+r)/(1+2*r) = l + m*(-r/(1+2*r)) := by
    dsimp [l,m]; field_simp; ring
  have hvm : -(1+q)/(1+2*q) = l + m*(-q/(1+2*q)) := by
    dsimp [l,m]; field_simp; ring
  let x := e.symm X
  let y := e.symm Y
  let p := e.symm P
  have hxmap : e x = X := e.apply_symm_apply X
  have hymap : e y = Y := e.apply_symm_apply Y
  have hpmap : e p = P := e.apply_symm_apply P
  have hxline : x.2 = l + m*x.1 := by
    have hh := det x (0,l) (-r/(1+2*r),(1+r)/(1+2*r))
      (pull _ _ _ (by simpa [hxmap, ← hl, ← hu, l] using hX.2.2))
    simp only at hh
    rw [hum] at hh
    have hn : -r/(1+2*r) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hr.ne') hrd
    apply (mul_left_cancel₀ hn)
    nlinarith [hh]
  have hyline : y.2 = l + m*y.1 := by
    have hh := det y (0,l) (-q/(1+2*q),-(1+q)/(1+2*q))
      (pull _ _ _ (by simpa only [hymap, ← hl, ← hv] using hY.2.2))
    simp only at hh
    rw [hvm] at hh
    have hn : -q/(1+2*q) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hq.ne') hqd
    apply (mul_left_cancel₀ hn)
    nlinarith [hh]
  have hxn : x.1 ≠ 0 := by
    intro hx0
    have he : x = (0,l) := Prod.ext hx0 (by simpa [hx0] using hxline)
    apply hX.1
    rw [← hxmap, he]
    exact hl.symm
  have hyn : y.1 ≠ 0 := by
    intro hy0
    have he : y = (0,l) := Prod.ext hy0 (by simpa [hy0] using hyline)
    apply hY.1
    rw [← hymap, he]
    exact hl.symm
  have hbaseC : (1-r*q)*q^2+r*q*(-1-q)^2-(q*(1+r)*l)*q-r*q*l*(-1-q)=0 := by
    dsimp [l]; field_simp; ring
  have hbaseB : (1-r*q)*r^2+r*q*(1+r)^2-(-r*(1+q)*l)*r-r*q*l*(1+r)=0 := by
    dsimp [l]; field_simp; ring
  have hxc := LeanFlowProofs.PB016.weighted_circle_equation (1-r*q) (r*q) κ l q (-1-q) (q*(1+r)*l)
    hκ.ne' hln hq.ne' e hmetric hbaseC x (by simpa only [hxmap,hi,← hl,hc] using hX.2.1)
  have hyc := LeanFlowProofs.PB016.weighted_circle_equation (1-r*q) (r*q) κ l r (1+r) (-r*(1+q)*l)
    hκ.ne' hln hr.ne' e hmetric hbaseB y (by simpa only [hymap,hi,← hl,hb] using hY.2.1)
  let D := 1-r*q+r*q*m^2
  have hDpos : 0 < D := by dsimp [D]; nlinarith [mul_nonneg (mul_pos hr hq).le (sq_nonneg m)]
  have hxx : x.1 = q*l*(1+r-r*m)/D := by
    have hh := LeanFlowProofs.PB016.second_intersection (1-r*q) (r*q) l m (q*(1+r)*l) x.1 x.2 hDpos.ne' hxn hxline hxc
    rw [hh]; dsimp [D]; congr 1; ring
  have hyy : y.1 = -r*l*(1+q+q*m)/D := by
    have hh := LeanFlowProofs.PB016.second_intersection (1-r*q) (r*q) l m (-r*(1+q)*l) y.1 y.2 hDpos.ne' hyn hyline hyc
    rw [hh]; dsimp [D]; congr 1; ring
  have hpc := det p x (q,-1-q) (pull _ _ _ (by simpa only [hpmap,hxmap,hc] using hP.2))
  have hpb := det p y (r,1+r) (pull _ _ _ (by simpa only [hpmap,hymap,hb] using hP.1))
  simp only at hpc hpb
  have hcross := LeanFlowProofs.PB016.crossed_lines r q m hr hq hrq hrne hm p.1 p.2
  have hcross' := hcross (by change (q*l*(1+r-r*m)/D-q)*(p.2+1+q)-(l+m*(q*l*(1+r-r*m)/D)+1+q)*(p.1-q)=0; rw [← hxx, ← hxline]; nlinarith only [hpc])
    (by change (-r*l*(1+q+q*m)/D-r)*(p.2-1-r)-(l+m*(-r*l*(1+q+q*m)/D)-1-r)*(p.1-r)=0; rw [← hyy, ← hyline]; nlinarith only [hpb])
  obtain ⟨hp1,hp2,hd1,hd2,hpn,hxy⟩ := hcross'
  change q*l*(1+r-r*m)/D - (-r*l*(1+q+q*m)/D) = l*p.1 at hd1
  change (l+m*(q*l*(1+r-r*m)/D)) - (l+m*(-r*l*(1+q+q*m)/D)) = l*p.2 at hd2
  have hdisp : x - y = l • (p - (0,0)) := by
    apply Prod.ext
    · change x.1-y.1 = l*(p.1-0)
      simpa only [← hxx, ← hyy, sub_zero] using hd1
    · change x.2-y.2 = l*(p.2-0)
      simpa only [← hxx, ← hyy, ← hxline, ← hyline, sub_zero] using hd2
  have hw : X -ᵥ Y = l • (P -ᵥ I) := by
    have hh := congrArg e.toAffineMap.linear hdisp
    simpa only [map_smul, ← vsub_eq_sub, AffineMap.linearMap_vsub, AffineEquiv.coe_toAffineMap, hxmap, hymap, hpmap, hi] using hh
  apply AffineSubspace.affineSpan_pair_parallel_iff_exists_unit_smul'.mpr
  refine ⟨Units.mk0 (-l) (neg_ne_zero.mpr hln), ?_⟩
  change (-l) • (P -ᵥ I) = Y -ᵥ X
  rw [neg_smul, ← hw, neg_vsub_eq_vsub_rev]

