import Mathlib

theorem LeanFlowProofs.PB016.initial_coordinates
    (r q κ : ℝ)
    (hr : 0 < r) (hq : 0 < q) (hrq : r * q < 1)
    (hne : r ≠ q) (hκ : 0 < κ)
    (e : (ℝ × ℝ) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hmetric : ∀ z t : ℝ × ℝ,
      dist (e z) (e t) ^ 2 =
        κ * ((1 - r * q) * (z.1 - t.1) ^ 2 +
          r * q * (z.2 - t.2) ^ 2))
    (E F U V L : EuclideanSpace ℝ (Fin 2))
    (hE : Collinear ℝ {E, e (r, 1 + r), e (0, 0)} ∧
      Collinear ℝ {E, e (-1, 0), e (q, -1 - q)})
    (hF : Collinear ℝ {F, e (q, -1 - q), e (0, 0)} ∧
      Collinear ℝ {F, e (-1, 0), e (r, 1 + r)})
    (hU : Sbtw ℝ (e (-1, 0)) U (e (r, 1 + r)) ∧
      dist (e (-1, 0)) U = dist (e (-1, 0)) E)
    (hV : Sbtw ℝ (e (-1, 0)) V (e (q, -1 - q)) ∧
      dist (e (-1, 0)) V = dist (e (-1, 0)) F)
    (hL : EuclideanGeometry.angle (e (-1, 0)) (e (0, 0)) L = Real.pi / 2 ∧
      Collinear ℝ {L, e (r, 1 + r), e (q, -1 - q)}) :
    U = e (-r / (1 + 2 * r), (1 + r) / (1 + 2 * r)) ∧
    V = e (-q / (1 + 2 * q), -(1 + q) / (1 + 2 * q)) ∧
    L = e (0, (r + q + 2 * r * q) / (q - r)) := by set_option maxHeartbeats 800000 in
  obtain ⟨E, rfl⟩ := e.surjective E
  obtain ⟨F, rfl⟩ := e.surjective F
  obtain ⟨U, rfl⟩ := e.surjective U
  obtain ⟨V, rfl⟩ := e.surjective V
  obtain ⟨L, rfl⟩ := e.surjective L
  have det (a b c : ℝ × ℝ) (h : Collinear ℝ {e a, e b, e c}) :
      (a.1-c.1)*(b.2-c.2)-(a.2-c.2)*(b.1-c.1)=0 := by
    obtain ⟨v,hv⟩ := (collinear_iff_of_mem (by simp : e c ∈ ({e a,e b,e c} : Set _))).mp h
    obtain ⟨s,hs⟩ := hv (e a) (by simp)
    obtain ⟨t,ht⟩ := hv (e b) (by simp)
    have hs' := congrArg e.symm hs
    have ht' := congrArg e.symm ht
    simp only [AffineEquiv.symm_apply_apply, AffineEquiv.map_vadd, map_smul] at hs' ht'
    have h1 := congrArg Prod.fst hs'
    have h2 := congrArg Prod.snd hs'
    have h3 := congrArg Prod.fst ht'
    have h4 := congrArg Prod.snd ht'
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      vadd_eq_add, smul_eq_mul] at h1 h2 h3 h4
    rw [h1,h2,h3,h4]
    ring
  have he1 := det _ _ _ hE.1
  have he2 := det _ _ _ hE.2
  have hf1 := det _ _ _ hF.1
  have hf2 := det _ _ _ hF.2
  dsimp at he1 he2 hf1 hf2
  have heY : E.2 = -E.1 - 1 := by
    have : (1+q)*(E.2+E.1+1)=0 := by nlinarith only [he2]
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have hfY : F.2 = F.1 + 1 := by
    have : (1+r)*(F.2-F.1-1)=0 := by nlinarith only [hf2]
    rcases mul_eq_zero.mp this with h | h
    · linarith only [h,hr]
    · linarith only [h]
  have heX : (1+2*r)*E.1 = -r := by rw [heY] at he1; nlinarith only [he1]
  have hfX : (1+2*q)*F.1 = -q := by rw [hfY] at hf1; nlinarith only [hf1]
  have huB : Wbtw ℝ (-1,0) U (r,1+r) := e.wbtw_map_iff.mp hU.1.1
  have hvB : Wbtw ℝ (-1,0) V (q,-1-q) := e.wbtw_map_iff.mp hV.1.1
  obtain ⟨s,hs,hsU⟩ := huB
  obtain ⟨t,ht,htV⟩ := hvB
  have huX := congrArg Prod.fst hsU
  have huY := congrArg Prod.snd hsU
  have hvX := congrArg Prod.fst htV
  have hvY := congrArg Prod.snd htV
  simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at huX huY hvX hvY
  have huY' : U.2 = U.1 + 1 := by nlinarith only [huX,huY]
  have hvY' : V.2 = -V.1 - 1 := by nlinarith only [hvX,hvY]
  have huPos : 0 ≤ U.1+1 := by nlinarith only [huX, hs.1, mul_nonneg hs.1 (le_of_lt hr)]
  have hvPos : 0 ≤ V.1+1 := by nlinarith only [hvX, ht.1, mul_nonneg ht.1 (le_of_lt hq)]
  have hePos : 0 ≤ E.1+1 := by nlinarith only [heX,hr]
  have hfPos : 0 ≤ F.1+1 := by nlinarith only [hfX,hq]
  have hdu := congrArg (fun d : ℝ => d^2) hU.2
  have hdv := congrArg (fun d : ℝ => d^2) hV.2
  rw [hmetric, hmetric] at hdu hdv
  dsimp at hdu hdv
  rw [heY,huY'] at hdu
  rw [hfY,hvY'] at hdv
  have huSq : (U.1+1)^2 = (E.1+1)^2 := by
    apply mul_left_cancel₀ (ne_of_gt hκ)
    convert hdu using 1 <;> ring
  have hvSq : (V.1+1)^2 = (F.1+1)^2 := by
    apply mul_left_cancel₀ (ne_of_gt hκ)
    convert hdv using 1 <;> ring
  have huEq : U.1 = E.1 := by nlinarith only [huSq,huPos,hePos]
  have hvEq : V.1 = F.1 := by nlinarith only [hvSq,hvPos,hfPos]
  have hpy := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
    (e (-1,0)) (e (0,0)) (e L)).mpr hL.1
  simp only [← sq] at hpy
  rw [hmetric,hmetric,hmetric] at hpy
  dsimp at hpy
  have hlX : L.1 = 0 := by
    have : κ * (1-r*q) * L.1 = 0 := by nlinarith only [hpy]
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (ne_of_gt hκ) (by linarith))
  have hlD := det _ _ _ hL.2
  dsimp at hlD
  rw [hlX] at hlD
  have hr0 : 1+2*r ≠ 0 := by positivity
  have hq0 : 1+2*q ≠ 0 := by positivity
  have hl0 : q-r ≠ 0 := sub_ne_zero.mpr hne.symm
  have heVal : E.1 = -r/(1+2*r) := (eq_div_iff hr0).mpr (by nlinarith only [heX])
  have hfVal : F.1 = -q/(1+2*q) := (eq_div_iff hq0).mpr (by nlinarith only [hfX])
  refine ⟨congrArg e (Prod.ext ?_ ?_), congrArg e (Prod.ext ?_ ?_), congrArg e (Prod.ext ?_ ?_)⟩
  · exact huEq.trans heVal
  · dsimp; rw [huY',huEq,heVal]; field_simp; ring
  · exact hvEq.trans hfVal
  · dsimp; rw [hvY',hvEq,hfVal]; field_simp; ring
  · exact hlX
  · dsimp; apply (eq_div_iff hl0).mpr; nlinarith only [hlD]

