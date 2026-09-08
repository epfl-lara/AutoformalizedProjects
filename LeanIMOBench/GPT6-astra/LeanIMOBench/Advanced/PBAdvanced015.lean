import LeanFlowProofs.PB015CircumcircleCoordinates
import LeanFlowProofs.PB015CoordinateCollinear
import LeanFlowProofs.PB015ExternalParameter
import LeanFlowProofs.PB015InternalBisector
import LeanFlowProofs.PB015Normalize
import LeanFlowProofs.PB015OrthicEquations
import LeanFlowProofs.PB015SecantCoordinates
import LeanFlowProofs.PB015TangencyRelation
import LeanFlowProofs.PB015TangentLineSq
import Mathlib

/-
Consider an acute triangle $ABC$ that is not isosceles. Let $H_0$, $E$, and $F$ be the feet of the perpendiculars dropped from vertices $A$, $B$, and $C$ to their opposite sides, respectively. Let $D$ be the point where the incircle of $\triangle ABC$ is tangent to side $ BC $. Denote the incenter and circumcenter of $\triangle ABC$ as $I$ and $O$, respectively. Let $K$ be the intersection of line $IO$ and line $BC$. Let $Q$ be the point where the ray $IH_0$ intersects the circumcircle of $\triangle ABC$ again. Let $X$ be the point where the line $ QD $ intersects the circumcircle of $\triangle ABC$ at a point other than $Q$.
Let $Y$ be the point where the circle that touches rays $AB$, $AC$, and is also externally tangent to the circumcircle of $\triangle ABC$, touches the circumcircle of $ \triangle ABC$. Prove that if segment $EF$ is tangent to the incircle of $ \triangle ABC$, then $X$, $Y$, and $K$ are collinear.
-/
open Affine.Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The set of points forming the ray $\overrightarrow{p₁ p₂}$. -/
def ray (p₁ p₂ : ℝ²) : Set ℝ² :=
  { AffineMap.lineMap p₁ p₂ t | (t : ℝ) (_ : t ≥ 0) }

theorem PBAdvanced015
    -- a triangle ABC
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    -- ABC is acute
    (h_acute : AcuteAngled ⟨![A, B, C], tri⟩)
    -- ABC is non-isosceles
    (n_isosceles : [dist A B, dist A C, dist B C].Nodup )
    (H₀ : ℝ²) (hH₀ : H₀ = altitudeFoot ⟨![A, B, C], tri⟩ 0) -- H₀ is the foot from A
    (E : ℝ²) (hE : E = altitudeFoot ⟨![A, B, C], tri⟩ 1) -- E is the foot from B
    (F : ℝ²) (hF : F = altitudeFoot ⟨![A, B, C], tri⟩ 2) -- F is the foot from C
    -- Let $D$ be the point where the incircle of $\triangle ABC$ is tangent to side $ BC $.
    (D : ℝ²) (hD : D = touchpoint ⟨![A, B, C], tri⟩ ∅ 0)
    (I : ℝ²) (hI : I = incenter ⟨![A, B, C], tri⟩) -- I is the incenter
    (O : ℝ²) (hO : O = circumcenter ⟨![A, B, C], tri⟩) -- O is the circumcenter
    -- Let $K$ be the intersection of line $IO$ and line $BC$.
    (K : ℝ²) (hK : Collinear ℝ {K, I, O} ∧ Collinear ℝ {K, B, C})
    -- We denote the circumcircle of ABC as ω
    (ω : Sphere ℝ²) (hω : ω = circumsphere ⟨![A, B, C], tri⟩)
    -- Let $Q$ be the point where the ray $IH_0$ intersects the circumcircle of $\triangle ABC$ again.
    (Q : ℝ²) (hQ : Q ∈ ray I H₀ ∩ ω)
    -- Let $X$ be the point where the line $ QD $ intersects the circumcircle of $\triangle ABC$ at a point other than $Q$.
    (X : ℝ²) (hX : X ≠ Q ∧ X ∈ (affineSpan ℝ {Q, D} ∩ ω : Set ℝ²))
    -- Let $Y$ be the point where the circle that touches rays $AB$, $AC$, and is also externally tangent to the circumcircle of $\triangle ABC$, touches the circumcircle of $ \triangle ABC$.
    (Y : ℝ²) (ωY : Sphere ℝ²) (hY :
      ωY.IsTangent (affineSpan ℝ {A, B}) ∧
      ωY.IsTangent (affineSpan ℝ {A, C}) ∧
      ωY.IsExtTangentAt ω Y ∧
      (affineSpan ℝ {A, ωY.center}).SOppSide B C) -- ensure ωY is in the angle BAC
    -- $EF$ is tangent to the incircle of $ \triangle ABC$
    (h : (insphere ⟨![A, B, C], tri⟩).IsTangent (affineSpan ℝ {E, F}))
    -- then $X$, $Y$, and $K$ are collinear.
    : Collinear ℝ {X, Y, K} := by 
  obtain ⟨r, m, n, Φ, hr, hrpos, hm, hn, hp, hd, hD', hI0, hI1, hB0, hB1,
    hC0, hC1, hA0, hA1⟩ := LeanFlowProofs.pb015_normalize A B C tri
  rw [← hD] at hD'
  rw [← hI] at hI0 hI1
  have dsq (U V : ℝ²) :
      (Φ U 0 - Φ V 0)^2 + (Φ U 1 - Φ V 1)^2 = (dist U V / r)^2 := by
    rw [← hd]
    simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]
  have ip (U V W : ℝ²) :
      inner ℝ (Φ U - Φ W) (Φ V - Φ W) = inner ℝ (U - W) (V - W) / r^2 := by
    simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
      sub_sub_sub_cancel_right, ← dist_eq_norm, hd]
    ring
  have ip0 (U V W : ℝ²) (hi : inner ℝ (U - W) (V - W) = 0) :
      (Φ U 0 - Φ W 0) * (Φ V 0 - Φ W 0) +
      (Φ U 1 - Φ W 1) * (Φ V 1 - Φ W 1) = 0 := by
    have hh := ip U V W
    rw [hi, zero_div] at hh
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hh
  have lineparam (U V W : ℝ²) (hw : W ∈ affineSpan ℝ {U,V}) :
      ∃ t : ℝ, Φ W = t • (Φ V - Φ U) + Φ U := by
    rw [← vsub_vadd W U, vadd_left_mem_affineSpan_pair] at hw
    obtain ⟨t, ht⟩ := hw
    have he : W = AffineMap.lineMap U V t := by
      rw [AffineMap.lineMap_apply, ht, vsub_vadd]
    refine ⟨t, ?_⟩
    rw [he, Φ.apply_lineMap, AffineMap.lineMap_apply]
    rfl
  have lineeq (U V W : ℝ²) (a b c : ℝ)
      (hU : a * Φ U 0 + b * Φ U 1 + c = 0)
      (hV : a * Φ V 0 + b * Φ V 1 + c = 0)
      (hw : W ∈ affineSpan ℝ {U,V}) : a * Φ W 0 + b * Φ W 1 + c = 0 := by
    obtain ⟨t, ht⟩ := lineparam U V W hw
    rw [ht]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    linear_combination (1-t) * hU + t * hV
  let T : Affine.Simplex ℝ ℝ² 2 := ⟨![A,B,C],tri⟩
  set_option maxHeartbeats 2000000 in
  have hEFmem : E ∈ affineSpan ℝ {A,C} ∧ F ∈ affineSpan ℝ {A,B} ∧
      H₀ ∈ affineSpan ℝ {B,C} := by
    have h0 := T.altitudeFoot_mem_affineSpan_image_compl 0
    have h1 := T.altitudeFoot_mem_affineSpan_image_compl 1
    have h2 := T.altitudeFoot_mem_affineSpan_image_compl 2
    have im0 : T.points '' ({0}ᶜ : Set (Fin 3)) = {B,C} := by
      have hc : ({0}ᶜ : Set (Fin 3)) = {1,2} := by ext i; fin_cases i <;> decide
      rw [hc, Set.image_pair]; rfl
    have im1 : T.points '' ({1}ᶜ : Set (Fin 3)) = {A,C} := by
      have hc : ({1}ᶜ : Set (Fin 3)) = {0,2} := by ext i; fin_cases i <;> decide
      rw [hc, Set.image_pair]; rfl
    have im2 : T.points '' ({2}ᶜ : Set (Fin 3)) = {A,B} := by
      have hc : ({2}ᶜ : Set (Fin 3)) = {0,1} := by ext i; fin_cases i <;> decide
      rw [hc, Set.image_pair]; rfl
    rw [im0] at h0
    rw [im1] at h1
    rw [im2] at h2
    simpa only [T, ← hE, ← hF, ← hH₀] using And.intro h1 (And.intro h2 h0)
  have hden : m*n-1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hden' : n*m-1 ≠ 0 := by rwa [mul_comm]
  have hAB (W : ℝ²) (hw : W ∈ affineSpan ℝ {A,B}) :
      2*m*Φ W 0 + (1-m^2)*Φ W 1 + 2*m^2 = 0 := by
    apply lineeq A B W (2*m) (1-m^2) (2*m^2) _ _ hw
    · rw [hA0, hA1]; field_simp [hden]; ring
    · rw [hB0, hB1]; ring
  have hAC (W : ℝ²) (hw : W ∈ affineSpan ℝ {A,C}) :
      -2*n*Φ W 0 + (1-n^2)*Φ W 1 + 2*n^2 = 0 := by
    apply lineeq A C W (-2*n) (1-n^2) (2*n^2) _ _ hw
    · rw [hA0, hA1]; field_simp [hden, hden']; ring
    · rw [hC0, hC1]; ring
  have hH1 : Φ H₀ 1 = 0 := by
    have hh := lineeq B C H₀ 0 1 0 (by simp [hB1]) (by simp [hC1]) hEFmem.2.2
    simpa using hh
  have hipfoot (i j : Fin 3) (hij : i ≠ j) :
      inner ℝ (T.points j - T.altitudeFoot i) (T.points i - T.altitudeFoot i) = 0 :=
    T.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero hij
  have hipE0 := ip0 A B E (by simpa [T, hE] using hipfoot 1 0 (by decide))
  have hipE2 := ip0 C B E (by simpa [T, hE] using hipfoot 1 2 (by decide))
  have hipF0 := ip0 A C F (by simpa [T, hF] using hipfoot 2 0 (by decide))
  have hipF1 := ip0 B C F (by simpa [T, hF] using hipfoot 2 1 (by decide))
  have hipH1 := ip0 B A H₀ (by simpa [T, hH₀] using hipfoot 0 1 (by decide))
  have hipH2 := ip0 C A H₀ (by simpa [T, hH₀] using hipfoot 0 2 (by decide))
  simp only [hA0,hA1,hB0,hB1,hC0,hC1,hH1] at hipE0 hipE2 hipF0 hipF1 hipH1 hipH2
  have hH0 : Φ H₀ 0 = -(n-m)/(m*n-1) := by
    have hz : (m+n)*(Φ H₀ 0 + (n-m)/(m*n-1)) = 0 := by
      linear_combination hipH1 - hipH2
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (add_pos hm hn))
    simpa only [neg_div] using (eq_neg_of_add_eq_zero_left this)
  have hEperp : (1-n^2)*(Φ E 0+m)+2*n*Φ E 1=0 := by
    have hz : m * ((1-n^2)*(Φ E 0+m)+2*n*Φ E 1) = 0 := by
      field_simp [hden, hden'] at hipE0
      linear_combination (m*n-1)*hipE2 - hipE0
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hm)
  have hFperp : (1-m^2)*(Φ F 0-n)-2*m*Φ F 1=0 := by
    have hz : n * ((1-m^2)*(Φ F 0-n)-2*m*Φ F 1) = 0 := by
      field_simp [hden, hden'] at hipF0
      linear_combination hipF0 - (m*n-1)*hipF1
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hn)
  obtain ⟨hEl,hFl,hab,hnorm⟩ := LeanFlowProofs.pb015_orthic_equations m n (Φ E 0) (Φ E 1)
    (Φ F 0) (Φ F 1) hm hn hp (hAC E hEFmem.1) hEperp (hAB F hEFmem.2.1) hFperp
  have tmap (s : Sphere ℝ²) (L : AffineSubspace ℝ ℝ²) (hs : s.IsTangent L) :
      (⟨Φ s.center, s.radius/r⟩ : Sphere ℝ²).IsTangent (L.map Φ.toAffineMap) := by
    obtain ⟨P, hP⟩ := hs
    refine ⟨Φ P, ?_, ?_, ?_⟩
    · change dist (Φ P) (Φ s.center) = s.radius/r
      rw [hd, hP.mem_sphere]
    · exact ⟨P, hP.mem_space, rfl⟩
    · rintro W ⟨V, hV, rfl⟩
      rw [Sphere.mem_orthRadius_iff_inner_left]
      change inner ℝ (Φ V - Φ P) (Φ P - Φ s.center) = 0
      rw [← neg_sub (Φ s.center) (Φ P), inner_neg_right, neg_eq_zero, ip]
      have hz := hP.inner_left_eq_zero_of_mem hV
      change inner ℝ (V-P) (P-s.center) = 0 at hz
      rw [← neg_sub s.center P, inner_neg_right, neg_eq_zero] at hz
      rw [hz, zero_div]
  have linechar (U V : ℝ²) (a b c : ℝ) (huv : U ≠ V)
      (hab : 0 < a^2+b^2)
      (hU : a*U 0+b*U 1+c=0) (hV : a*V 0+b*V 1+c=0) :
      ∀ W : ℝ², W ∈ affineSpan ℝ {U,V} ↔ a*W 0+b*W 1+c=0 := by
    intro W
    rw [← vsub_vadd W U, vadd_left_mem_affineSpan_pair, vsub_vadd]
    change (∃ t : ℝ, t • (V-U) = W-U) ↔ a*W 0+b*W 1+c=0
    constructor
    · rintro ⟨t,ht⟩
      have ht0 := congrArg (fun Z : ℝ² => Z 0) ht
      have ht1 := congrArg (fun Z : ℝ² => Z 1) ht
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at ht0 ht1
      linear_combination -a*ht0 - b*ht1 + (1-t)*hU+t*hV
    · intro hW
      have hdet : (W 0-U 0)*(V 1-U 1) = (W 1-U 1)*(V 0-U 0) := by
        have ha : a*((W 0-U 0)*(V 1-U 1)-(W 1-U 1)*(V 0-U 0))=0 := by
          linear_combination (V 1-U 1)*hW-(W 1-U 1)*hV+(W 1-V 1)*hU
        have hb : b*((W 0-U 0)*(V 1-U 1)-(W 1-U 1)*(V 0-U 0))=0 := by
          linear_combination -(V 0-U 0)*hW+(W 0-U 0)*hV+(V 0-W 0)*hU
        rcases eq_or_ne a 0 with rfl | ha0
        · have hb0 : b ≠ 0 := by intro hh; simp [hh] at hab
          exact sub_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hb0)
        · exact sub_eq_zero.mp ((mul_eq_zero.mp ha).resolve_left ha0)
      by_cases h0 : V 0-U 0=0
      · have h1 : V 1-U 1 ≠ 0 := by
          intro hh
          apply huv
          ext i; fin_cases i <;> dsimp <;> linarith
        refine ⟨(W 1-U 1)/(V 1-U 1), ?_⟩
        ext i; fin_cases i
        · change (W 1-U 1)/(V 1-U 1)*(V 0-U 0)=W 0-U 0
          rw [h0, mul_zero]
          have := (mul_eq_zero.mp (by simpa [h0] using hdet)).resolve_right h1
          linarith
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          exact div_mul_cancel₀ _ h1
      · refine ⟨(W 0-U 0)/(V 0-U 0), ?_⟩
        ext i; fin_cases i
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          exact div_mul_cancel₀ _ h0
        · simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
          rw [div_mul_eq_mul_div, div_eq_iff h0]
          exact hdet
  have hEFne : E ≠ F := by
    intro hef
    obtain ⟨P, hP⟩ := h
    have hPE : P = E := by simpa [← hef] using hP.mem_space
    have hs : dist E I = r := by
      have hh := hP.mem_sphere
      change dist P T.incenter = T.inradius at hh
      simpa [hPE, hI, hr, T] using hh
    have hsq := dsq E I
    rw [hs, div_self (ne_of_gt hrpos), hI0, hI1] at hsq
    have hl := hAB F hEFmem.2.1
    rw [← hef] at hl
    have hr' := hAC E hEFmem.1
    have hy : (m*n-1)*Φ E 1=2*m*n := by
      have hz : (m+n)*((m*n-1)*Φ E 1-2*m*n)=0 := by
        linear_combination -n*hl-m*hr'
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (add_pos hm hn)))
    have hey : 2 < Φ E 1 := by
      by_contra! he
      have hh := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (sub_pos.mpr hp)) (sub_nonpos.mpr he)
      nlinarith only [hy,hh]
    nlinarith only [hsq, hey, sq_nonneg (Φ E 0), sq_nonneg (Φ E 1-2)]
  have hmapline (U V : ℝ²) :
      (affineSpan ℝ {U,V}).map Φ.toAffineMap = affineSpan ℝ {Φ U,Φ V} := by
    rw [AffineSubspace.map_span, Set.image_pair]
    rfl
  have htEF := tmap T.insphere (affineSpan ℝ {E,F}) h
  rw [hmapline] at htEF
  have htsq := LeanFlowProofs.pb015_tangent_line_sq _ _ _ _ _ hab
    (linechar (Φ E) (Φ F) _ _ _ (fun hh => hEFne (Φ.injective hh)) hab hEl hFl) htEF
  change (_ * Φ T.incenter 0 + _ * Φ T.incenter 1 + _)^2 =
    (T.inradius/r)^2 * _ at htsq
  have hiT : T.incenter = I := hI.symm
  have hrT : T.inradius = r := hr.symm
  rw [hiT, hrT, hI0, hI1, div_self (ne_of_gt hrpos)] at htsq
  simp only [mul_zero, zero_add, mul_one, one_pow, one_mul] at htsq
  rw [hnorm] at htsq
  have hrel : (4*(m*n)*(m*n-1)-((n-m)^2+(m*n+1)^2))^2 =
      ((n-m)^2+(m*n+1)^2)^2 := by convert htsq using 1 <;> ring
  obtain ⟨hδ,hp4⟩ := LeanFlowProofs.pb015_tangency_relation (m*n) (n-m) hp hrel
  have hcO : ω.center = O := by rw [hω, hO]; rfl
  have hv (i : Fin 3) : dist (T.points i) O = ω.radius := by
    rw [hO, hω]
    exact T.dist_circumcenter_eq_circumradius i
  have hsB := dsq B O
  have hsC := dsq C O
  have hsA := dsq A O
  have hvA : dist A O = ω.radius := hv 0
  have hvB : dist B O = ω.radius := hv 1
  have hvC : dist C O = ω.radius := hv 2
  rw [hvA, hA0, hA1] at hsA
  rw [hvB, hB0, hB1, zero_sub, neg_sq] at hsB
  rw [hvC, hC0, hC1, zero_sub, neg_sq] at hsC
  have hRnonneg : 0 ≤ ω.radius/r := div_nonneg (by rw [← hvA]; exact dist_nonneg) hrpos.le
  obtain ⟨hO0,hO1,hR⟩ := LeanFlowProofs.pb015_circumcircle_coordinates
    m n (Φ O 0) (Φ O 1) (ω.radius/r) hm hn hp4 hδ hRnonneg hsB hsC hsA
  have circleeq (W : ℝ²) (hw : W ∈ ω) :
      (Φ W 0)^2+(Φ W 1)^2-(n-m)*Φ W 0-Φ W 1-m*n=0 := by
    have hh := dsq W O
    have hw' : dist W O = ω.radius := by
      change dist W ω.center = ω.radius at hw
      rwa [hcO] at hw
    rw [hw', hR, hO0, hO1] at hh
    nlinarith only [hh,hδ]
  have hBCne : B ≠ C := by
    intro hh
    have hh' := congrArg (fun W => Φ W 0) hh
    rw [hB0,hC0] at hh'
    linarith only [hh',hm,hn]
  have hIOne : I ≠ O := by
    intro hh
    have hh' := congrArg (fun W => Φ W 1) hh
    rw [hI1,hO1] at hh'
    norm_num at hh'
  have hKBC : K ∈ affineSpan ℝ {B,C} :=
    hK.2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hBCne
  have hKIO : K ∈ affineSpan ℝ {I,O} :=
    hK.1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hIOne
  have hK1 : Φ K 1=0 := by
    have hh := lineeq B C K 0 1 0 (by simp [hB1]) (by simp [hC1]) hKBC
    simpa using hh
  have hK0 : Φ K 0=n-m := by
    have hh := lineeq I O K 1 (n-m) (-(n-m))
      (by simp [hI0,hI1]) (by rw [hO0,hO1]; ring) hKIO
    rw [hK1] at hh
    linarith only [hh]
  obtain ⟨t,ht,htQ⟩ := hQ.1
  have hQt : Φ Q = t • (Φ H₀-Φ I)+Φ I := by
    rw [← htQ, AffineEquiv.apply_lineMap, AffineMap.lineMap_apply]
    rfl
  have hqx : Φ Q 0 = -t*(n-m)/(m*n-1) := by
    have hh := congrArg (fun W : ℝ² => W 0) hQt
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,hH0,hI0] at hh
    rw [hh]; ring
  have hqy : Φ Q 1 = 1-t := by
    have hh := congrArg (fun W : ℝ² => W 1) hQt
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,hH1,hI1] at hh
    linarith only [hh]
  obtain ⟨v,hvX⟩ := lineparam Q D X hX.2.1
  have hxv : Φ X = (1-v) • Φ Q := by rw [hvX,hD']; module
  have hvne : 1-v ≠ 1 := by
    intro hh
    apply hX.1
    apply Φ.injective
    simpa [hh] using hxv
  have hx0 : Φ X 0 = (1-v)*Φ Q 0 := congrArg (fun W : ℝ² => W 0) hxv
  have hx1 : Φ X 1 = (1-v)*Φ Q 1 := congrArg (fun W : ℝ² => W 1) hxv
  have hxs := circleeq X hX.2.2
  rw [hx0,hx1] at hxs
  obtain ⟨_,_,_,hxx,hxy⟩ := LeanFlowProofs.pb015_secant_coordinates
    (m*n) (n-m) t (1-v) (Φ Q 0) (Φ Q 1) hp4 hδ ht hqx hqy
    (circleeq Q hQ.2) hvne hxs
  have hXcoord : Φ X 0 = m*n*(n-m)/(m*n-1) ∧ Φ X 1=2*(m*n)/(m*n-1) :=
    ⟨hx0.trans hxx, hx1.trans hxy⟩
  have hside : (affineSpan ℝ {Φ A,Φ ωY.center}).SOppSide (Φ B) (Φ C) := by
    rw [← hmapline, Φ.sOppSide_map_iff]
    exact hY.2.2.2
  have hρ : 0 ≤ ωY.radius/r :=
    div_nonneg (ωY.radius_nonneg_of_mem hY.2.2.1.mem_left) hrpos.le
  have hABne : Φ A ≠ Φ B := by
    intro hh
    have hh' := congrArg (fun W : ℝ² => W 1) hh
    rw [hA1,hB1] at hh'
    have hpos : 0 < 2*m*n/(m*n-1) := div_pos (by positivity) (by linarith only [hp])
    linarith only [hh',hpos]
  have hACne : Φ A ≠ Φ C := by
    intro hh
    have hh' := congrArg (fun W : ℝ² => W 1) hh
    rw [hA1,hC1] at hh'
    have hpos : 0 < 2*m*n/(m*n-1) := div_pos (by positivity) (by linarith only [hp])
    linarith only [hh',hpos]
  have hleft : (2*m*Φ ωY.center 0+(1-m^2)*Φ ωY.center 1+2*m^2)^2 =
      (ωY.radius/r)^2*(m^2+1)^2 := by
    have hta := tmap ωY _ hY.1
    rw [hmapline] at hta
    have hh := LeanFlowProofs.pb015_tangent_line_sq _ _ (2*m) (1-m^2) (2*m^2)
      (by positivity) (linechar _ _ _ _ _ hABne (by positivity)
        (hAB A (mem_affineSpan ℝ (by simp)))
        (hAB B (mem_affineSpan ℝ (by simp)))) hta
    dsimp only at hh
    convert hh using 1 <;> ring
  have hright : (-2*n*Φ ωY.center 0+(1-n^2)*Φ ωY.center 1+2*n^2)^2 =
      (ωY.radius/r)^2*(n^2+1)^2 := by
    have hta := tmap ωY _ hY.2.1
    rw [hmapline] at hta
    have hnormal : 0 < (-2*n)^2+(1-n^2)^2 := by nlinarith only [sq_nonneg (1-n^2),sq_pos_of_pos hn]
    have hh := LeanFlowProofs.pb015_tangent_line_sq _ _ (-2*n) (1-n^2) (2*n^2)
      hnormal (linechar _ _ _ _ _ hACne hnormal
        (hAC A (mem_affineSpan ℝ (by simp)))
        (hAC C (mem_affineSpan ℝ (by simp)))) hta
    dsimp only at hh
    convert hh using 1 <;> ring
  obtain ⟨s,hsne,hJ0,hJ1,hρs⟩ := LeanFlowProofs.pb015_internal_bisector
    m n (ωY.radius/r) (Φ A) (Φ B) (Φ C) (Φ ωY.center) hm hn hp hρ
    ⟨hA0,hA1⟩ ⟨hB0,hB1⟩ ⟨hC0,hC1⟩ hleft hright hside
  have hdistJO : dist ωY.center O = ωY.radius+ω.radius := by
    rw [← hcO]
    exact hY.2.2.1.isExtTangent.dist_center
  have hJO := dsq ωY.center O
  rw [hdistJO,add_div,hρs,hR,hJ0,hJ1,hA0,hA1,hO0,hO1] at hJO
  have extcalc (p d z : ℝ) (hd : p-1 ≠ 0) (he : d^2=p^2-4*p-1)
      (hc : ((1-z)*(-d/(p-1))-d/2)^2+((1-z)*(2*p/(p-1))+z-1/2)^2=(|z|+p/2)^2) :
      z^2*(2*p/(p-1)-1)-z*(p+2*p/(p-1))=p*|z| := by
    have hid : ((1-z)*(-d/(p-1))-d/2)^2+((1-z)*(2*p/(p-1))+z-1/2)^2-(|z|+p/2)^2 =
        z^2*(2*p/(p-1)-1)-z*(p+2*p/(p-1))-p*|z| +
        (d^2-(p^2-4*p-1))*((1-z)/(p-1)+1/2)^2 := by
      field_simp [hd]
      nlinarith only [sq_abs z]
    rw [he,sub_self,zero_mul,add_zero,hc,sub_self] at hid
    linarith only [hid]
  have hext := extcalc (m*n) (n-m) s hden hδ (by simpa only [mul_assoc] using hJO)
  obtain ⟨hsval,hspos⟩ := LeanFlowProofs.pb015_external_parameter (m*n) s hp4 hsne hext
  have hpplus : m*n+1 ≠ 0 := by linarith only [hp4]
  have hρval : ωY.radius/r = 2*(m*n)^2/(m*n+1) := by rw [hρs,abs_of_pos hspos,hsval]
  have hJ0val : Φ ωY.center 0=(n-m)*(2*(m*n)+1)/(m*n+1) := by
    rw [hJ0,hA0,hsval]
    field_simp [hden,hpplus]
    ring
  have hJ1val : Φ ωY.center 1= -2*(m*n) := by
    rw [hJ1,hA1,hsval]
    field_simp [hden,hpplus]
    ring
  obtain ⟨w,hw,hwy⟩ := hY.2.2.1.wbtw
  have hwρ : w*(ωY.radius/r+ω.radius/r)=ωY.radius/r := by
    have hh := hY.2.2.1.mem_left
    change dist Y ωY.center=ωY.radius at hh
    rw [← hwy,dist_lineMap_left,Real.norm_eq_abs,abs_of_nonneg hw.1,
      hY.2.2.1.isExtTangent.dist_center] at hh
    have hh' := congrArg (fun z : ℝ => z/r) hh
    simpa only [mul_div_assoc,add_div] using hh'
  have hwval : w=4*(m*n)/(5*(m*n)+1) := by
    rw [hρval,hR] at hwρ
    have h5 : 5*(m*n)+1 ≠ 0 := by linarith only [hp4]
    apply (eq_div_iff h5).2
    field_simp [hpplus] at hwρ
    nlinarith only [hwρ]
  have hYmap : Φ Y = w • (Φ O-Φ ωY.center)+Φ ωY.center := by
    rw [← hwy,AffineEquiv.apply_lineMap,AffineMap.lineMap_apply,hcO]
    rfl
  have hYcoord : Φ Y 0=(n-m)*(4*(m*n)+1)/(5*(m*n)+1) ∧
      Φ Y 1= -2*(m*n)^2/(5*(m*n)+1) := by
    have hy0 := congrArg (fun W : ℝ² => W 0) hYmap
    have hy1 := congrArg (fun W : ℝ² => W 1) hYmap
    simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,
      hJ0val,hJ1val,hO0,hO1,hwval] at hy0 hy1
    have h5 : 5*(m*n)+1 ≠ 0 := by linarith only [hp4]
    constructor
    · rw [hy0]; field_simp [hpplus,h5]; ring
    · rw [hy1]; field_simp [h5]; ring
  have hcol := LeanFlowProofs.pb015_coordinate_collinear (m*n) (n-m) hp4
    (Φ X) (Φ Y) (Φ K) hXcoord hYcoord ⟨hK0,hK1⟩
  obtain ⟨v₀,hv₀⟩ := (collinear_iff_of_mem (by simp : Φ X ∈ ({Φ X,Φ Y,Φ K} : Set ℝ²))).1 hcol
  apply (collinear_iff_of_mem (by simp : X ∈ ({X,Y,K} : Set ℝ²))).2
  refine ⟨Φ.symm.linear v₀,fun P hP => ?_⟩
  have hP' : Φ P ∈ ({Φ X,Φ Y,Φ K} : Set ℝ²) := by
    rcases hP with rfl | hP
    · simp
    rcases hP with rfl | hP
    · simp
    simp only [Set.mem_singleton_iff] at hP
    simp [hP]
  obtain ⟨z,hz⟩ := hv₀ (Φ P) hP'
  refine ⟨z,?_⟩
  have hh := congrArg Φ.symm hz
  simpa only [AffineEquiv.symm_apply_apply,AffineEquiv.map_vadd,LinearEquiv.map_smul] using hh
