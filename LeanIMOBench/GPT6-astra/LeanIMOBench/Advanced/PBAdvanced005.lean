import LeanFlowProofs.PBAdvanced005.InterceptBranch
import LeanFlowProofs.PBAdvanced005.ObliqueGram
import LeanFlowProofs.PBAdvanced005.PartnerTransfer
import LeanFlowProofs.PBAdvanced005.PositiveConeInterior
import LeanFlowProofs.PBAdvanced005.SectorCoordinates
import Mathlib

/-
Let $\angle XYZ$ be an acute angle with $\angle XYZ \ne 60^\circ$, and let $A$ be a point inside $\angle XYZ$. Prove that there exists $D\ne A$ inside $\angle XYZ$ and $\theta\in (0,2\pi )$ satisfying the following condition:

For points $B$ and $C$ on the rays $\overrightarrow{YX}$ and $\overrightarrow{YZ}$ respectively, then
\[
\angle BAC = \angle XYZ \quad \implies \quad \angle BDC = \theta.
\]
-/

open EuclideanGeometry Real

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation degrees "ᵒ" => (degrees * π / 180)

-- Points involved in the problem are now of type `Point`
variable (X Y Z A : ℝ²)

/-- The set of points forming the ray $\overrightarrow{p₁ p₂}$. -/
def raySet (p₁ p₂ : ℝ²) : Set ℝ² :=
  { AffineMap.lineMap p₁ p₂ t | (t : ℝ) (_ : t ≥ 0) }

/-- A point `A` is in the interior of $\angle XYZ$ if it satisfies the angle addition property
and is not on the boundary. -/
def InsideAngle (A X Y Z : ℝ²) : Prop :=
  A ∉ raySet Y X ∧ A ∉ raySet Y Z ∧
  ∠ X Y A + ∠ A Y Z = ∠ X Y Z

/--
The formal statement of the geometric problem (PB-Advanced-005).
-/
theorem PBAdvanced005
    (hxy : X ≠ Y) (hzy : Z ≠ Y)
    (h_acute : ∠ X Y Z < 90ᵒ)
    (h_not_60 : ∠ X Y Z ≠ 60ᵒ)
    (hA_interior : InsideAngle A X Y Z) :
    ∃ D : ℝ², D ≠ A ∧ InsideAngle D X Y Z ∧
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * π ∧
    ∀ B C : ℝ²,
      (B ∈ raySet Y X) →
      (C ∈ raySet Y Z) →
      (∠ B A C = ∠ X Y Z) →
      (∠ B D C = θ) := by set_option maxHeartbeats 1600000 in
  let u := ‖X - Y‖⁻¹ • (X - Y)
  let v := ‖Z - Y‖⁻¹ • (Z - Y)
  have hx : 0 < ‖X - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hz : 0 < ‖Z - Y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
  have hu : ‖u‖ = 1 := by simp [u, norm_smul, abs_of_pos hx, ne_of_gt hx]
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, abs_of_pos hz, ne_of_gt hz]
  have ang (P Q : ℝ²) : ∠ P Y Q = ∠ (P - Y) 0 (Q - Y) := by
    simp [EuclideanGeometry.angle]
  have au (w : ℝ²) : ∠ u 0 w = ∠ (X - Y) 0 w := by
    simp [EuclideanGeometry.angle, u, InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr hx)]
  have av (w : ℝ²) : ∠ w 0 v = ∠ w 0 (Z - Y) := by
    simp [EuclideanGeometry.angle, v, InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr hz)]
  have huvangle : ∠ u 0 v = ∠ X Y Z := by rw [au, av, ang]
  have ray (P Q : ℝ²) : P ∈ raySet Y Q ↔ ∃ t : ℝ, 0 ≤ t ∧ P - Y = t • (Q - Y) := by
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [AffineMap.lineMap_apply_module]; module⟩
    · rintro ⟨t, ht, he⟩
      refine ⟨t, ht, ?_⟩
      have hP : P = t • (Q - Y) + Y := sub_eq_iff_eq_add.mp he
      rw [hP]
      simp [AffineMap.lineMap_apply_module]
      module
  have rayu (P : ℝ²) : P ∈ raySet Y X ↔ ∃ t : ℝ, 0 ≤ t ∧ P - Y = t • u := by
    rw [ray]
    constructor
    · rintro ⟨t, ht, he⟩
      refine ⟨t * ‖X - Y‖, mul_nonneg ht hx.le, ?_⟩
      simpa [u, smul_smul, ne_of_gt hx] using he
    · rintro ⟨t, ht, he⟩
      exact ⟨t * ‖X - Y‖⁻¹, mul_nonneg ht (inv_nonneg.mpr hx.le), by simpa [u, smul_smul] using he⟩
  have rayv (P : ℝ²) : P ∈ raySet Y Z ↔ ∃ t : ℝ, 0 ≤ t ∧ P - Y = t • v := by
    rw [ray]
    constructor
    · rintro ⟨t, ht, he⟩
      refine ⟨t * ‖Z - Y‖, mul_nonneg ht hz.le, ?_⟩
      simpa [v, smul_smul, ne_of_gt hz] using he
    · rintro ⟨t, ht, he⟩
      exact ⟨t * ‖Z - Y‖⁻¹, mul_nonneg ht (inv_nonneg.mpr hz.le), by simpa [v, smul_smul] using he⟩
  have hacute : ∠ u 0 v < π / 2 := by rw [huvangle]; linarith
  obtain ⟨hpos, p, q, hp, hq, ha⟩ := LeanFlowProofs.PBAdvanced005.sectorCoordinates u v (A - Y) hu hv hacute
    (fun t ht he => hA_interior.1 ((rayu A).mpr ⟨t, ht, he⟩))
    (fun t ht he => hA_interior.2.1 ((rayv A).mpr ⟨t, ht, he⟩))
    (by rw [au, av, ← ang, ← ang, huvangle]; exact hA_interior.2.2)
  let α := ∠ u 0 v
  let k := cos α
  have hk0 : 0 < k := cos_pos_of_mem_Ioo ⟨by dsimp [α]; linarith [pi_pos], hacute⟩
  have hk1 : k < 1 := by
    have hh := strictAntiOn_cos ⟨(le_refl 0), pi_pos.le⟩ ⟨hpos.le, le_trans hacute.le (by linarith [pi_pos])⟩ hpos
    simpa [k, α] using hh
  have hik : inner ℝ u v = k := by
    simpa [EuclideanGeometry.angle, hu, hv, k, α] using (InnerProductGeometry.cos_angle u v).symm
  have hsq : 0 < 1 - k ^ 2 := by nlinarith
  let H := 2 * k
  have hH : 0 < H := by dsimp [H]; positivity
  let r := q / H
  let w := p / H
  have hr : 0 < r := div_pos hq hH
  have hw : 0 < w := div_pos hp hH
  let D := Y + (r • u + w • v)
  have hd : D - Y = r • u + w • v := by dsimp [D]; abel
  obtain ⟨hdu, hdv, hda⟩ := LeanFlowProofs.PBAdvanced005.positiveConeInterior u v hu hv hpos hacute r w hr hw
  have hDi : InsideAngle D X Y Z := by
    refine ⟨?_, ?_, ?_⟩
    · intro hh; obtain ⟨t, ht, he⟩ := (rayu D).mp hh; exact hdu t ht (hd.symm.trans he)
    · intro hh; obtain ⟨t, ht, he⟩ := (rayv D).mp hh; exact hdv t ht (hd.symm.trans he)
    · rw [ang X D, ang D Z, ← au, ← av, hd, ← huvangle]; exact hda
  have hinj (a b c d : ℝ) (he : a • u + b • v = c • u + d • v) : a = c ∧ b = d := by
    have hiu := congrArg (fun z => inner ℝ u z) he
    have hiv := congrArg (fun z => inner ℝ v z) he
    have huu : inner ℝ u u = 1 := by simpa [hu] using real_inner_self_eq_norm_sq u
    have hvv : inner ℝ v v = 1 := by simpa [hv] using real_inner_self_eq_norm_sq v
    have hvi : inner ℝ v u = k := by rw [real_inner_comm]; exact hik
    simp only [inner_add_right, inner_smul_right, huu, hvv, hik, hvi, mul_one] at hiu hiv
    constructor <;> nlinarith [sq_nonneg (a-c), sq_nonneg (b-d)]
  have hne : D ≠ A := by
    intro he
    have hh := hinj r w p q (hd.symm.trans ((congrArg (fun z => z - Y) he).trans ha))
    have eq1 : q = p * H := (div_eq_iff (ne_of_gt hH)).mp hh.1
    have eq2 : p = q * H := (div_eq_iff (ne_of_gt hH)).mp hh.2
    have HH : H = 1 := by nlinarith
    have hkhalf : k = 1 / 2 := by dsimp [H] at HH; linarith
    have hal : α = π / 3 := by
      apply (strictAntiOn_cos.injOn ⟨hpos.le, by linarith [pi_pos]⟩ ⟨by positivity, by linarith [pi_pos]⟩)
      simpa [k, cos_pi_div_three] using hkhalf
    apply h_not_60
    rw [← huvangle]
    change α = _
    rw [hal]; ring
  refine ⟨D, hne, hDi, π - 2 * α, by dsimp [α]; linarith, by dsimp [α]; linarith [pi_pos], ?_⟩
  intro B C hB hC hang
  obtain ⟨t, ht, hb⟩ := (rayu B).mp hB
  obtain ⟨s, hs, hc⟩ := (rayv C).mp hC
  have hba : B - A = t • u - (p • u + q • v) := by rw [← hb, ← ha]; abel
  have hca : C - A = s • v - (p • u + q • v) := by rw [← hc, ← ha]; abel
  have hbd : B - D = t • u - (r • u + w • v) := by rw [← hb, ← hd]; abel
  have hcd : C - D = s • v - (r • u + w • v) := by rw [← hc, ← hd]; abel
  have hBA : B - A ≠ 0 := sub_ne_zero.mpr (fun e => hA_interior.1 (e ▸ hB))
  have hCA : C - A ≠ 0 := sub_ne_zero.mpr (fun e => hA_interior.2.1 (e ▸ hC))
  have hBD : B - D ≠ 0 := sub_ne_zero.mpr (fun e => hDi.1 (e ▸ hB))
  have hCD : C - D ≠ 0 := sub_ne_zero.mpr (fun e => hDi.2.1 (e ▸ hC))
  let N := ‖B - A‖ * ‖C - A‖
  let M := ‖B - D‖ * ‖C - D‖
  have hN : 0 < N := mul_pos (norm_pos_iff.mpr hBA) (norm_pos_iff.mpr hCA)
  have hM : 0 < M := mul_pos (norm_pos_iff.mpr hBD) (norm_pos_iff.mpr hCD)
  let F := t * s - t * q - s * p
  let T := p ^ 2 + q ^ 2 + 2 * k * p * q - t * (p + k * q) - s * (q + k * p) + k * t * s
  have gram := LeanFlowProofs.PBAdvanced005.obliqueGramIdentity u v k p q t s hu hv hik
  change inner ℝ (t • u - (p • u + q • v)) (s • v - (p • u + q • v)) = T ∧ _ = T ^ 2 + (1-k^2)*F^2 at gram
  rw [← hba, ← hca] at gram
  have hTN : T = k * N := by
    rw [← gram.1]
    have hh := InnerProductGeometry.cos_angle_mul_norm_mul_norm (B-A) (C-A)
    have haeq : InnerProductGeometry.angle (B-A) (C-A) = α := by
      change ∠ B A C = α
      exact hang.trans huvangle.symm
    rw [haeq] at hh
    exact hh.symm
  have hNF : N = |F| := by
    have hsquare : N^2 = F^2 := by
      have gg := gram.2
      change N^2 = _ at gg
      rw [hTN] at gg
      nlinarith only [gg, hsq]
    nlinarith only [hsquare, sq_abs F, abs_nonneg F, hN]
  have hF : F ≠ 0 := by intro he; rw [he, abs_zero] at hNF; linarith
  have branch := LeanFlowProofs.PBAdvanced005.admissibleInterceptBranch k p q t s hk0 hk1 hp hq ht hs hF (hTN.trans (by rw [hNF]))
  dsimp only at branch
  have trans := LeanFlowProofs.PBAdvanced005.partnerInterceptTransfer k p q t s hk0 hk1 hp hq branch.2.1 branch.2.2.1 branch.2.2.2.1 branch.2.2.2.2
  let G := t*s-t*w-s*r
  let S := r^2+w^2+2*k*r*w-t*(r+k*w)-s*(w+k*r)+k*t*s
  change G < 0 ∧ S = (k - 1 / H) * G ∧ S^2+(1-k^2)*G^2 = G^2/H^2 at trans
  have gramD := LeanFlowProofs.PBAdvanced005.obliqueGramIdentity u v k r w t s hu hv hik
  change inner ℝ (t • u - (r • u + w • v)) (s • v - (r • u + w • v)) = S ∧ _ = S ^ 2 + (1-k^2)*G^2 at gramD
  rw [← hbd, ← hcd] at gramD
  have hMG : M * H = -G := by
    have gg := gramD.2.trans trans.2.2
    change M^2 = G^2/H^2 at gg
    have hh : M^2*H^2 = G^2 := (eq_div_iff (pow_ne_zero 2 (ne_of_gt hH))).mp gg
    nlinarith only [hh, mul_pos hM hH, trans.1]
  have hcos : cos (∠ B D C) = 1 - 2*k^2 := by
    have cc := InnerProductGeometry.cos_angle_mul_norm_mul_norm (B-D) (C-D)
    change cos (∠ B D C) * M = _ at cc
    rw [gramD.1, trans.2.1] at cc
    have hh : (cos (∠ B D C) * M) * H = (k*H-1)*G := by
      rw [cc]; field_simp
    have hG : G = -(M * H) := by linarith only [hMG]
    rw [hG] at hh
    apply mul_right_cancel₀ (ne_of_gt (mul_pos hM hH))
    calc
      cos (∠ B D C) * (M * H) = (k * H - 1) * -(M * H) := by simpa [mul_assoc] using hh
      _ = (1 - 2*k^2) * (M * H) := by dsimp [H]; ring
  apply strictAntiOn_cos.injOn ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩ ⟨by dsimp [α]; linarith, by dsimp [α]; linarith⟩
  rw [hcos, cos_sub, cos_pi, sin_pi, cos_two_mul]
  dsimp [k]
  ring
