import LeanFlowProofs.PBAdvanced016.SideWeights
import Mathlib

theorem LeanFlowProofs.PB016.weighted_frame
    (A B C I : EuclideanSpace ℝ (Fin 2))
    (tri : AffineIndependent ℝ ![A, B, C])
    (hne : dist A B ≠ dist A C)
    (hI : I = Affine.Simplex.incenter ⟨![A, B, C], tri⟩) :
    ∃ r q κ : ℝ,
      ∃ e : (ℝ × ℝ) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2),
        0 < r ∧ 0 < q ∧ r * q < 1 ∧ r ≠ q ∧ 0 < κ ∧
        e (-1, 0) = A ∧ e (0, 0) = I ∧
        e (r, 1 + r) = B ∧ e (q, -1 - q) = C ∧
        (∀ z t : ℝ × ℝ,
          dist (e z) (e t) ^ 2 =
            κ * ((1 - r * q) * (z.1 - t.1) ^ 2 +
              r * q * (z.2 - t.2) ^ 2)) := by set_option maxHeartbeats 800000 in
  {
  have hncol : ¬ Collinear ℝ ({A, B, C} : Set _) :=
    affineIndependent_iff_not_collinear_set.mp tri
  have hab : A ≠ B := by
    intro h
    have := tri.injective (show ![A,B,C] (0 : Fin 3) = ![A,B,C] 1 by simpa using h)
    norm_num at this
  have hac : A ≠ C := by
    intro h
    have := tri.injective (show ![A,B,C] (0 : Fin 3) = ![A,B,C] 2 by simpa using h)
    exact (by decide : (0 : Fin 3) ≠ 2) this
  have hbc : B ≠ C := by
    intro h
    have := tri.injective (show ![A,B,C] (1 : Fin 3) = ![A,B,C] 2 by simpa using h)
    exact (by decide : (1 : Fin 3) ≠ 2) this
  have ht₁ : dist B C < dist A B + dist A C := by
    rw [dist_comm A B]
    apply dist_lt_dist_add_dist_iff.mpr
    intro h
    apply hncol
    simpa [Set.insert_comm] using h.collinear
  have ht₂ : dist A C < dist B C + dist A B := by
    apply lt_of_lt_of_eq (dist_lt_dist_add_dist_iff.mpr (fun h => hncol h.collinear))
    ring
  have ht₃ : dist A B < dist B C + dist A C := by
    rw [dist_comm B C]
    have hset : ({A,C,B} : Set _) = {A,B,C} := by ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    have hh : ¬ Wbtw ℝ A C B := fun h => hncol (hset ▸ h.collinear)
    have hh' := dist_lt_dist_add_dist_iff.mpr hh
    linarith
  let a := dist B C
  let b := dist A C
  let c := dist A B
  let d := a + b + c
  have ha : 0 < a := dist_pos.mpr hbc
  have hb : 0 < b := dist_pos.mpr hac
  have hc : 0 < c := dist_pos.mpr hab
  have hd : 0 < d := by dsimp [d]; positivity
  have hb0 := ne_of_gt hb
  have hc0 := ne_of_gt hc
  have hd0 := ne_of_gt hd
  let r := (a + c - b) / (2 * b)
  let q := (a + b - c) / (2 * c)
  let κ := (2 * b * c / d) ^ 2
  have hr : 0 < r := div_pos (by dsimp [a,b,c]; linarith) (by positivity)
  have hq : 0 < q := div_pos (by dsimp [a,b,c]; linarith) (by positivity)
  have hrq : r * q < 1 := by
    dsimp [r,q]
    rw [div_mul_div_comm, div_lt_one (by positivity : 0 < 2*b*(2*c))]
    have hta : a < b + c := by dsimp [a,b,c]; linarith
    nlinarith [sq_nonneg (b-c), mul_pos (show 0 < b+c-a by linarith) (show 0 < a+b+c by positivity)]
  have hrne : r ≠ q := by
    intro he
    have he' : (a+c-b)*(2*c) = (a+b-c)*(2*b) :=
      (div_eq_div_iff (by positivity) (by positivity)).mp he
    have hbcne : b ≠ c := Ne.symm hne
    apply hbcne
    have : (b-c)*d = 0 := by dsimp [d]; nlinarith [he']
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hd0)
  have hk : 0 < κ := sq_pos_of_pos (by positivity)
  let u := B - A
  let t := C - A
  let v := (b/d) • u + (c/d) • t
  let w := (b/d) • u - (c/d) • t
  have hv : v = I - A := by
    have hi := LeanFlowProofs.PB016.incenter_side_weights A B C tri
    rw [← hI, dist_comm C A] at hi
    change d • (I-A) = b • u + c • t at hi
    calc
      v = d⁻¹ • (b • u + c • t) := by dsimp [v]; simp [smul_add, smul_smul, div_eq_inv_mul]
      _ = I-A := by rw [← hi, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have huu : inner ℝ u u = c^2 := by
    rw [real_inner_self_eq_norm_sq]
    congr 1
    exact (dist_eq_norm B A).symm.trans (dist_comm B A)
  have htt : inner ℝ t t = b^2 := by
    rw [real_inner_self_eq_norm_sq]
    congr 1
    exact (dist_eq_norm C A).symm.trans (dist_comm C A)
  have hut : 2 * inner ℝ u t = c^2 + b^2 - a^2 := by
    have hh : inner ℝ (u-t) (u-t) = a^2 := by
      rw [real_inner_self_eq_norm_sq]
      have : u-t = B-C := by dsimp [u,t]; abel
      rw [this, ← dist_eq_norm]
    rw [inner_sub_left, inner_sub_right u u t, inner_sub_right t u t, huu, htt,
      real_inner_comm t u] at hh
    linarith [real_inner_comm t u]
  have hvw : inner ℝ v w = 0 := by
    dsimp [v,w]
    simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, huu, htt, real_inner_comm t u]
    ring
  have hww : inner ℝ w w = κ * (r*q) := by
    dsimp [w,κ,r,q]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      conj_trivial, huu, htt, real_inner_comm t u]
    field_simp
    nlinarith [hut, real_inner_comm t u]
  have hvv : inner ℝ v v = κ * (1-r*q) := by
    have hh : inner ℝ v v + inner ℝ w w = κ := by
      dsimp [v,w,κ]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, conj_trivial, huu, htt, real_inner_comm t u]
      ring
    rw [hww] at hh
    nlinarith
  let f : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toFun := fun z => z.1 • v + z.2 • w
      map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
      map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply, smul_eq_mul] }
  have hf : ∀ z : ℝ × ℝ, inner ℝ (f z) (f z) = κ * ((1-r*q)*z.1^2 + r*q*z.2^2) := by
    intro z
    change inner ℝ (z.1 • v + z.2 • w) (z.1 • v + z.2 • w) = _
    have hwv : inner ℝ w v = 0 := by rw [real_inner_comm, hvw]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, hvv, hww, hvw, hwv]
    ring
  have hfi : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro z hz
    have hh := hf z
    rw [hz, inner_zero_left] at hh
    have hh' : (1-r*q)*z.1^2 + r*q*z.2^2 = 0 := (mul_eq_zero.mp hh.symm).resolve_left (ne_of_gt hk)
    have hp : 0 < r*q := mul_pos hr hq
    have hp' : 0 < 1-r*q := sub_pos.mpr hrq
    have hz₁ : (1-r*q)*z.1^2 = 0 := le_antisymm (by nlinarith only [hh', mul_nonneg (le_of_lt hp) (sq_nonneg z.2)]) (mul_nonneg (le_of_lt hp') (sq_nonneg z.1))
    have hz₂ : r*q*z.2^2 = 0 := by linarith only [hh', hz₁]
    have hh₁ : z.1^2 = 0 := (mul_eq_zero.mp hz₁).resolve_left (ne_of_gt hp')
    have hh₂ : z.2^2 = 0 := (mul_eq_zero.mp hz₂).resolve_left (ne_of_gt hp)
    exact Prod.ext (by simpa using (sq_eq_zero_iff.mp hh₁)) (by simpa using (sq_eq_zero_iff.mp hh₂))
  have hfs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)))).mp hfi
  let g := LinearEquiv.ofBijective f ⟨hfi,hfs⟩
  let e : (ℝ × ℝ) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    g.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ _ I)
  have he : ∀ z, e z = f z + I := by intro z; change I + f z = f z + I; exact add_comm _ _
  refine ⟨r,q,κ,e,hr,hq,hrq,hrne,hk,?_,?_,?_,?_,?_⟩
  · rw [he]
    change (-1:ℝ) • v + (0:ℝ) • w + I = A
    rw [zero_smul, add_zero, neg_one_smul, hv]
    abel
  · rw [he]
    change (0:ℝ) • v + (0:ℝ) • w + I = I
    simp
  · rw [he]
    change r • v + (1+r) • w + I = B
    have hh : (1+r) • (v+w) = u := by
      have hs : (1+r)*(2*b/d) = 1 := by dsimp [r,d]; field_simp; ring
      have hvw' : v+w = (2*b/d) • u := by dsimp [v,w]; module
      rw [hvw', smul_smul, hs, one_smul]
    have hi : I = v + A := by rw [hv]; abel
    rw [hi]
    calc
      r • v + (1+r) • w + (v+A) = (1+r) • (v+w) + A := by module
      _ = B := by rw [hh]; dsimp [u]; abel
  · rw [he]
    change q • v + (-1-q) • w + I = C
    have hh : (1+q) • (v-w) = t := by
      have hs : (1+q)*(2*c/d) = 1 := by dsimp [q,d]; field_simp; ring
      have hvw' : v-w = (2*c/d) • t := by dsimp [v,w]; module
      rw [hvw', smul_smul, hs, one_smul]
    have hi : I = v + A := by rw [hv]; abel
    rw [hi]
    calc
      q • v + (-1-q) • w + (v+A) = (1+q) • (v-w) + A := by module
      _ = C := by rw [hh]; dsimp [t]; abel
  · intro z t'
    rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, he, he]
    rw [add_sub_add_right_eq_sub, ← map_sub, hf]
    rfl
  }
