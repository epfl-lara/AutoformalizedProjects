import Mathlib

theorem LeanFlowProofs.PBBasic026_reflection_model
    (I u v : EuclideanSpace ℝ (Fin 2)) (r t k : ℝ)
    (hr : 0 < r) (hk : 1 < k)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℝ u v = 0) :
    let U := t ^ 2 + (k + 1) ^ 2
    let A := I + r •
      ((-t / (k - 1)) • u + ((k + 1) / (k - 1)) • v)
    EuclideanGeometry.reflection (affineSpan ℝ {A, I}) (I - r • v) =
      I + r •
        ((2 * t * (k + 1) / U) • u +
          ((t ^ 2 - (k + 1) ^ 2) / U) • v) := by 
  intro U A
  have hU : U ≠ 0 := by dsimp [U]; nlinarith [sq_nonneg t, sq_pos_of_pos (show 0 < k+1 by linarith)]
  have hk1 : k - 1 ≠ 0 := by linarith
  let c : ℝ := -(k+1)*(k-1)/U
  let Q := I + c • (A-I)
  have hI : I ∈ affineSpan ℝ {A,I} := subset_affineSpan ℝ _ (by simp)
  have hA : A ∈ affineSpan ℝ {A,I} := subset_affineSpan ℝ _ (by simp)
  have hQ : Q ∈ affineSpan ℝ {A,I} := by
    simpa [Q, vsub_eq_sub, vadd_eq_add, add_comm] using
      (affineSpan ℝ {A,I}).smul_vsub_vadd_mem c hA hI hI
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm, huv]
  have hp : (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A,I}) (I-r • v) : EuclideanSpace ℝ (Fin 2)) = Q := by
    apply EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr
    refine ⟨hQ, ?_⟩
    rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_orthogonal_singleton_iff_inner_right]
    have he : (I-r • v) -ᵥ Q = -r • v - c • (A-I) := by simp only [Q, vsub_eq_sub]; module
    rw [he]
    simp only [vsub_eq_sub, A, add_sub_cancel_left, inner_sub_right,
      inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      huu, hvv, huv, hvu, map_neg, RCLike.conj_to_real]
    dsimp [c, U]
    field_simp
    <;> ring
  rw [EuclideanGeometry.reflection_apply', hp]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp [Q, A, c]
  ext i
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  dsimp [U] at hU ⊢
  field_simp
  <;> ring
