import Mathlib

theorem LeanFlowProofs.PBBasic028.midpointCircleInvariants
    (A B C e f : EuclideanSpace ℝ (Fin 2))
    (a b c q : ℝ)
    (hb : 0 < b) (hc : 0 < c)
    (hB : B - A = c • e) (hC : C - A = b • f)
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hq : inner ℝ e f = q)
    (hlaw : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * q)
    (ω : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (hω : midpoint ℝ A B ∈ ω ∧
      midpoint ℝ B C ∈ ω ∧ midpoint ℝ C A ∈ ω) :
    let n : EuclideanSpace ℝ (Fin 2) := ω.center - A
    0 ≤ ω.radius ∧
      inner ℝ n e = c / 4 + b * q / 2 ∧
      inner ℝ n f = b / 4 + c * q / 2 ∧
      ‖n‖ ^ 2 - ω.radius ^ 2 = b * c * q / 2 ∧
      16 * ω.radius ^ 2 * (1 - q ^ 2) = a ^ 2 := by 
  dsimp only
  let n := ω.center - A
  have hn : ω.center = n + A := by dsimp [n]; abel
  have hB' : B = c • e + A := by rw [← hB]; abel
  have hC' : C = b • f + A := by rw [← hC]; abel
  have hm (U V : EuclideanSpace ℝ (Fin 2)) :
      ω.center - midpoint ℝ (U + A) (V + A) = n - (2:ℝ)⁻¹ • (U + V) := by
    rw [midpoint_eq_smul_add, hn]
    norm_num
    module
  have hd (P : EuclideanSpace ℝ (Fin 2)) (hP : P ∈ ω) :
      inner ℝ (ω.center - P) (ω.center - P) = ω.radius ^ 2 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, EuclideanGeometry.mem_sphere'.mp hP]
  have h1 := hd _ hω.1
  have h2 := hd _ hω.2.1
  have h3 := hd _ hω.2.2
  rw [hB'] at h1
  rw [show ω.center - midpoint ℝ A (c • e + A) = n - (2:ℝ)⁻¹ • (0 + c • e) by simpa using hm 0 (c • e)] at h1
  rw [hB', hC', hm] at h2
  rw [hC'] at h3
  rw [show ω.center - midpoint ℝ (b • f + A) A = n - (2:ℝ)⁻¹ • (b • f + 0) by simpa using hm (b • f) 0] at h3
  have hee : inner ℝ e e = 1 := by simp [real_inner_self_eq_norm_sq, he]
  have hff : inner ℝ f f = 1 := by simp [real_inner_self_eq_norm_sq, hf]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_zero_left, inner_zero_right,
    map_inv₀, map_ofNat, conj_trivial, hee, hff, hq] at h1 h2 h3
  rw [show inner ℝ f e = q by rw [real_inner_comm]; exact hq] at h2
  simp only [show inner ℝ e n = inner ℝ n e from real_inner_comm _ _,
    show inner ℝ f n = inner ℝ n f from real_inner_comm _ _] at h1 h2 h3
  have hne : inner ℝ n e = c / 4 + b * q / 2 := by
    nlinarith
  have hnf : inner ℝ n f = b / 4 + c * q / 2 := by
    nlinarith
  have hp : ‖n‖ ^ 2 - ω.radius ^ 2 = b * c * q / 2 := by
    rw [← real_inner_self_eq_norm_sq]
    nlinarith
  refine ⟨ω.radius_nonneg_of_mem hω.1, hne, hnf, hp, ?_⟩
  have gram :
      (inner ℝ e e * inner ℝ f f - (inner ℝ e f)^2) * inner ℝ n n =
      inner ℝ f f * (inner ℝ n e)^2 + inner ℝ e e * (inner ℝ n f)^2 -
        2 * inner ℝ e f * inner ℝ n e * inner ℝ n f := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
      star_trivial]
    ring
  rw [hee, hff, hq, hne, hnf, real_inner_self_eq_norm_sq] at gram
  nlinarith [congrArg (fun x : ℝ => x * (1 - q^2)) hp]

