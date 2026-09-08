import LeanFlowProofs.PBBasic028.AltitudeFootVectors
import LeanFlowProofs.PBBasic028.InsideTwoLineTangency
import LeanFlowProofs.PBBasic028.MidpointCircleInvariants
import LeanFlowProofs.PBBasic028.NormalizedFrame
import LeanFlowProofs.PBBasic028.SelectSmallTangencyRoot
import LeanFlowProofs.PBBasic028.UnitRayTriangleIncenter
import Mathlib

/-
In $\triangle ABC$ the altitudes $BE$ and $CF$ intersect at $H$. A circle $(W)$ is
externally tangent to the Euler circle $(E)$ of $\triangle ABC$ and also tangent
to the sides $AB$ and $AC$ at $X$ and $Y$, respectively, with
the center of $(W)$ inside $\triangle ABC$. Let $I'$ be the
incenter of $\triangle AEF$. Prove that $AXI'Y$ is a rhombus.
-/
open Real Affine Simplex EuclideanGeometry
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem PBBasic028
    (A B C : ℝ²) (tri : AffineIndependent ℝ ![A, B, C])
    (ω : Sphere ℝ²) -- ω is the 9-point (Euler) circle
    (hω : midpoint ℝ A B ∈ ω ∧ midpoint ℝ B C ∈ ω ∧ midpoint ℝ C A ∈ ω)
    (W : Sphere ℝ²) (X Y : ℝ²) -- W is a circle that
    (hX : W.IsTangentAt X (affineSpan ℝ {A, B})) -- is tangent to AB at X
    (hY : W.IsTangentAt Y (affineSpan ℝ {A, C})) -- is tangent to AC at Y
    (tangent : W.IsExtTangent ω) -- is externally tangent to the 9-point circle
    (inside : W.center ∈ convexHull ℝ {A, B, C}) : -- and the center of W is inside triangle ABC
    let E := altitudeFoot ⟨![A, B, C], tri⟩ 1 -- E is the foot from B
    let F := altitudeFoot ⟨![A, B, C], tri⟩ 2 -- F is the foot from C
    let H := Triangle.orthocenter ⟨![A, B, C], tri⟩ -- H is the orthocenter
    ∀ tri2 : AffineIndependent ℝ ![A, E, F], -- aux assumption to take the incenter
    let I' := incenter ⟨![A, E, F], tri2⟩ -- I' is the incenter of AEF
    -- then all `dist A X`, `dist X I'`, `dist I' Y`, `dist Y A` are equal
    List.Pairwise (· = ·) [dist A X, dist X I', dist I' Y, dist Y A] := by 
  let a := dist B C
  let b := dist A C
  let c := dist A B
  let e := c⁻¹ • (B - A)
  let f := b⁻¹ • (C - A)
  let q := inner ℝ e f
  obtain ⟨ha, hb, hc, hB, hC, he, hf, hql, hqu, hlaw⟩ :=
    LeanFlowProofs.PBBasic028.normalizedFrame A B C tri
  change 0 < a at ha
  change 0 < b at hb
  change 0 < c at hc
  change B - A = c • e at hB
  change C - A = b • f at hC
  change ‖e‖ = 1 at he
  change ‖f‖ = 1 at hf
  change -1 < q at hql
  change q < 1 at hqu
  change a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * q at hlaw
  obtain ⟨k, hk, hinside, hW, hXX, hYY, hr, hrsq⟩ :=
    LeanFlowProofs.PBBasic028.insideTwoLineTangency A B C e f b c q hb hc
      hB hC he hf rfl hql hqu W X Y hX hY inside
  obtain ⟨hR, hne, hnf, hpower, hRsq⟩ :=
    LeanFlowProofs.PBBasic028.midpointCircleInvariants A B C e f a b c q hb hc
      hB hC he hf rfl hlaw ω hω
  have hprod : 4 * ω.radius * W.radius = a * k := by
    have hs : (4 * ω.radius * W.radius) ^ 2 = (a * k) ^ 2 := by
      calc
        _ = (16 * ω.radius ^ 2 * (1 - q ^ 2)) * k ^ 2 := by rw [mul_pow, mul_pow, hrsq] <;> ring
        _ = _ := by rw [hRsq]; ring
    nlinarith [mul_nonneg hR hr, mul_nonneg (le_of_lt ha) hk]
  have hd := tangent.dist_center
  have hn : ‖e + f‖ ^ 2 = 2 + 2 * q := by
    rw [norm_add_sq_real, he, hf]
    dsimp [q]
    ring
  have hninner : inner ℝ (ω.center - A) (k • (e + f)) =
      k * ((b + c) / 4 + (b + c) * q / 2) := by
    rw [inner_smul_right, inner_add_right, hne, hnf]
    ring
  have hdist : dist W.center ω.center ^ 2 =
      ‖ω.center - A‖ ^ 2 + k ^ 2 * (2 + 2 * q) -
      2 * (k * ((b + c) / 4 + (b + c) * q / 2)) := by
    rw [dist_comm, dist_eq_norm]
    have hv : ω.center - W.center = (ω.center - A) - k • (e + f) := by
      rw [← hW]; abel
    rw [hv, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hn, hninner]
    ring
  have hquad : 2 * k ^ 2 * (1 + q) ^ 2 -
      k * ((b + c) * (1 + 2 * q) + a) + b * c * q = 0 := by
    rw [hd] at hdist
    nlinarith only [hdist, hpower, hrsq, hprod]
  obtain ⟨hroot, hq0⟩ := LeanFlowProofs.PBBasic028.selectSmallTangencyRoot
    a b c q k ha hb hc hql hqu hlaw hk hinside hquad
  obtain ⟨hE, hF⟩ := LeanFlowProofs.PBBasic028.altitudeFootVectors
    A B C e f b c q tri hB hC he hf rfl
  let E := altitudeFoot (⟨![A, B, C], tri⟩ : Simplex ℝ ℝ² 2) 1
  let F := altitudeFoot (⟨![A, B, C], tri⟩ : Simplex ℝ ℝ² 2) 2
  change E - A = (c * q) • f at hE
  change F - A = (b * q) • e at hF
  change ∀ tri2 : AffineIndependent ℝ ![A, E, F], _
  intro tri2
  let I := incenter (⟨![A, E, F], tri2⟩ : Simplex ℝ ℝ² 2)
  change List.Pairwise (· = ·) [dist A X, dist X I, dist I Y, dist Y A]
  have hqpos : 0 < q := by
    have hneEA : E ≠ A := by
      intro hh
      have hi := tri2.injective
      have heq : (![A, E, F] : Fin 3 → ℝ²) 1 = ![A, E, F] 0 := by simpa using hh
      have := hi heq
      norm_num at this
    have hqne : q ≠ 0 := by
      intro hz
      rw [hz, mul_zero, zero_smul, sub_eq_zero] at hE
      exact hneEA hE
    exact lt_of_le_of_ne hq0 (Ne.symm hqne)
  have hEF : dist E F = q * a := by
    have hv : E - F = (c * q) • f - (b * q) • e := by
      rw [← hE, ← hF]; abel
    have hsq : dist E F ^ 2 = (q * a) ^ 2 := by
      rw [dist_eq_norm, hv, norm_sub_sq_real]
      simp only [norm_smul, Real.norm_eq_abs, he, hf, mul_one, sq_abs,
        inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
      rw [real_inner_comm e f]
      change (c * q) ^ 2 - 2 * (b * q * (c * q * q)) + (b * q) ^ 2 = (q * a) ^ 2
      nlinarith only [congrArg (fun x : ℝ => q ^ 2 * x) hlaw]
    nlinarith only [hsq, dist_nonneg (x := E) (y := F), mul_pos hqpos ha]
  have hI := LeanFlowProofs.PBBasic028.unitRayTriangleIncenter
    A E F e f (c * q) (b * q) (mul_pos hc hqpos) (mul_pos hb hqpos)
      he hf hE hF tri2
  change I - A = _ at hI
  have hcoef : (c * q) * (b * q) / (dist E F + c * q + b * q) = k * (1 + q) := by
    rw [hEF]
    apply (div_eq_iff (by positivity : q * a + c * q + b * q ≠ 0)).2
    nlinarith only [congrArg (fun x : ℝ => q * x) hroot]
  rw [hcoef] at hI
  have hXI : I - X = (k * (1 + q)) • f := by
    calc
      I - X = (I - A) - (X - A) := by abel
      _ = _ := by rw [hI, hXX, smul_add]; abel
  have hIY : I - Y = (k * (1 + q)) • e := by
    calc
      I - Y = (I - A) - (Y - A) := by abel
      _ = _ := by rw [hI, hYY, smul_add]; abel
  have d1 : dist A X = |k * (1 + q)| := by
    rw [dist_comm, dist_eq_norm, hXX, norm_smul, Real.norm_eq_abs, he, mul_one]
  have d2 : dist X I = |k * (1 + q)| := by
    rw [dist_comm, dist_eq_norm, hXI, norm_smul, Real.norm_eq_abs, hf, mul_one]
  have d3 : dist I Y = |k * (1 + q)| := by
    rw [dist_eq_norm, hIY, norm_smul, Real.norm_eq_abs, he, mul_one]
  have d4 : dist Y A = |k * (1 + q)| := by
    rw [dist_eq_norm, hYY, norm_smul, Real.norm_eq_abs, hf, mul_one]
  simp [d1, d2, d3, d4]

