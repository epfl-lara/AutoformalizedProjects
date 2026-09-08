import Mathlib

theorem LeanFlowProofs.pb015_tangent_line_sq
    (s : EuclideanGeometry.Sphere (EuclideanSpace ℝ (Fin 2)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (a b c : ℝ)
    (hab : 0 < a ^ 2 + b ^ 2)
    (hL : ∀ P : EuclideanSpace ℝ (Fin 2),
      P ∈ L ↔ a * P 0 + b * P 1 + c = 0)
    (ht : s.IsTangent L) :
    (a * s.center 0 + b * s.center 1 + c) ^ 2 =
      s.radius ^ 2 * (a ^ 2 + b ^ 2) := by 
  obtain ⟨p, hp⟩ := ht
  have hpL := (hL p).1 hp.mem_space
  let q : EuclideanSpace ℝ (Fin 2) := !₂[p 0 + b, p 1 - a]
  have hq : q ∈ L := by
    apply (hL q).2
    change a * (p 0 + b) + b * (p 1 - a) + c = 0
    nlinarith [hpL]
  have ho := hp.inner_left_eq_zero_of_mem hq
  have ho' : b * (p 0 - s.center 0) - a * (p 1 - s.center 1) = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, q, vsub_eq_sub, real_inner_comm,
      mul_comm, sub_eq_add_neg] using ho
  have hd : (p 0 - s.center 0)^2 + (p 1 - s.center 1)^2 = s.radius^2 := by
    have hd := congrArg (fun x : ℝ => x^2)
      (show dist p s.center = s.radius from hp.mem_sphere)
    simpa [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq] using hd
  calc
    (a * s.center 0 + b * s.center 1 + c)^2 =
        (a * (p 0 - s.center 0) + b * (p 1 - s.center 1))^2 := by
          have he : a * s.center 0 + b * s.center 1 + c =
              -(a * (p 0 - s.center 0) + b * (p 1 - s.center 1)) := by linarith
          rw [he, neg_sq]
    _ = ((p 0 - s.center 0)^2 + (p 1 - s.center 1)^2) * (a^2+b^2) := by
      nlinarith [sq_nonneg (b * (p 0 - s.center 0) - a * (p 1 - s.center 1))]
    _ = s.radius^2 * (a^2+b^2) := by rw [hd]
