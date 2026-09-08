import Mathlib

theorem LeanFlowProofs.PBAdvanced027Aux.crossing_obstruction
    (A B C D : EuclideanSpace ℝ (Fin 2))
    (hC : dist A B ^ 2 < dist A C ^ 2 + dist B C ^ 2)
    (hD : dist A B ^ 2 < dist A D ^ 2 + dist B D ^ 2)
    (hA : dist C D ^ 2 < dist C A ^ 2 + dist D A ^ 2)
    (hB : dist C D ^ 2 < dist C B ^ 2 + dist D B ^ 2) :
    (openSegment ℝ A B) ∩ (openSegment ℝ C D) = ∅ := by 
  apply Set.eq_empty_of_forall_notMem
  intro X hX
  rcases hX.1 with ⟨a, b, ha, hb, hab, hXab⟩
  rcases hX.2 with ⟨c, d, hc, hd, hcd, hXcd⟩
  have heq : a • A + b • B = c • C + d • D := hXab.trans hXcd.symm
  have hb' : b = 1-a := by linarith
  have hd' : d = 1-c := by linarith
  subst b
  subst d
  have he (i : Fin 2) : a * A i + (1-a) * B i - c * C i - (1-c) * D i = 0 := by
    have := congrArg (fun Y : EuclideanSpace ℝ (Fin 2) => Y i) heq
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at this
    linarith
  have pos := add_pos (add_pos (mul_pos hc (sub_pos.mpr hC))
    (mul_pos hd (sub_pos.mpr hD)))
    (add_pos (mul_pos ha (sub_pos.mpr hA)) (mul_pos hb (sub_pos.mpr hB)))
  have ident :
      c * (dist A C ^ 2 + dist B C ^ 2 - dist A B ^ 2) +
      (1-c) * (dist A D ^ 2 + dist B D ^ 2 - dist A B ^ 2) +
      (a * (dist C A ^ 2 + dist D A ^ 2 - dist C D ^ 2) +
      (1-a) * (dist C B ^ 2 + dist D B ^ 2 - dist C D ^ 2)) =
      2 * (a * A 0 + (1-a) * B 0 - c * C 0 - (1-c) * D 0) * (A 0 + B 0 - C 0 - D 0) +
      2 * (a * A 1 + (1-a) * B 1 - c * C 1 - (1-c) * D 1) * (A 1 + B 1 - C 1 - D 1) := by
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]
    ring
  rw [he 0, he 1] at ident
  linarith
