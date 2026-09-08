import Mathlib

theorem LeanFlowProofs.pbbasic025_angleOfOrthogonalSpans
    (A B C D p r s : EuclideanSpace ℝ (Fin 2))
    (horth : inner ℝ (B - A) (D - C) = 0)
    (hpAB : p ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hrAB : r ∈ affineSpan ℝ ({A, B} : Set (EuclideanSpace ℝ (Fin 2))))
    (hpCD : p ∈ affineSpan ℝ ({C, D} : Set (EuclideanSpace ℝ (Fin 2))))
    (hsCD : s ∈ affineSpan ℝ ({C, D} : Set (EuclideanSpace ℝ (Fin 2)))) :
    EuclideanGeometry.angle r p s = Real.pi / 2 := by 
  have hr := AffineSubspace.vsub_mem_direction hrAB hpAB
  have hs := AffineSubspace.vsub_mem_direction hsCD hpCD
  rw [direction_affineSpan, mem_vectorSpan_pair_rev] at hr hs
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := hs
  change InnerProductGeometry.angle (r - p) (s - p) = Real.pi / 2
  change a • (B - A) = r - p at ha
  change b • (D - C) = s - p at hb
  rw [← ha, ← hb]
  simp [InnerProductGeometry.angle, inner_smul_left, inner_smul_right, horth]
