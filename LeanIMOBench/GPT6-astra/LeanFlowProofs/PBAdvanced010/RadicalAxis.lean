import Mathlib

theorem LeanFlowProofs.PBAdvanced010.radicalAxisDet
    (px py tx ty jx jy d e g : ℝ)
    (hne : d ≠ 0 ∨ e ≠ 0 ∨ g ≠ 0)
    (hP : d * px + e * py + g = 0)
    (hT : d * tx + e * ty + g = 0)
    (hJ : d * jx + e * jy + g = 0) :
    (px - jx) * (ty - jy) - (py - jy) * (tx - jx) = 0 := by 
  by_cases hd : d = 0
  · by_cases he : e = 0
    · have hg : g = 0 := by simpa [hd, he] using hJ
      rcases hne with h | h | h
      · exact (h hd).elim
      · exact (h he).elim
      · exact (h hg).elim
    · apply (mul_eq_zero.mp (show e * ((px - jx) * (ty - jy) - (py - jy) * (tx - jx)) = 0 from ?_)).resolve_left he
      linear_combination (px - jx) * (hT - hJ) - (tx - jx) * (hP - hJ)
  · apply (mul_eq_zero.mp (show d * ((px - jx) * (ty - jy) - (py - jy) * (tx - jx)) = 0 from ?_)).resolve_left hd
    linear_combination (ty - jy) * (hP - hJ) - (py - jy) * (hT - hJ)
