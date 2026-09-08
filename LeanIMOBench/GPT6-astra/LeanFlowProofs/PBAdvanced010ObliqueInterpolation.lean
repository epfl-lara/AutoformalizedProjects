import Mathlib

theorem LeanFlowProofs.PBAdvanced010.obliqueInterpolation
    (c d n s t k ell m z : ℝ)
    (hs : s ≠ 0)
    (hkt : k ≠ t)
    (hk : c * k = 2 * s * n)
    (hK : c * k ^ 2 + ell * k + z = 0)
    (hQ : c * t ^ 2 + ell * t + z = 0)
    (hP : d * s ^ 2 + m * s + z = 0) :
    ell = -(2 * s * n + c * t) ∧
      m = -(s * d + 2 * t * n) ∧
      z = 2 * s * t * n := by 
  have hf : (k - t) * (c * k + c * t + ell) = 0 := by
    nlinarith [hK, hQ]
  have he : c * k + c * t + ell = 0 :=
    (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr hkt)
  have hell : ell = -(2 * s * n + c * t) := by linarith
  have hz : z = 2 * s * t * n := by
    nlinarith [congrArg (fun x : ℝ => x * t) hell]
  have hf' : s * (s * d + m + 2 * t * n) = 0 := by
    nlinarith [hP, hz]
  have hm : s * d + m + 2 * t * n = 0 :=
    (mul_eq_zero.mp hf').resolve_left hs
  exact ⟨hell, by linarith, hz⟩
