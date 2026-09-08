import LeanFlowProofs.PBAdvanced010ObliqueInterpolation
import Mathlib

theorem LeanFlowProofs.PBAdvanced010.equalPower
    (a b s t α β γ : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0) :
    let c : ℝ := (a + 1) ^ 2 + b ^ 2
    let n : ℝ := a ^ 2 + b ^ 2 - 1
    let L : ℝ := 3 - 3 * a ^ 2 - b ^ 2
    let q : ℝ → ℝ → ℝ :=
      fun x y => x ^ 2 + y ^ 2 + α * x + β * y + γ
    2 * s * n ≠ c * t →
    q (a - (2 * s * n / c) * (a + 1))
      (b * (1 - 2 * s * n / c)) = 0 →
    q (a + s * (1 - a)) (b * (1 - s)) = 0 →
    q (a - t * (a + 1)) (b * (1 - t)) = 0 →
    2 * a * (q (1 / a) 0 - (1 - a ^ 2) / a ^ 2) =
      4 * a * n * s * t - (L + 3 * a * n) * s +
        (L - 3 * a * n) * t + 2 * a * n := by 
  dsimp only
  intro hne hK hP hQ
  let c := (a + 1) ^ 2 + b ^ 2
  let n := a ^ 2 + b ^ 2 - 1
  let d := (a - 1) ^ 2 + b ^ 2
  let ell := -2*a*(a+1)-2*b^2-α*(a+1)-β*b
  let m := 2*a*(1-a)-2*b^2+α*(1-a)-β*b
  let z := a^2+b^2+α*a+β*b+γ
  let k := 2*s*n/c
  have hc : c ≠ 0 := by
    dsimp [c]
    have := sq_pos_of_ne_zero hb
    nlinarith [sq_nonneg (a+1)]
  have hk : c * k = 2*s*n := by
    dsimp [k]
    field_simp
  have hkt : k ≠ t := by
    intro he
    apply hne
    change 2*s*n = c*t
    rw [← hk, he]
  have eB (u : ℝ) :
      (a-u*(a+1))^2+(b*(1-u))^2+α*(a-u*(a+1))+β*(b*(1-u))+γ =
      c*u^2+ell*u+z := by dsimp [c, ell, z]; ring
  have eC (u : ℝ) :
      (a+u*(1-a))^2+(b*(1-u))^2+α*(a+u*(1-a))+β*(b*(1-u))+γ =
      d*u^2+m*u+z := by dsimp [d, m, z]; ring
  have hK' : c*k^2+ell*k+z=0 := by rw [← eB]; exact hK
  have hQ' : c*t^2+ell*t+z=0 := by rw [← eB]; exact hQ
  have hP' : d*s^2+m*s+z=0 := by rw [← eC]; exact hP
  obtain ⟨hell, hm, hz⟩ :=
    LeanFlowProofs.PBAdvanced010.obliqueInterpolation c d n s t k ell m z hs hkt hk hK' hQ' hP'
  have hj : 2*a*((1/a)^2+0^2+α*(1/a)+β*0+γ-(1-a^2)/a^2) =
      2*α+2*a*γ+2*a := by
        field_simp
        <;> ring
  rw [hj]
  dsimp [ell, m, z, c, d, n] at hell hm hz
  linear_combination (a-1)*hell + (a+1)*hm + 2*a*hz
