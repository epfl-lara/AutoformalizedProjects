import LeanFlowProofs.PBAdvanced009.CosphericalEquation
import Mathlib

theorem LeanFlowProofs.PB009.originCircleTransfer
    (s : Set (EuclideanSpace ℝ (Fin 2)))
    (hs : EuclideanGeometry.Cospherical s)
    (hzero : (0 : EuclideanSpace ℝ (Fin 2)) ∈ s)
    (p q : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ s) (hq : q ∈ s)
    (hpzero : p ≠ 0) (hqzero : q ≠ 0) (hpq : p ≠ q)
    (u v : ℝ)
    (hpc : (p 0) ^ 2 + (p 1) ^ 2 = u * p 0 + v * p 1)
    (hqc : (q 0) ^ 2 + (q 1) ^ 2 = u * q 0 + v * q 1) :
    ∀ X : EuclideanSpace ℝ (Fin 2), X ∈ s →
      (X 0) ^ 2 + (X 1) ^ 2 = u * X 0 + v * X 1 := by 
  have ext2 : ∀ (x y : EuclideanSpace ℝ (Fin 2)), x 0 = y 0 → x 1 = y 1 → x = y := by
    intro x y h0 h1
    ext i
    fin_cases i <;> assumption
  have prop : ∀ t : ℝ, q 0 = t * p 0 → q 1 = t * p 1 → False := by
    intro t ht0 ht1
    have hn : p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by
      intro h
      have h0 : p 0 = 0 := by nlinarith [sq_nonneg (p 1)]
      have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 0)]
      exact hpzero (ext2 p 0 h0 h1)
    have he : t * (t - 1) * (p 0 ^ 2 + p 1 ^ 2) = 0 := by
      rw [ht0, ht1] at hqc
      linear_combination hqc - t * hpc
    have ht : t = 0 ∨ t = 1 := by
      rcases mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn) with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases ht with ht | ht
    · apply hqzero
      apply ext2 <;> simp_all
    · apply hpq
      apply ext2 <;> simp_all
  have hd : p 0 * q 1 - p 1 * q 0 ≠ 0 := by
    intro hd
    by_cases h0 : p 0 = 0
    · have h1 : p 1 ≠ 0 := by
        intro h1
        exact hpzero (ext2 p 0 h0 h1)
      apply prop (q 1 / p 1)
      · have : q 0 = 0 := by
          have : p 1 * q 0 = 0 := by simpa [h0] using hd
          exact (mul_eq_zero.mp this).resolve_left h1
        simp [h0, this]
      · field_simp
    · apply prop (q 0 / p 0)
      · field_simp
      · field_simp
        nlinarith
  obtain ⟨u', v', w, he⟩ := LeanFlowProofs.PB009.cosphericalEquation s hs
  have hw : w = 0 := by simpa using he 0 hzero
  have hp' := he p hp
  have hq' := he q hq
  have hu : (u' - u) * (p 0 * q 1 - p 1 * q 0) = 0 := by
    linear_combination q 1 * (hpc - hp') - p 1 * (hqc - hq') + (q 1 - p 1) * hw
  have hv : (v' - v) * (p 0 * q 1 - p 1 * q 0) = 0 := by
    linear_combination p 0 * (hqc - hq') - q 0 * (hpc - hp') + (p 0 - q 0) * hw
  have huu : u' = u := by
    have := (mul_eq_zero.mp hu).resolve_right hd
    linarith
  have hvv : v' = v := by
    have := (mul_eq_zero.mp hv).resolve_right hd
    linarith
  intro X hX
  have := he X hX
  rw [huu, hvv, hw] at this
  linarith

