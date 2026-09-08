import Mathlib

theorem LeanFlowProofs.pb015_internal_bisector
    (m n ρ : ℝ)
    (A B C J : EuclideanSpace ℝ (Fin 2))
    (hm : 0 < m) (hn : 0 < n) (hp : 1 < m * n)
    (hρ : 0 ≤ ρ)
    (hA : A 0 = -(n - m) / (m * n - 1) ∧
      A 1 = 2 * m * n / (m * n - 1))
    (hB : B 0 = -m ∧ B 1 = 0)
    (hC : C 0 = n ∧ C 1 = 0)
    (hleft : (2 * m * J 0 + (1 - m ^ 2) * J 1 + 2 * m ^ 2) ^ 2 =
      ρ ^ 2 * (m ^ 2 + 1) ^ 2)
    (hright : (-2 * n * J 0 + (1 - n ^ 2) * J 1 + 2 * n ^ 2) ^ 2 =
      ρ ^ 2 * (n ^ 2 + 1) ^ 2)
    (hside : (affineSpan ℝ {A, J}).SOppSide B C) :
    ∃ t : ℝ, t ≠ 0 ∧
      J 0 = (1 - t) * A 0 ∧
      J 1 = (1 - t) * A 1 + t ∧
      ρ = |t| := by classical
  set_option maxHeartbeats 1000000 in
  have functional : ∀ a b c : ℝ,
      a * A 0 + b * A 1 + c = 0 →
      0 < a * B 0 + b * B 1 + c →
      0 < a * C 0 + b * C 1 + c →
      a * J 0 + b * J 1 + c ≠ 0 := by
    intro a b c ha hb hc hj
    have hz : ∀ P ∈ affineSpan ℝ {A, J}, a * P 0 + b * P 1 + c = 0 := by
      intro P hP
      refine affineSpan_induction (p := fun P => a * P 0 + b * P 1 + c = 0) hP ?_ ?_
      · intro P hP
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hP
        rcases hP with rfl | rfl <;> assumption
      · intro r U V W hu hv hw
        change a * (r * (U 0 - V 0) + W 0) + b * (r * (U 1 - V 1) + W 1) + c = 0
        linear_combination r * hu - r * hv + hw
    obtain ⟨P, hP, Q, hQ, hr⟩ := hside.1
    have hp := hz P hP
    have hq := hz Q hQ
    rcases hr with he | he | ⟨r, s, hr, hs, he⟩
    · have he0 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 0) he
      have he1 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 1) he
      change B 0 - P 0 = 0 at he0
      change B 1 - P 1 = 0 at he1
      rw [sub_eq_zero.mp he0, sub_eq_zero.mp he1] at hb
      linarith only [hb, hp]
    · have he0 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 0) he
      have he1 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 1) he
      change Q 0 - C 0 = 0 at he0
      change Q 1 - C 1 = 0 at he1
      rw [sub_eq_zero.mp he0, sub_eq_zero.mp he1] at hq
      linarith only [hc, hq]
    · have he0 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 0) he
      have he1 := congrArg (fun V : EuclideanSpace ℝ (Fin 2) => V 1) he
      change r * (B 0 - P 0) = s * (Q 0 - C 0) at he0
      change r * (B 1 - P 1) = s * (Q 1 - C 1) at he1
      have heq : r * (a * B 0 + b * B 1 + c) + s * (a * C 0 + b * C 1 + c) = 0 := by
        linear_combination a * he0 + b * he1 + r * hp + s * hq
      have := add_pos (mul_pos hr hb) (mul_pos hs hc)
      linarith
  have hd : m * n - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hm2 : 0 < m ^ 2 + 1 := by positivity
  have hn2 : 0 < n ^ 2 + 1 := by positivity
  let l := 2 * m * J 0 + (1 - m ^ 2) * J 1 + 2 * m ^ 2
  let r := -2 * n * J 0 + (1 - n ^ 2) * J 1 + 2 * n ^ 2
  have hsum : (n ^ 2 + 1) * l + (m ^ 2 + 1) * r ≠ 0 := by
    have hh := functional (2 * m * (n ^ 2 + 1) - 2 * n * (m ^ 2 + 1))
      ((1 - m ^ 2) * (n ^ 2 + 1) + (1 - n ^ 2) * (m ^ 2 + 1))
      (2 * m ^ 2 * (n ^ 2 + 1) + 2 * n ^ 2 * (m ^ 2 + 1))
    have ha : (2 * m * (n ^ 2 + 1) - 2 * n * (m ^ 2 + 1)) * A 0 +
        ((1 - m ^ 2) * (n ^ 2 + 1) + (1 - n ^ 2) * (m ^ 2 + 1)) * A 1 +
        (2 * m ^ 2 * (n ^ 2 + 1) + 2 * n ^ 2 * (m ^ 2 + 1)) = 0 := by
      rw [hA.1, hA.2]
      field_simp
      <;> ring
    have hb : 0 < (2 * m * (n ^ 2 + 1) - 2 * n * (m ^ 2 + 1)) * B 0 +
        ((1 - m ^ 2) * (n ^ 2 + 1) + (1 - n ^ 2) * (m ^ 2 + 1)) * B 1 +
        (2 * m ^ 2 * (n ^ 2 + 1) + 2 * n ^ 2 * (m ^ 2 + 1)) := by
      rw [hB.1, hB.2]
      ring_nf
      positivity
    have hc : 0 < (2 * m * (n ^ 2 + 1) - 2 * n * (m ^ 2 + 1)) * C 0 +
        ((1 - m ^ 2) * (n ^ 2 + 1) + (1 - n ^ 2) * (m ^ 2 + 1)) * C 1 +
        (2 * m ^ 2 * (n ^ 2 + 1) + 2 * n ^ 2 * (m ^ 2 + 1)) := by
      rw [hC.1, hC.2]
      ring_nf
      positivity
    convert hh ha hb hc using 1 <;> dsimp [l, r] <;> ring
  have heq : (n ^ 2 + 1) * l = (m ^ 2 + 1) * r := by
    have hprod : ((n ^ 2 + 1) * l - (m ^ 2 + 1) * r) *
        ((n ^ 2 + 1) * l + (m ^ 2 + 1) * r) = 0 := by
      dsimp [l, r]
      linear_combination (n ^ 2 + 1) ^ 2 * hleft - (m ^ 2 + 1) ^ 2 * hright
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum)
  let t := l / (m ^ 2 + 1)
  have hl : l = t * (m ^ 2 + 1) := by dsimp [t]; field_simp
  have hr : r = t * (n ^ 2 + 1) := by nlinarith [hm2]
  have ht : t ≠ 0 := by
    intro ht
    apply hsum
    rw [hl, hr, ht]
    ring
  refine ⟨t, ht, ?_, ?_, ?_⟩
  · rw [hA.1, ← mul_div_assoc, eq_div_iff hd]
    apply mul_left_cancel₀ (ne_of_gt (add_pos hm hn))
    dsimp only [l, r] at hl hr
    linear_combination (n ^ 2 - 1) / 2 * hl + (1 - m ^ 2) / 2 * hr
  · have hy : J 1 * (m * n - 1) = (1 - t) * (2 * m * n) + t * (m * n - 1) := by
      apply mul_left_cancel₀ (ne_of_gt (add_pos hm hn))
      dsimp only [l, r] at hl hr
      linear_combination -n * hl - m * hr
    rw [hA.2, ← mul_div_assoc, div_add' _ _ _ hd, eq_div_iff hd]
    exact hy
  · have hsq : ρ ^ 2 = t ^ 2 := by
      change l ^ 2 = _ at hleft
      rw [hl] at hleft
      have he : (m ^ 2 + 1) ^ 2 * (ρ ^ 2 - t ^ 2) = 0 := by linear_combination -hleft
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt (sq_pos_of_pos hm2)))
    nlinarith [sq_abs t, abs_nonneg t]

