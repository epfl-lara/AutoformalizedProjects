import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

open Affine EuclideanGeometry Module
open scoped Real

namespace IMO2026P4

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]

/-- The condition to win immediately with a given triangle. -/
def WinsNow (t : Triangle ℝ P) (θ : ℝ) : Prop :=
  ∃ i, ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) = θ

/-- A choice of perimeter point not at a vertex by Mulan. -/
structure Move (t : Triangle ℝ P) where
  /-- The vertex opposite the point chosen. -/
  i : Fin 3
  /-- The point chosen. -/
  p : P
  sbtw_p : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2))

/-- One half of the triangle split by a move. -/
def Move.half {t : Triangle ℝ P} (m : Move t) (c : Prop) [Decidable c] : Triangle ℝ P :=
  if c then ⟨![t.points m.i, t.points (m.i + 1), m.p], by
    have h : AffineIndependent ℝ ![t.points m.i, t.points (m.i + 1), t.points (m.i + 2)] := by
      convert t.independent.comp_embedding (finCycle m.i).toEmbedding
      ext i; fin_cases i <;> simp [add_comm]
    convert! h.affineIndependent_update_of_notMem_affineSpan (i := 2) (p₀ := m.p) ?_
    · ext i; fin_cases i <;> simp
    · obtain ⟨r, ⟨hr0, hr1⟩, hre⟩ := m.sbtw_p.mem_image_Ioo
      change AffineMap.lineMap (![t.points m.i, t.points (m.i + 1), t.points (m.i + 2)] 1)
        (![t.points m.i, t.points (m.i + 1), t.points (m.i + 2)] 2) r = m.p at hre
      rw [← hre,
        ← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (by grind) (by grind)]
      intro hm
      apply hr0.ne'
      convert h.eq_zero_of_affineCombination_mem_affineSpan (by simp) hm (i := 2) (by simp)
        (by simp)
      simp⟩ else
    ⟨![t.points m.i, t.points (m.i + 2), m.p], by
    have h : AffineIndependent ℝ ![t.points m.i, t.points (m.i + 2), t.points (m.i + 1)] := by
      convert t.independent.comp_embedding ((Equiv.swap 2 1).trans (finCycle m.i)).toEmbedding
      ext i; fin_cases i <;> simp [add_comm]; grind
    convert! h.affineIndependent_update_of_notMem_affineSpan (i := 2) (p₀ := m.p) ?_
    · ext i; fin_cases i <;> simp
    · obtain ⟨r, ⟨hr0, hr1⟩, hre⟩ := m.sbtw_p.mem_image_Ioo
      change AffineMap.lineMap (![t.points m.i, t.points (m.i + 2), t.points (m.i + 1)] 2)
        (![t.points m.i, t.points (m.i + 2), t.points (m.i + 1)] 1) r = m.p at hre
      rw [← hre,
        ← Finset.univ.affineCombination_affineCombinationLineMapWeights _ (by grind) (by grind)]
      intro hm
      suffices 1 - r = 0 by
        grind
      convert h.eq_zero_of_affineCombination_mem_affineSpan (by simp) hm (i := 2) (by simp)
        (by simp)
      simp⟩

variable (P) in
/-- A strategy for Mulan chooses a move for the last triangle in a list of triangles seen (where
the choices are irrelevant for lists that cannot arise by this strategy, including those where
Mulan has already won). -/
abbrev Strategy := {k : ℕ} → (t : Fin (k + 1) → Triangle ℝ P) → Move (t (Fin.last k))

/-- Given the initial triangle and the choices made by Shan-Yu, the first `k` triangles from playing
a strategy (if it does not win before the end of that list). -/
def Strategy.play (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop) [∀ k, Decidable (c k)] :
    (k : ℕ) → Fin k → Triangle ℝ P
| 0 => Fin.elim0
| 1 => ![t₀]
| k + 2 => Fin.snoc (s.play t₀ c (k + 1)) ((s (s.play t₀ c (k + 1))).half (c k))

open scoped Classical in
/-- Whether a strategy wins for Mulan, against all possible moves by Shan-Yu. -/
def Strategy.Winning (s : Strategy P) (θ : ℝ) : Prop :=
  ∀ (t₀ : Triangle ℝ P) (c : ℕ → Prop), ∃ k, WinsNow ((s.play t₀ c) (k + 1) (Fin.last k)) θ

/-- The answer to be determined. -/
def answer : Set ℝ := {θ : ℝ | ∃ n : ℕ, 2 ≤ n ∧ θ = Real.pi / (n : ℝ)}

private lemma play_last_succ (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop)
    [∀ k, Decidable (c k)] (k : ℕ) :
    (s.play t₀ c (k + 2) (Fin.last (k + 1))) =
      (s (s.play t₀ c (k + 1))).half (c k) := by
  simp [Strategy.play]

private lemma answer_subset_open_interval :
    answer ⊆ {θ : ℝ | 0 < θ ∧ θ < Real.pi} := by
  intro θ hθ
  change ∃ n : ℕ, 2 ≤ n ∧ θ = Real.pi / (n : ℝ) at hθ
  rcases hθ with ⟨n, hn, rfl⟩
  have hn0nat : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn0nat
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have h : (1 : ℕ) < 2 := by decide
    have h' : (1 : ℕ) < n := lt_of_lt_of_le h hn
    exact_mod_cast h'
  constructor
  · exact div_pos Real.pi_pos hn0
  · apply (div_lt_iff₀ hn0).2
    calc
      Real.pi = Real.pi * 1 := by ring
      _ < Real.pi * (n : ℝ) :=
        mul_lt_mul_of_pos_left hn1 Real.pi_pos

private lemma winsNow_cyclic_cases (t : Triangle ℝ P) (θ : ℝ) (h : WinsNow t θ) :
    θ = ∠ (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) ∨
    θ = ∠ (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) (t.points (0 : Fin 3)) ∨
    θ = ∠ (t.points (2 : Fin 3)) (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) := by
  rcases h with ⟨i, hi⟩
  fin_cases i <;> simp_all [WinsNow]

private lemma triangle_cyclic_angle_sum (t : Triangle ℝ P) :
    ∠ (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) +
        ∠ (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) (t.points (0 : Fin 3)) +
        ∠ (t.points (2 : Fin 3)) (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) = Real.pi := by
  apply EuclideanGeometry.angle_add_angle_add_angle_eq_pi
  intro h
  have h' : (1 : Fin 3) = 0 := t.independent.injective h
  exact Fin.zero_ne_one h'.symm

private lemma triangle_cyclic_angle_bounds (t : Triangle ℝ P) (i : Fin 3) :
    0 < ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ∧
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < Real.pi := by
  have ha : AffineIndependent ℝ ![t.points i, t.points (i + 1), t.points (i + 2)] := by
    convert t.independent.comp_embedding (finCycle i).toEmbedding
    ext j
    fin_cases j <;> simp [add_comm]
  have h : ¬ Collinear ℝ ({t.points i, t.points (i + 1), t.points (i + 2)} : Set P) :=
    affineIndependent_iff_not_collinear_set.mp ha
  exact ⟨angle_pos_of_not_collinear h, angle_lt_pi_of_not_collinear h⟩

private lemma move_half_points (t : Triangle ℝ P) (m : Move t) (c : Prop) [Decidable c] :
    (m.half c).points 0 = t.points m.i ∧
      (m.half c).points 1 = (if c then t.points (m.i + 1) else t.points (m.i + 2)) ∧
      (m.half c).points 2 = m.p := by
  by_cases hc : c <;> simp [Move.half, hc]

private lemma result_of_game_characterization
    (hforward :
      ∀ {θ : ℝ}, (∃ s : Strategy P, s.Winning θ) →
        ∃ n : ℕ, 2 ≤ n ∧ θ = Real.pi / (n : ℝ))
    (hreverse :
      ∀ n : ℕ, 2 ≤ n →
        ∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ))) :
    {θ : ℝ | 0 < θ ∧ θ < Real.pi ∧ ∃ s : Strategy P, s.Winning θ} = answer := by
  ext θ
  constructor
  · rintro ⟨_, _, s, hs⟩
    simpa [answer] using hforward ⟨s, hs⟩
  · intro hθ
    change ∃ n : ℕ, 2 ≤ n ∧ θ = Real.pi / (n : ℝ) at hθ
    rcases hθ with ⟨n, hn, rfl⟩
    have hopen := answer_subset_open_interval (show Real.pi / (n : ℝ) ∈ answer from ⟨n, hn, rfl⟩)
    exact ⟨hopen.1, hopen.2, hreverse n hn⟩

private lemma triangle_angle_bounds_zero (t : Triangle ℝ P) :
    0 < ∠ (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) ∧
      ∠ (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) < Real.pi := by
  have ha : AffineIndependent ℝ ![t.points (0 : Fin 3), t.points (1 : Fin 3), t.points (2 : Fin 3)] := by
    convert t.independent
    ext i
    fin_cases i <;> simp
  have h : ¬ Collinear ℝ ({t.points (0 : Fin 3), t.points (1 : Fin 3), t.points (2 : Fin 3)} : Set P) :=
    affineIndependent_iff_not_collinear_set.mp ha
  exact ⟨angle_pos_of_not_collinear h, angle_lt_pi_of_not_collinear h⟩

private lemma move_half_retained_true (t : Triangle ℝ P) (m : Move t) :
    ∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
        ((m.half True).points (2 : Fin 3)) =
      ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) := by
  obtain ⟨h0, h1, h2⟩ := move_half_points t m True
  simp only [↓reduceIte] at h1
  rw [h0, h1, h2]
  exact m.sbtw_p.angle_eq_right (t.points m.i)

private lemma move_half_retained_false (t : Triangle ℝ P) (m : Move t) :
    ∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
        ((m.half False).points (2 : Fin 3)) =
      ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) := by
  obtain ⟨h0, h1, h2⟩ := move_half_points t m False
  simp only [↓reduceIte] at h1
  rw [h0, h1, h2]
  exact m.sbtw_p.symm.angle_eq_right (t.points m.i)

private lemma move_half_true_remaining_sum (t : Triangle ℝ P) (m : Move t) :
    let u : Triangle ℝ P := m.half True
    (∠ (u.points (1 : Fin 3)) (u.points (2 : Fin 3)) (u.points (0 : Fin 3)) +
      ∠ (u.points (2 : Fin 3)) (u.points (0 : Fin 3)) (u.points (1 : Fin 3))) =
      Real.pi - ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) := by
  let u : Triangle ℝ P := m.half True
  have hc := triangle_cyclic_angle_sum u
  have hr :
      ∠ (u.points (0 : Fin 3)) (u.points (1 : Fin 3)) (u.points (2 : Fin 3)) =
        ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) := by
    dsimp [u]
    exact move_half_retained_true t m
  dsimp
  linarith

private lemma move_half_false_remaining_sum (t : Triangle ℝ P) (m : Move t) :
    let u : Triangle ℝ P := m.half False
    (∠ (u.points (1 : Fin 3)) (u.points (2 : Fin 3)) (u.points (0 : Fin 3)) +
      ∠ (u.points (2 : Fin 3)) (u.points (0 : Fin 3)) (u.points (1 : Fin 3))) =
      Real.pi - ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) := by
  let u : Triangle ℝ P := m.half False
  have hc := triangle_cyclic_angle_sum u
  have hr :
      ∠ (u.points (0 : Fin 3)) (u.points (1 : Fin 3)) (u.points (2 : Fin 3)) =
        ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) := by
    dsimp [u]
    exact move_half_retained_false t m
  dsimp
  linarith

private def emptyMetric : MetricSpace Empty :=
  { dist := fun x _ => nomatch x
    dist_self := by intro x; exact nomatch x
    dist_comm := by intro x; exact nomatch x
    dist_triangle := by intro x; exact nomatch x
    eq_of_dist_eq_zero := by intro x; exact nomatch x }

private lemma winsNow_open_interval (t : Triangle ℝ P) (θ : ℝ) (h : WinsNow t θ) :
    0 < θ ∧ θ < Real.pi := by
  rcases winsNow_cyclic_cases t θ h with h0 | h1 | h2
  · simpa [h0] using triangle_cyclic_angle_bounds t (0 : Fin 3)
  · simpa [h1] using triangle_cyclic_angle_bounds t (1 : Fin 3)
  · simpa [h2] using triangle_cyclic_angle_bounds t (2 : Fin 3)

private lemma move_half_split_angles (t : Triangle ℝ P) (m : Move t) :
    ∠ (t.points (m.i + 1)) m.p (t.points m.i) +
        ∠ (t.points (m.i + 2)) m.p (t.points m.i) = Real.pi := by
  have hp : ∠ (t.points (m.i + 1)) m.p (t.points (m.i + 2)) = Real.pi :=
    m.sbtw_p.angle₁₂₃_eq_pi
  have h := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
    (t.points m.i) hp
  simpa [angle_comm] using h

private lemma move_half_branch_angle_sum (t : Triangle ℝ P) (m : Move t) :
    ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) +
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) = Real.pi := by
  obtain ⟨h0t, h1t, h2t⟩ := move_half_points t m True
  obtain ⟨h0f, h1f, h2f⟩ := move_half_points t m False
  rw [h0t, h1t, h2t, h0f, h1f, h2f]
  exact move_half_split_angles t m

private lemma winning_strategy_open_interval (s : Strategy P) (θ : ℝ)
    (hs : s.Winning θ) (t₀ : Triangle ℝ P) : 0 < θ ∧ θ < Real.pi := by
  obtain ⟨k, hk⟩ := hs t₀ (fun _ => True)
  exact winsNow_open_interval _ _ hk

private lemma move_exists (t : Triangle ℝ P) : Nonempty (Move t) := by
  classical
  refine ⟨{ i := 0, p := AffineMap.lineMap (t.points (0 + 1)) (t.points (0 + 2)) (1 / 2 : ℝ), sbtw_p := ?_ }⟩
  refine (sbtw_iff_mem_image_Ioo_and_ne).2 ⟨?_, ?_⟩
  · exact ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩, rfl⟩
  · intro h
    have h' : (0 + 1 : Fin 3) = 0 + 2 := t.independent.injective h
    omega

private lemma split_midpoint_target (t : Triangle ℝ P) (m : Move t) (θ : ℝ)
    (hT : ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) = θ)
    (hF : ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) = θ) :
    θ = Real.pi / 2 := by
  have hs := move_half_branch_angle_sum t m
  rw [hT, hF] at hs
  linarith

private lemma strategy_nonempty : Nonempty (Strategy P) := by
  classical
  let s : Strategy P := fun {k} t => Classical.choice (move_exists (t (Fin.last k)))
  exact ⟨s⟩

private lemma triangle_nonempty : Nonempty (Triangle ℝ P) := by
  classical
  letI : FiniteDimensional ℝ V := by
    apply FiniteDimensional.of_finrank_eq_succ
    exact_mod_cast (Fact.out : Module.finrank ℝ V = 2)
  let h : Nonempty (AffineBasis (Fin 3) ℝ P) :=
    AffineBasis.exists_affineBasis_of_finiteDimensional (ι := Fin 3) (k := ℝ)
      (V := V) (P := P) (by
        rw [Fintype.card_fin]
        have hf : Module.finrank ℝ V = 2 := Fact.out
        omega)
  obtain ⟨b⟩ := h
  exact ⟨⟨b, b.ind⟩⟩

private lemma branch_arithmetic (a b c x θ : ℝ) (hsum : a + b + c = Real.pi)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)
    (ha : ∀ z : ℤ, a ≠ (z : ℝ) * θ)
    (hb : ∀ z : ℤ, b ≠ (z : ℝ) * θ)
    (hc : ∀ z : ℤ, c ≠ (z : ℝ) * θ) :
    (∀ z : ℤ, x ≠ (z : ℝ) * θ ∧ Real.pi - a - x ≠ (z : ℝ) * θ) ∨
      (∀ z : ℤ, Real.pi - x ≠ (z : ℝ) * θ ∧ x - b ≠ (z : ℝ) * θ) := by
  classical
  by_cases hA1 : ∃ z : ℤ, x = (z : ℝ) * θ
  · by_cases hA2 : ∃ z : ℤ, Real.pi - a - x = (z : ℝ) * θ
    · by_cases hB1 : ∃ z : ℤ, Real.pi - x = (z : ℝ) * θ
      · exfalso
        rcases hA1 with ⟨z, hz⟩
        rcases hB1 with ⟨w, hw⟩
        apply hpi (z + w)
        calc
          Real.pi = x + (Real.pi - x) := by ring
          _ = (z : ℝ) * θ + (w : ℝ) * θ := by linarith [hz, hw]
          _ = ((z + w : ℤ) : ℝ) * θ := by rw [Int.cast_add]; ring
      · by_cases hB2 : ∃ z : ℤ, x - b = (z : ℝ) * θ
        · exfalso
          rcases hA1 with ⟨z, hz⟩
          rcases hB2 with ⟨w, hw⟩
          apply hb (z - w)
          calc
            b = x - (x - b) := by ring
            _ = (z : ℝ) * θ - (w : ℝ) * θ := by linarith [hz, hw]
            _ = ((z - w : ℤ) : ℝ) * θ := by rw [Int.cast_sub]; ring
        · right
          intro z
          constructor
          · intro hz
            exact hB1 ⟨z, hz⟩
          · intro hz
            exact hB2 ⟨z, hz⟩
    · by_cases hB1 : ∃ z : ℤ, Real.pi - x = (z : ℝ) * θ
      · exfalso
        rcases hA1 with ⟨z, hz⟩
        rcases hB1 with ⟨w, hw⟩
        apply hpi (z + w)
        calc
          Real.pi = x + (Real.pi - x) := by ring
          _ = (z : ℝ) * θ + (w : ℝ) * θ := by linarith [hz, hw]
          _ = ((z + w : ℤ) : ℝ) * θ := by rw [Int.cast_add]; ring
      · by_cases hB2 : ∃ z : ℤ, x - b = (z : ℝ) * θ
        · exfalso
          rcases hA1 with ⟨z, hz⟩
          rcases hB2 with ⟨w, hw⟩
          apply hb (z - w)
          calc
            b = x - (x - b) := by ring
            _ = (z : ℝ) * θ - (w : ℝ) * θ := by linarith [hz, hw]
            _ = ((z - w : ℤ) : ℝ) * θ := by rw [Int.cast_sub]; ring
        · right
          intro z
          constructor
          · intro hz
            exact hB1 ⟨z, hz⟩
          · intro hz
            exact hB2 ⟨z, hz⟩
  · by_cases hA2 : ∃ z : ℤ, Real.pi - a - x = (z : ℝ) * θ
    · by_cases hB1 : ∃ z : ℤ, Real.pi - x = (z : ℝ) * θ
      · exfalso
        rcases hA2 with ⟨z, hz⟩
        rcases hB1 with ⟨w, hw⟩
        apply ha (w - z)
        calc
          a = (Real.pi - x) - (Real.pi - a - x) := by ring
          _ = (w : ℝ) * θ - (z : ℝ) * θ := by rw [hw, hz]
          _ = ((w - z : ℤ) : ℝ) * θ := by rw [Int.cast_sub]; ring
      · by_cases hB2 : ∃ z : ℤ, x - b = (z : ℝ) * θ
        · exfalso
          rcases hA2 with ⟨z, hz⟩
          rcases hB2 with ⟨w, hw⟩
          apply hc (z + w)
          calc
            c = Real.pi - a - b := by linarith
            _ = (Real.pi - a - x) + (x - b) := by ring
            _ = (z : ℝ) * θ + (w : ℝ) * θ := by linarith [hz, hw]
            _ = ((z + w : ℤ) : ℝ) * θ := by rw [Int.cast_add]; ring
        · right
          intro z
          constructor
          · intro hz
            exact hB1 ⟨z, hz⟩
          · intro hz
            exact hB2 ⟨z, hz⟩
    · left
      intro z
      constructor
      · intro hz
        exact hA1 ⟨z, hz⟩
      · intro hz
        exact hA2 ⟨z, hz⟩

private lemma half_branch_angle_relations (t : Triangle ℝ P) (m : Move t) :
    let a := ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2))
    let b := ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1))
    let x := ∠ (t.points (m.i + 1)) m.p (t.points m.i)
    (∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
        ((m.half True).points (2 : Fin 3)) = a ∧
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) = x ∧
      ∠ ((m.half True).points (2 : Fin 3)) ((m.half True).points (0 : Fin 3))
        ((m.half True).points (1 : Fin 3)) = Real.pi - a - x) ∧
    (∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
        ((m.half False).points (2 : Fin 3)) = b ∧
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) = Real.pi - x ∧
      ∠ ((m.half False).points (2 : Fin 3)) ((m.half False).points (0 : Fin 3))
        ((m.half False).points (1 : Fin 3)) = x - b) := by
  dsimp
  have hT0 := move_half_retained_true t m
  have hF0 := move_half_retained_false t m
  have hTsum := move_half_true_remaining_sum t m
  have hFsum := move_half_false_remaining_sum t m
  dsimp at hTsum hFsum
  have hsplit := move_half_split_angles t m
  have hT1 :
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) =
        ∠ (t.points (m.i + 1)) m.p (t.points m.i) := by
    obtain ⟨h0, h1, h2⟩ := move_half_points t m True
    rw [h0, h1, h2]
    simp
  have hF1 :
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) =
        Real.pi - ∠ (t.points (m.i + 1)) m.p (t.points m.i) := by
    obtain ⟨h0, h1, h2⟩ := move_half_points t m False
    rw [h0, h1, h2]
    simp only [if_false]
    linarith [hsplit]
  constructor
  · refine ⟨hT0, hT1, ?_⟩
    linarith [hTsum]
  · refine ⟨hF0, hF1, ?_⟩
    linarith [hFsum]

private lemma pi_multiple_gives_answer (θ : ℝ) (hθpos : 0 < θ) (hθlt : θ < Real.pi)
    (hbad : ¬ (∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)) :
    ∃ n : ℕ, 2 ≤ n ∧ θ = Real.pi / (n : ℝ) := by
  push_neg at hbad
  obtain ⟨z, hz⟩ := hbad
  have hzpos : 0 < (z : ℝ) := by
    nlinarith [Real.pi_pos, hθpos]
  have hz0 : (0 : ℤ) ≤ z := by
    exact_mod_cast (le_of_lt hzpos)
  let n : ℕ := z.toNat
  have hcastZ : (n : ℤ) = z := by
    simpa [n] using (Int.toNat_of_nonneg hz0)
  have hcast : (n : ℝ) = (z : ℝ) := by
    exact_mod_cast hcastZ
  have hzgt : (1 : ℝ) < (z : ℝ) := by
    nlinarith [hθlt, hθpos, hz]
  have hzgt' : (1 : ℤ) < z := by
    exact_mod_cast hzgt
  have hzgtN : (1 : ℤ) < (n : ℤ) := by
    rw [hcastZ]
    exact hzgt'
  have hzNat : (1 : ℕ) < n := by
    exact_mod_cast hzgtN
  have hn : 2 ≤ n := by omega
  refine ⟨n, hn, ?_⟩
  apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).2
  rw [hcast]
  nlinarith [hz]

private lemma half_branch_avoids_multiples (t : Triangle ℝ P) (m : Move t) (θ : ℝ)
    (hsum :
      (∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2))) +
      (∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1))) +
      (∠ (t.points (m.i + 1)) (t.points (m.i + 2)) (t.points m.i)) = Real.pi)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)
    (ha : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) ≠ (z : ℝ) * θ)
    (hb : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) ≠ (z : ℝ) * θ)
    (hc : ∀ z : ℤ, ∠ (t.points (m.i + 1)) (t.points (m.i + 2)) (t.points m.i) ≠ (z : ℝ) * θ) :
    (∀ z : ℤ,
      ∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
          ((m.half True).points (2 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
          ((m.half True).points (0 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half True).points (2 : Fin 3)) ((m.half True).points (0 : Fin 3))
          ((m.half True).points (1 : Fin 3)) ≠ (z : ℝ) * θ) ∨
    (∀ z : ℤ,
      ∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
          ((m.half False).points (2 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
          ((m.half False).points (0 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half False).points (2 : Fin 3)) ((m.half False).points (0 : Fin 3))
          ((m.half False).points (1 : Fin 3)) ≠ (z : ℝ) * θ) := by
  have hrel := half_branch_angle_relations t m
  dsimp at hrel
  rcases hrel with ⟨⟨hT0, hT1, hT2⟩, ⟨hF0, hF1, hF2⟩⟩
  rcases branch_arithmetic
      (∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)))
      (∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)))
      (∠ (t.points (m.i + 1)) (t.points (m.i + 2)) (t.points m.i))
      (∠ (t.points (m.i + 1)) m.p (t.points m.i)) θ hsum hpi ha hb hc with hT | hF
  · left
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact ha z (by rw [← hT0]; exact hz)
    · intro hz
      exact (hT z).1 (by rw [← hT1]; exact hz)
    · intro hz
      exact (hT z).2 (by rw [← hT2]; exact hz)
  · right
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact hb z (by rw [← hF0]; exact hz)
    · intro hz
      exact (hF z).1 (by rw [← hF1]; exact hz)
    · intro hz
      exact (hF z).2 (by rw [← hF2]; exact hz)

private lemma answer_of_pi_multiple (θ : ℝ) (hθpos : 0 < θ) (hθlt : θ < Real.pi)
    (hbad : ¬ (∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)) : θ ∈ answer := by
  simpa [answer] using pi_multiple_gives_answer θ hθpos hθlt hbad

private lemma answer_mem_pi_multiple (θ : ℝ) (hθ : θ ∈ answer) :
    ¬ (∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) := by
  rcases hθ with ⟨n, hn, hEq⟩
  push_neg
  refine ⟨(n : ℤ), ?_⟩
  rw [hEq]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))
  simpa [mul_comm] using (div_mul_cancel₀ Real.pi hn0).symm

private lemma winning_predicate_of_successor_step
    (W : ℕ → Prop)
    (hbase : W 2)
    (hstep : ∀ n : ℕ, 2 ≤ n → W n → W (n + 1)) :
    ∀ n : ℕ, 2 ≤ n → W n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases h2 : n = 2
      · simpa [h2] using hbase
      · have hn2 : 2 ≤ n := by omega
        have hnsub : 2 ≤ n - 1 := by omega
        have hlt : n - 1 < n := by omega
        have hprev : W (n - 1) := ih (n - 1) hlt hnsub
        have hnext := hstep (n - 1) hnsub hprev
        convert hnext using 1 <;> omega

private lemma no_winning_of_one_adversarial_coloring
    (s : Strategy P) (θ : ℝ) (t₀ : Triangle ℝ P)
    (c : ℕ → Prop)
    (hno : ∀ k, ¬ WinsNow
      ((letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
        (s.play t₀ c) (k + 1) (Fin.last k))) θ) :
    ¬ s.Winning θ := by
  intro hs
  obtain ⟨k, hk⟩ := hs t₀ c
  exact hno k hk

private lemma no_pi_multiple_of_not_mem_answer (θ : ℝ) (hθpos : 0 < θ)
    (hθlt : θ < Real.pi) (hθans : θ ∉ answer) :
    ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ := by
  intro z hz
  apply hθans
  apply answer_of_pi_multiple θ hθpos hθlt
  push_neg
  exact ⟨z, hz⟩

private lemma integer_rank_step
    (a b θ : ℝ) (r : ℕ) (hr : 2 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hθ : 0 < θ)
    (hsum : a + b + (r : ℝ) * θ = Real.pi) :
    b < b + θ ∧ b + θ < b + (r : ℝ) * θ ∧
      Real.pi - a - (b + θ) = ((r - 1 : ℕ) : ℝ) * θ ∧
      (b + θ) - b = θ := by
  have hr1 : (1 : ℕ) ≤ r := by omega
  have hrgt : (1 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show (1 : ℕ) < r by omega)
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr1]
    norm_num
  have hmul' : (1 : ℝ) * θ < (r : ℝ) * θ :=
    mul_lt_mul_of_pos_right hrgt hθ
  have hmul : θ < (r : ℝ) * θ := by simpa using hmul'
  rw [hcast]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · ring

private lemma triangle_angle_sum_reordered (t : Triangle ℝ P) :
    ∠ (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) (t.points (2 : Fin 3)) +
        ∠ (t.points (0 : Fin 3)) (t.points (2 : Fin 3)) (t.points (1 : Fin 3)) +
        ∠ (t.points (2 : Fin 3)) (t.points (0 : Fin 3)) (t.points (1 : Fin 3)) = Real.pi := by
  simpa [angle_comm] using triangle_cyclic_angle_sum t

private lemma half_branch_avoids_multiples_correct (t : Triangle ℝ P) (m : Move t) (θ : ℝ)
    (hsum :
      (∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2))) +
      (∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1))) +
      (∠ (t.points (m.i + 2)) (t.points m.i) (t.points (m.i + 1))) = Real.pi)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)
    (ha : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) ≠ (z : ℝ) * θ)
    (hb : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) ≠ (z : ℝ) * θ)
    (hc : ∀ z : ℤ, ∠ (t.points (m.i + 2)) (t.points m.i) (t.points (m.i + 1)) ≠ (z : ℝ) * θ) :
    (∀ z : ℤ,
      ∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
          ((m.half True).points (2 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
          ((m.half True).points (0 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half True).points (2 : Fin 3)) ((m.half True).points (0 : Fin 3))
          ((m.half True).points (1 : Fin 3)) ≠ (z : ℝ) * θ) ∨
    (∀ z : ℤ,
      ∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
          ((m.half False).points (2 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
          ((m.half False).points (0 : Fin 3)) ≠ (z : ℝ) * θ ∧
      ∠ ((m.half False).points (2 : Fin 3)) ((m.half False).points (0 : Fin 3))
          ((m.half False).points (1 : Fin 3)) ≠ (z : ℝ) * θ) := by
  have hrel := half_branch_angle_relations t m
  dsimp at hrel
  rcases hrel with ⟨⟨hT0, hT1, hT2⟩, ⟨hF0, hF1, hF2⟩⟩
  rcases branch_arithmetic
      (∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)))
      (∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)))
      (∠ (t.points (m.i + 2)) (t.points m.i) (t.points (m.i + 1)))
      (∠ (t.points (m.i + 1)) m.p (t.points m.i)) θ hsum hpi ha hb hc with hT | hF
  · left
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact ha z (by rw [← hT0]; exact hz)
    · intro hz
      exact (hT z).1 (by rw [← hT1]; exact hz)
    · intro hz
      exact (hT z).2 (by rw [← hT2]; exact hz)
  · right
    intro z
    refine ⟨?_, ?_, ?_⟩
    · intro hz
      exact hb z (by rw [← hF0]; exact hz)
    · intro hz
      exact (hF z).1 (by rw [← hF1]; exact hz)
    · intro hz
      exact (hF z).2 (by rw [← hF2]; exact hz)

private lemma answer_iff_not_pi_multiple (θ : ℝ) (hθpos : 0 < θ) (hθlt : θ < Real.pi) :
    θ ∈ answer ↔ ¬ (∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) := by
  constructor
  · exact answer_mem_pi_multiple θ
  · exact answer_of_pi_multiple θ hθpos hθlt

private lemma safe_branch_bool_choice (t : Triangle ℝ P) (m : Move t) (θ : ℝ)
    (hsum :
      (∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2))) +
      (∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1))) +
      (∠ (t.points (m.i + 1)) (t.points (m.i + 2)) (t.points m.i)) = Real.pi)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)
    (ha : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) ≠ (z : ℝ) * θ)
    (hb : ∀ z : ℤ, ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) ≠ (z : ℝ) * θ)
    (hc : ∀ z : ℤ, ∠ (t.points (m.i + 1)) (t.points (m.i + 2)) (t.points m.i) ≠ (z : ℝ) * θ) :
    ∃ b : Bool,
      ∀ z : ℤ,
        (∠ ((m.half (b = true)).points (0 : Fin 3)) ((m.half (b = true)).points (1 : Fin 3))
            ((m.half (b = true)).points (2 : Fin 3)) ≠ (z : ℝ) * θ ∧
         ∠ ((m.half (b = true)).points (1 : Fin 3)) ((m.half (b = true)).points (2 : Fin 3))
            ((m.half (b = true)).points (0 : Fin 3)) ≠ (z : ℝ) * θ ∧
         ∠ ((m.half (b = true)).points (2 : Fin 3)) ((m.half (b = true)).points (0 : Fin 3))
            ((m.half (b = true)).points (1 : Fin 3)) ≠ (z : ℝ) * θ) := by
  rcases half_branch_avoids_multiples t m θ hsum hpi ha hb hc with hT | hF
  · refine ⟨true, ?_⟩
    simpa using hT
  · refine ⟨false, ?_⟩
    simpa using hF

omit [Fact (finrank ℝ V = 2)] in
private lemma play_prefix_congr (s : Strategy P) (t : Triangle ℝ P) (c d : ℕ → Prop) :
    ∀ n : ℕ, (∀ j < n, c j ↔ d j) →
      ∀ i : Fin (n + 1),
        (letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable (c k); s.play t c (n + 1) i) =
          (letI : ∀ k, Decidable (d k) := fun k => Classical.propDecidable (d k); s.play t d (n + 1) i) := by
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable (c k)
  letI : ∀ k, Decidable (d k) := fun k => Classical.propDecidable (d k)
  intro n
  induction n with
  | zero =>
      intro h i
      simp [Strategy.play]
  | succ n ih =>
      intro h i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hhist : s.play t c (n + 1) = s.play t d (n + 1) := by
          funext j
          exact ih (fun j hj => h j (by omega)) j
        have hcn := h n (by omega)
        simp only [Strategy.play]
        rw [hhist]
        by_cases hc : c n
        · have hd : d n := hcn.1 hc
          simp [hc, hd]
        · have hd : ¬ d n := by
            intro hd
            exact hc (hcn.2 hd)
          simp [hc, hd]
      · simpa [Strategy.play] using ih (fun j hj => h j (by omega)) j

omit [Fact (finrank ℝ V = 2)] in
private lemma no_wins_of_play_angles (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop) (θ : ℝ)
    (havoid : ∀ k : ℕ, ∀ i : Fin 3,
      (∠ (((letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
          s.play t₀ c (k + 1) (Fin.last k))).points i)
          (((letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
          s.play t₀ c (k + 1) (Fin.last k))).points (i + 1))
          (((letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
          s.play t₀ c (k + 1) (Fin.last k))).points (i + 2))) ≠ θ) :
    ∀ k, ¬ WinsNow
      ((letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
        (s.play t₀ c) (k + 1) (Fin.last k))) θ := by
  intro k hk
  rcases hk with ⟨i, hi⟩
  exact havoid k i hi

private lemma initial_target_is_already_winning
    (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop)
    [∀ k, Decidable (c k)] :
    WinsNow ((s.play t₀ c) (0 + 1) (Fin.last 0))
      (∠ (t₀.points (0 : Fin 3)) (t₀.points (0 + 1)) (t₀.points (0 + 2))) := by
  simp [Strategy.play, WinsNow]
  exact ⟨0, rfl⟩

private lemma equilateral_hinit_bridge (t₀ : Triangle ℝ P)
    (heq : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3)
    (θ : ℝ) (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) :
    ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ≠ θ := by
  intro i hi
  have hθ : θ = Real.pi / 3 := by
    linarith [heq i, hi]
  apply (hpi 3)
  rw [hθ]
  ring

private lemma half_branch_preserves_no_multiples (t : Triangle ℝ P) (m : Move t) (θ : ℝ)
    (hgood : ∀ i : Fin 3, ∀ z : ℤ,
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ≠ (z : ℝ) * θ)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) :
    ∃ b : Bool, ∀ i : Fin 3, ∀ z : ℤ,
      ∠ ((m.half (b = true)).points i) ((m.half (b = true)).points (i + 1))
          ((m.half (b = true)).points (i + 2)) ≠ (z : ℝ) * θ := by
  have hsum0 := triangle_angle_sum_reordered t
  have hsum' : ∀ i : Fin 3,
      (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) +
      (∠ (t.points i) (t.points (i + 2)) (t.points (i + 1))) +
      (∠ (t.points (i + 2)) (t.points i) (t.points (i + 1))) = Real.pi := by
    intro i
    fin_cases i <;> simp [Fin.add_def]
    · exact hsum0
    · rw [angle_comm (t.points 1) (t.points 2) (t.points 0)]
      rw [angle_comm (t.points 1) (t.points 0) (t.points 2)]
      calc
        _ = ∠ (t.points 0) (t.points 1) (t.points 2) +
            ∠ (t.points 0) (t.points 2) (t.points 1) +
            ∠ (t.points 2) (t.points 0) (t.points 1) := by abel
        _ = Real.pi := hsum0
    · rw [angle_comm (t.points 2) (t.points 1) (t.points 0)]
      rw [angle_comm (t.points 1) (t.points 2) (t.points 0)]
      calc
        _ = ∠ (t.points 0) (t.points 1) (t.points 2) +
            ∠ (t.points 0) (t.points 2) (t.points 1) +
            ∠ (t.points 2) (t.points 0) (t.points 1) := by abel
        _ = Real.pi := hsum0
  have hsum := hsum' m.i
  have hangle_b : ∀ i : Fin 3,
      ∠ (t.points i) (t.points (i + 2)) (t.points (i + 1)) =
        ∠ (t.points (i + 1)) (t.points ((i + 1) + 1)) (t.points ((i + 1) + 2)) := by
    intro i
    fin_cases i <;> simp [Fin.add_def, angle_comm]
  have hangle_c : ∀ i : Fin 3,
      ∠ (t.points (i + 2)) (t.points i) (t.points (i + 1)) =
        ∠ (t.points (i + 2)) (t.points ((i + 2) + 1)) (t.points ((i + 2) + 2)) := by
    intro i
    fin_cases i <;> simp [Fin.add_def, angle_comm]
  have ha : ∀ z : ℤ,
      ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) ≠ (z : ℝ) * θ := by
    intro z
    exact hgood m.i z
  have hb : ∀ z : ℤ,
      ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) ≠ (z : ℝ) * θ := by
    intro z hz
    apply hgood (m.i + 1) z
    rw [← hangle_b m.i]
    exact hz
  have hc : ∀ z : ℤ,
      ∠ (t.points (m.i + 2)) (t.points m.i) (t.points (m.i + 1)) ≠ (z : ℝ) * θ := by
    intro z hz
    apply hgood (m.i + 2) z
    rw [← hangle_c m.i]
    exact hz
  rcases half_branch_avoids_multiples_correct t m θ hsum hpi ha hb hc with hT | hF
  · refine ⟨true, ?_⟩
    intro i z
    fin_cases i
    · exact hT z |>.1
    · exact hT z |>.2.1
    · exact hT z |>.2.2
  · refine ⟨false, ?_⟩
    intro i z
    fin_cases i
    · exact hF z |>.1
    · exact hF z |>.2.1
    · exact hF z |>.2.2

private lemma adversarial_coloring_of_hinit (s : Strategy P) (t₀ : Triangle ℝ P) (θ : ℝ)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ)
    (hinit : ∀ i : Fin 3, ∀ z : ℤ,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ≠ (z : ℝ) * θ) :
    ∃ c : ℕ → Prop, ∀ k : ℕ, ∀ i : Fin 3, ∀ z : ℤ,
      (letI : ∀ j, Decidable (c j) := fun j => Classical.propDecidable (c j)
       ∠ ((s.play t₀ c (k + 1) (Fin.last k)).points i)
          ((s.play t₀ c (k + 1) (Fin.last k)).points (i + 1))
          ((s.play t₀ c (k + 1) (Fin.last k)).points (i + 2)) ≠ (z : ℝ) * θ) := by
  classical
  let good : Triangle ℝ P → Prop := fun t => ∀ i : Fin 3, ∀ z : ℤ,
    ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ≠ (z : ℝ) * θ
  let chooseb : ∀ n : ℕ, (Fin (n + 1) → Triangle ℝ P) → Bool := fun n h =>
    if hh : good (h (Fin.last n)) then
      Classical.choose (half_branch_preserves_no_multiples (h (Fin.last n)) (s h) θ hh hpi)
    else true
  let next : ∀ n : ℕ, (Fin (n + 1) → Triangle ℝ P) → Fin (n + 2) → Triangle ℝ P :=
    fun n h =>
      letI : Decidable (chooseb n h = true) := Classical.propDecidable _
      fun i =>
        Fin.lastCases
          ((s h).half (chooseb n h = true))
          (fun j => h j) i
  let H : ∀ n : ℕ, Fin (n + 1) → Triangle ℝ P := fun n =>
    Nat.rec (motive := fun n => Fin (n + 1) → Triangle ℝ P)
      (fun _ => t₀) (fun n h => next n h) n
  let c : ℕ → Prop := fun n => chooseb n (H n) = true
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable (c k)
  have hplay : ∀ n : ℕ, ∀ i : Fin (n + 1),
      H n i = s.play t₀ c (n + 1) i := by
    intro n
    induction n with
    | zero =>
        intro i
        simp [H, Strategy.play]
    | succ n ih =>
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · change (next n (H n)) (Fin.last (n + 1)) =
            s.play t₀ c (n + 1 + 1) (Fin.last (n + 1))
          simp [next, Strategy.play, Fin.snoc_last]
          have hn : H n = s.play t₀ c (n + 1) := funext ih
          have hhalf :
              (s (H n)).half (c n) =
                (s (s.play t₀ c (n + 1))).half (c n) := by
            rw [hn]
          simpa only [c] using hhalf
        · simpa [H, next, Strategy.play] using ih j
  have hgood : ∀ n : ℕ, good (H n (Fin.last n)) := by
    intro n
    induction n with
    | zero =>
        simpa [good, H] using hinit
    | succ n ih =>
        have hs := half_branch_preserves_no_multiples
          (H n (Fin.last n)) (s (H n)) θ ih hpi
        letI : Decidable (chooseb n (H n) = true) := Classical.propDecidable _
        have hb : ∀ i : Fin 3, ∀ z : ℤ,
            ∠ (((s (H n)).half (chooseb n (H n) = true)).points i)
              (((s (H n)).half (chooseb n (H n) = true)).points (i + 1))
              (((s (H n)).half (chooseb n (H n) = true)).points (i + 2)) ≠
              (z : ℝ) * θ := by
          simpa only [chooseb, dif_pos ih] using (Classical.choose_spec hs)
        simpa [good, H, next] using hb
  refine ⟨c, ?_⟩
  intro k i z
  rw [← hplay k (Fin.last k)]
  exact hgood k i z

private lemma equilateral_hinit_all {t₀ : Triangle ℝ P}
    (heq : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3)
    (θ : ℝ) (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) :
    ∀ i : Fin 3, ∀ z : ℤ,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ≠ (z : ℝ) * θ := by
  intro i z hz
  apply hpi (3 * z)
  have hz' : Real.pi / 3 = (z : ℝ) * θ := by
    rw [← heq i]
    exact hz
  calc
    Real.pi = 3 * (Real.pi / 3) := by ring
    _ = 3 * ((z : ℝ) * θ) := by rw [hz']
    _ = ((3 * z : ℤ) : ℝ) * θ := by norm_num; ring

private lemma no_adversarial_coloring_at_its_initial_angle
    (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop)
    [∀ k, Decidable (c k)]
    (hno : ∀ k, ¬ WinsNow
      ((s.play t₀ c) (k + 1) (Fin.last k))
        (∠ (t₀.points (0 : Fin 3)) (t₀.points (0 + 1)) (t₀.points (0 + 2)))) :
    False := by
  apply hno 0
  simp [Strategy.play, WinsNow]
  exact ⟨0, rfl⟩

private lemma winning_mem_answer_of_hinit (s : Strategy P) (t₀ : Triangle ℝ P) (θ : ℝ)
    (hθpos : 0 < θ) (hθlt : θ < Real.pi)
    (hinit : ∀ i : Fin 3, ∀ z : ℤ,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ≠ (z : ℝ) * θ)
    (hs : s.Winning θ) : θ ∈ answer := by
  apply (answer_iff_not_pi_multiple θ hθpos hθlt).2
  intro hpi
  obtain ⟨c, hc⟩ := adversarial_coloring_of_hinit s t₀ θ hpi hinit
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable _
  apply (no_winning_of_one_adversarial_coloring s θ t₀ c ?_) hs
  intro k hwin
  rcases hwin with ⟨i, hi⟩
  have havoid := hc k i 1
  exact havoid (by simpa using hi)

private lemma candidate_pi_div_three_avoids (θ : ℝ)
    (hpi : ∀ z : ℤ, Real.pi ≠ (z : ℝ) * θ) :
    ∀ z : ℤ, Real.pi / 3 ≠ (z : ℝ) * θ := by
  intro z hz
  apply hpi (3 * z)
  calc
    Real.pi = 3 * ((z : ℝ) * θ) := by linarith
    _ = ((3 * z : ℤ) : ℝ) * θ := by norm_num; ring

private lemma pi_eq_nat_mul_pi_div (n : ℕ) (hn : 2 ≤ n) :
    Real.pi = (n : ℝ) * (Real.pi / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))
  field_simp [hn0]

private lemma pi_div_nat_rank_decomp (n : ℕ) (hn : 2 ≤ n) :
    Real.pi - Real.pi / (n : ℝ) =
      ((n - 1 : ℕ) : ℝ) * (Real.pi / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hcast]
  field_simp [hn0]

private lemma initial_no_win_of_hinit
    (s : Strategy P) (t₀ : Triangle ℝ P) (c : ℕ → Prop)
    [∀ k, Decidable (c k)] (θ : ℝ)
    (hinit : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ≠ θ) :
    ¬ WinsNow ((s.play t₀ c) (0 + 1) (Fin.last 0)) θ := by
  simp [Strategy.play, WinsNow]
  intro i hi
  exact hinit i hi

private lemma exists_equilateral_triangle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] :
    ∃ q : Fin 3 → P, ∀ i j, i ≠ j → dist (q i) (q j) = 1 := by
  letI : FiniteDimensional ℝ V := by
    apply FiniteDimensional.of_finrank_eq_succ
    exact_mod_cast (Fact.out : Module.finrank ℝ V = 2)
  let hf : finrank ℝ V = 2 := Fact.out
  let b := stdOrthonormalBasis ℝ V
  let i0 : Fin (finrank ℝ V) := ⟨0, by rw [hf]; decide⟩
  let i1 : Fin (finrank ℝ V) := ⟨1, by rw [hf]; decide⟩
  let u : V := b i0
  let v : V := b i1
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    exact b.norm_eq_one i0
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    exact b.norm_eq_one i1
  have huv : inner ℝ u v = 0 := by
    dsimp [u, v]
    exact b.orthonormal.2 (by
      intro h
      have hh := congrArg Fin.val h
      norm_num at hh)
  have hc : ‖(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v‖ = 1 := by
    have hsq : ‖(1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v‖ ^ 2 = 1 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, hu, hv, huv]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith [norm_nonneg ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v)]
  have hd : ‖u - ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v)‖ = 1 := by
    have hvect : u - ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v) =
        (1 / 2 : ℝ) • u - (Real.sqrt 3 / 2) • v := by
      module
    rw [hvect]
    have hsq : ‖(1 / 2 : ℝ) • u - (Real.sqrt 3 / 2) • v‖ ^ 2 = 1 := by
      rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, hu, hv, huv]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    nlinarith [norm_nonneg ((1 / 2 : ℝ) • u - (Real.sqrt 3 / 2) • v)]
  let p : P := (Classical.choice (triangle_nonempty (V := V) (P := P))).points 0
  let q : Fin 3 → P := ![p, u +ᵥ p,
    ((1 / 2 : ℝ) • u + (Real.sqrt 3 / 2) • v) +ᵥ p]
  refine ⟨q, ?_⟩
  have h01 : dist (q 0) (q 1) = 1 := by
    rw [dist_comm]
    dsimp [q]
    rw [dist_eq_norm_vsub V, vadd_vsub]
    exact hu
  have h02 : dist (q 0) (q 2) = 1 := by
    rw [dist_comm]
    dsimp [q]
    rw [dist_eq_norm_vsub V, vadd_vsub]
    exact hc
  have h12 : dist (q 1) (q 2) = 1 := by
    dsimp [q]
    rw [dist_eq_norm_vsub V, vsub_vadd_eq_vsub_sub, vadd_vsub]
    exact hd
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01
  · exact h02
  · calc
      dist (q 1) (q 0) = dist (q 0) (q 1) := dist_comm _ _
      _ = 1 := h01
  · exact (hij rfl).elim
  · exact h12
  · calc
      dist (q 2) (q 0) = dist (q 0) (q 2) := dist_comm _ _
      _ = 1 := h02
  · calc
      dist (q 2) (q 1) = dist (q 1) (q 2) := dist_comm _ _
      _ = 1 := h12
  · exact (hij rfl).elim

private lemma affineIndependent_of_pairwise_dist_one {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (q : Fin 3 → P)
    (hq : ∀ i j, i ≠ j → dist (q i) (q j) = 1) : AffineIndependent ℝ q := by
  classical
  rw [affineIndependent_iff_linearIndependent_vsub ℝ q 0]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let i1 : { x : Fin 3 // x ≠ 0 } := ⟨1, by decide⟩
  let i2 : { x : Fin 3 // x ≠ 0 } := ⟨2, by decide⟩
  have huniv : (Finset.univ : Finset { x : Fin 3 // x ≠ 0 }) = {i1, i2} := by
    ext x
    fin_cases x <;> simp [i1, i2]
  have hg' : g i1 • (q (i1 : Fin 3) -ᵥ q 0) + g i2 • (q (i2 : Fin 3) -ᵥ q 0) = 0 := by
    have hgs := hg
    change ((Finset.univ : Finset { x : Fin 3 // x ≠ 0 }).sum
      (fun x => g x • (q (x : Fin 3) -ᵥ q 0))) = 0 at hgs
    rw [huniv, Finset.sum_insert (by simp [i1, i2]), Finset.sum_singleton] at hgs
    simpa [i1, i2] using hgs
  let a : V := q (1 : Fin 3) -ᵥ q 0
  let b : V := q (2 : Fin 3) -ᵥ q 0
  have ha : ‖a‖ = 1 := by
    dsimp [a]
    rw [← dist_eq_norm_vsub V]
    exact hq 1 0 (by decide)
  have hb : ‖b‖ = 1 := by
    dsimp [b]
    rw [← dist_eq_norm_vsub V]
    exact hq 2 0 (by decide)
  have hab : ‖a - b‖ = 1 := by
    have hsub : a - b = q (1 : Fin 3) -ᵥ q 2 := by
      exact vsub_sub_vsub_cancel_right (q (1 : Fin 3)) (q 2) (q 0)
    rw [hsub, ← dist_eq_norm_vsub V]
    exact hq 1 2 (by decide)
  have hiab : inner ℝ a b = (1 / 2 : ℝ) := by
    have hnorm := norm_sub_sq_real a b
    rw [ha, hb] at hnorm
    have hnorm' : ‖a - b‖ ^ 2 = (1 : ℝ) := by rw [hab]; norm_num
    nlinarith
  have hg'' : g i1 • a + g i2 • b = 0 := by
    simpa [i1, i2, a, b] using hg'
  have hga := congrArg (fun x : V => inner ℝ x a) hg''
  have hgb := congrArg (fun x : V => inner ℝ x b) hg''
  simp [inner_add_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ha, hb, real_inner_comm, hiab] at hga hgb
  fin_cases i
  · dsimp [i1]
    nlinarith
  · dsimp [i2]
    nlinarith

private lemma winning_of_immediate_strategy_pre (θ : ℝ)
    (h : ∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (h (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  letI : ∀ k : ℕ, Decidable (c k) := fun k => Classical.propDecidable _
  by_cases hc : c 0
  · refine ⟨1, ?_⟩
    have hm := Classical.choose_spec (h ((s.play t₀ c) (0 + 1) (Fin.last 0)))
    have hlast := play_last_succ s t₀ c 0
    rw [hlast]
    simpa [s, hc] using hm.1
  · refine ⟨1, ?_⟩
    have hm := Classical.choose_spec (h ((s.play t₀ c) (0 + 1) (Fin.last 0)))
    have hlast := play_last_succ s t₀ c 0
    rw [hlast]
    simpa [s, hc] using hm.2

private lemma winning_after_one_move (θ : ℝ)
    (M : ∀ t : Triangle ℝ P, Move t)
    (sT : Strategy P) (hT : sT.Winning θ)
    (hF : ∀ t : Triangle ℝ P, WinsNow ((M t).half False) θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let lift : Strategy P := fun {k} h =>
    match k with
    | 0 => by simpa using M (h (Fin.last 0))
    | k + 1 =>
        let htail : Fin (k + 1) → Triangle ℝ P := fun j => h j.succ
        have he : htail (Fin.last k) = h (Fin.last (k + 1)) := by
          apply congrArg h
          apply Fin.ext
          simp
        let q := sT (k := k) htail
        ⟨q.i, q.p, by
          rw [← he]
          exact q.sbtw_p⟩
  refine ⟨lift, ?_⟩
  intro t₀ c
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable _
  by_cases hc : c 0
  · let child := (M t₀).half True
    let d : ℕ → Prop := fun j => c (j + 1)
    letI : ∀ k, Decidable (d k) := fun k => Classical.propDecidable _
    obtain ⟨k, hk⟩ := hT child d
    refine ⟨k + 1, ?_⟩
    have htail : ∀ n : ℕ, ∀ i : Fin (n + 1),
        lift.play t₀ c (n + 2) i.succ = sT.play child d (n + 1) i := by
      intro n
      induction n with
      | zero =>
          intro i
          fin_cases i
          simp [lift, child, Strategy.play, hc]
      | succ n ih =>
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · let h : Fin (n + 2) → Triangle ℝ P :=
                Fin.snoc (lift.play t₀ c (n + 1))
                  ((lift (lift.play t₀ c (n + 1))).half (c n))
            have hfun : (fun j : Fin (n + 1) => h j.succ) =
                sT.play child d (n + 1) := by
              funext j
              dsimp [h]
              exact ih j
            have hidx : (Fin.last n).succ = Fin.last (n + 1) := by
              apply Fin.ext
              simp
            have htri : h (Fin.last (n + 1)) =
                sT.play child d (n + 1) (Fin.last n) := by
              rw [← hidx]
              exact congrFun hfun (Fin.last n)
            have hpts : (h (Fin.last (n + 1))).points =
                (sT.play child d (n + 1) (Fin.last n)).points :=
              congrArg (fun t : Triangle ℝ P => t.points) htri
            have hi := congrArg (fun x : Fin (n + 1) → Triangle ℝ P =>
              (sT x).i) hfun
            have hp := congrArg (fun x : Fin (n + 1) → Triangle ℝ P =>
              (sT x).p) hfun
            have hi' : (lift h).i = (sT (sT.play child d (n + 1))).i := by
              simpa only [lift] using hi
            have hp' : (lift h).p = (sT (sT.play child d (n + 1))).p := by
              simpa only [lift] using hp
            have hhalf : (lift h).half (c (n + 1)) =
                (sT (sT.play child d (n + 1))).half (c (n + 1)) := by
              obtain ⟨l0, l1, l2⟩ :=
                move_half_points (h (Fin.last (n + 1))) (lift h) (c (n + 1))
              obtain ⟨r0, r1, r2⟩ :=
                move_half_points (sT.play child d (n + 1) (Fin.last n))
                  (sT (sT.play child d (n + 1))) (c (n + 1))
              have e0mid : (h (Fin.last (n + 1))).points (lift h).i =
                  (sT.play child d (n + 1) (Fin.last n)).points
                    (sT (sT.play child d (n + 1))).i := by
                rw [hpts, hi']
              have e1mid :
                  (if c (n + 1) then
                    (h (Fin.last (n + 1))).points ((lift h).i + 1)
                   else (h (Fin.last (n + 1))).points ((lift h).i + 2)) =
                    (if c (n + 1) then
                      (sT.play child d (n + 1) (Fin.last n)).points
                        ((sT (sT.play child d (n + 1))).i + 1)
                     else (sT.play child d (n + 1) (Fin.last n)).points
                        ((sT (sT.play child d (n + 1))).i + 2)) := by
                rw [hpts, hi']
              have e2mid : (lift h).p =
                  (sT (sT.play child d (n + 1))).p := hp'
              have e0 : ((lift h).half (c (n + 1))).points 0 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 0 :=
                l0.trans (e0mid.trans r0.symm)
              have e1 : ((lift h).half (c (n + 1))).points 1 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 1 :=
                l1.trans (e1mid.trans r1.symm)
              have e2 : ((lift h).half (c (n + 1))).points 2 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 2 :=
                l2.trans (e2mid.trans r2.symm)
              ext z
              fin_cases z
              · simpa using e0
              · simpa using e1
              · simpa using e2
            simp [Strategy.play]
            simpa [h] using hhalf
          · rw [show lift.play t₀ c (n + 1 + 2) =
                Fin.snoc (lift.play t₀ c (n + 1 + 1))
                  ((lift (lift.play t₀ c (n + 1 + 1))).half (c (n + 1))) from rfl]
            rw [show sT.play child d (n + 1 + 1) =
                Fin.snoc (sT.play child d (n + 1))
                  ((sT (sT.play child d (n + 1))).half (d n)) from rfl]
            have hidx : j.castSucc.succ = (j.succ).castSucc := by rfl
            rw [hidx]
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            simpa [Nat.add_assoc] using ih j
    rw [show lift.play t₀ c (k + 1 + 1) (Fin.last (k + 1)) =
        sT.play child d (k + 1) (Fin.last k) from by
          simpa [Nat.add_assoc] using htail k (Fin.last k)]
    exact hk
  · refine ⟨1, ?_⟩
    have hlast := play_last_succ lift t₀ c 0
    rw [hlast]
    simpa [lift, Strategy.play, hc] using hF t₀

private lemma successor_pi_rank_identity (n : ℕ) (hn : 2 ≤ n) :
    Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) =
      (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn0]
  norm_num [Nat.cast_add]

omit [Fact (finrank ℝ V = 2)] in
private lemma hreverse_of_explicit_successor
    (hbase : ∃ s : Strategy P, s.Winning (Real.pi / (2 : ℝ)))
    (hstep : ∀ n : ℕ, 2 ≤ n →
      (∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ))) →
      ∃ s : Strategy P, s.Winning (Real.pi / ((n + 1 : ℕ) : ℝ))) :
    ∀ n : ℕ, 2 ≤ n → ∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ)) := by
  intro n hn
  apply winning_predicate_of_successor_step
    (W := fun n : ℕ => ∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ)))
  · simpa using hbase
  · exact hstep
  · exact hn

private lemma successor_rank_angle_step (n : ℕ) (hn : 2 ≤ n) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    a + b + (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi →
    b < b + Real.pi / ((n + 1 : ℕ) : ℝ) ∧
      b + Real.pi / ((n + 1 : ℕ) : ℝ) <
        b + (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) ∧
      Real.pi - a - (b + Real.pi / ((n + 1 : ℕ) : ℝ)) =
        ((n - 1 : ℕ) : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) ∧
      (b + Real.pi / ((n + 1 : ℕ) : ℝ)) - b =
        Real.pi / ((n + 1 : ℕ) : ℝ) := by
  intro hsum
  exact integer_rank_step a b (Real.pi / ((n + 1 : ℕ) : ℝ)) n hn ha hb
    (div_pos Real.pi_pos (by positivity))
    (by simpa [add_assoc] using hsum)

private lemma successor_rank_angle_data (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.pi / ((n + 1 : ℕ) : ℝ) ∧
      Real.pi / ((n + 1 : ℕ) : ℝ) < Real.pi ∧
      Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) =
        (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hpos : 0 < Real.pi / ((n + 1 : ℕ) : ℝ) := by positivity
  have hnpos : 0 < n := lt_of_lt_of_le (by decide) hn
  have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hden : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    have hden' : (1 : ℝ) < (n : ℝ) + 1 := by linarith
    simpa [Nat.cast_add] using hden'
  have hlt : Real.pi / ((n + 1 : ℕ) : ℝ) < Real.pi := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))).2
    have hmul := mul_lt_mul_of_pos_left hden Real.pi_pos
    simpa using hmul
  exact ⟨hpos, hlt, successor_pi_rank_identity n hn⟩

omit [Fact (finrank ℝ V = 2)] in
private lemma hreverse_of_explicit_successor_check
    (hbase : ∃ s : Strategy P, s.Winning (Real.pi / (2 : ℝ)))
    (hstep : ∀ n : ℕ, 2 ≤ n →
      (∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ))) →
      ∃ s : Strategy P, s.Winning (Real.pi / ((n + 1 : ℕ) : ℝ))) :
    ∀ n : ℕ, 2 ≤ n → ∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ)) := by
  intro n hn
  apply winning_predicate_of_successor_step
    (W := fun n : ℕ => ∃ s : Strategy P, s.Winning (Real.pi / (n : ℝ)))
  · simpa using hbase
  · exact hstep
  · exact hn

private lemma candidate_unit_transfer_transition
    (n : ℕ) (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 1 < c)
    (hsum : a + b + c = (n : ℝ)) :
    0 < b + 1 ∧
      0 < c - 1 ∧
      0 < (n : ℝ) - b - 1 ∧
      a + (b + 1) + (c - 1) = (n : ℝ) ∧
      b + ((n : ℝ) - b - 1) + 1 = (n : ℝ) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private lemma candidate_residue_clear_transition
    (n : ℕ) (a b c : ℝ)
    (ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hbN : b < (n : ℝ) - 1)
    (hc : 0 < c)
    (hsum : a + b + c = (n : ℝ)) :
    0 < (n : ℝ) - 1 - b ∧
      0 < 1 - a ∧
      a + ((n : ℝ) - 1) + (1 - a) = (n : ℝ) ∧
      b + 1 + ((n : ℝ) - 1 - b) = (n : ℝ) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

private lemma candidate_canonical_rank_transition
    (n : ℕ) (a b : ℝ)
    (hn : 2 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hsum : a + b + (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi) :
    b < b + Real.pi / ((n + 1 : ℕ) : ℝ) ∧
      b + Real.pi / ((n + 1 : ℕ) : ℝ) <
        b + (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) ∧
      Real.pi - a - (b + Real.pi / ((n + 1 : ℕ) : ℝ)) =
        ((n - 1 : ℕ) : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) ∧
      (b + Real.pi / ((n + 1 : ℕ) : ℝ)) - b =
        Real.pi / ((n + 1 : ℕ) : ℝ) := by
  exact successor_rank_angle_step n hn a b ha hb hsum

private lemma candidate_unit_transfer_branch_angles
    (t : Triangle ℝ P) (m : Move t) (a b c θ : ℝ)
    (ha :
      ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) = a)
    (hb :
      ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) = b)
    (hx :
      ∠ (t.points (m.i + 1)) m.p (t.points m.i) = b + θ)
    (hsum : a + b + c = Real.pi) :
    (∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
        ((m.half True).points (2 : Fin 3)) = a ∧
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) = b + θ ∧
      ∠ ((m.half True).points (2 : Fin 3)) ((m.half True).points (0 : Fin 3))
        ((m.half True).points (1 : Fin 3)) = c - θ) ∧
    (∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
        ((m.half False).points (2 : Fin 3)) = b ∧
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) = a + c - θ ∧
      ∠ ((m.half False).points (2 : Fin 3)) ((m.half False).points (0 : Fin 3))
        ((m.half False).points (1 : Fin 3)) = θ) := by
  have hrel := half_branch_angle_relations t m
  dsimp at hrel
  rcases hrel with ⟨⟨hT0, hT1, hT2⟩, ⟨hF0, hF1, hF2⟩⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hT0, ha]
  · rw [hT1, hx]
  · rw [hT2, ha, hx]
    linarith
  · rw [hF0, hb]
  · rw [hF1, hx]
    linarith [hsum]
  · rw [hF2, hx, hb]
    ring

private lemma candidate_residue_clear_branch_angles
    (t : Triangle ℝ P) (m : Move t) (a b θ : ℝ)
    (ha :
      ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) = a)
    (hb :
      ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) = b)
    (hx :
      ∠ (t.points (m.i + 1)) m.p (t.points m.i) = Real.pi - θ) :
    (∠ ((m.half True).points (0 : Fin 3)) ((m.half True).points (1 : Fin 3))
        ((m.half True).points (2 : Fin 3)) = a ∧
      ∠ ((m.half True).points (1 : Fin 3)) ((m.half True).points (2 : Fin 3))
        ((m.half True).points (0 : Fin 3)) = Real.pi - θ ∧
      ∠ ((m.half True).points (2 : Fin 3)) ((m.half True).points (0 : Fin 3))
        ((m.half True).points (1 : Fin 3)) = θ - a) ∧
    (∠ ((m.half False).points (0 : Fin 3)) ((m.half False).points (1 : Fin 3))
        ((m.half False).points (2 : Fin 3)) = b ∧
      ∠ ((m.half False).points (1 : Fin 3)) ((m.half False).points (2 : Fin 3))
        ((m.half False).points (0 : Fin 3)) = θ ∧
      ∠ ((m.half False).points (2 : Fin 3)) ((m.half False).points (0 : Fin 3))
        ((m.half False).points (1 : Fin 3)) = Real.pi - θ - b) := by
  have hrel := half_branch_angle_relations t m
  dsimp at hrel
  rcases hrel with ⟨⟨hT0, hT1, hT2⟩, ⟨hF0, hF1, hF2⟩⟩
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hT0, ha]
  · rw [hT1, hx]
  · rw [hT2, ha, hx] <;> ring
  · rw [hF0, hb]
  · rw [hF1, hx] <;> ring
  · rw [hF2, hx, hb] <;> ring

private lemma result_forward_helper (t₀ : Triangle ℝ P)
    (heq : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3) :
    ∀ θ : ℝ, (∃ s : Strategy P, s.Winning θ) → θ ∈ answer := by
  intro θ hθ
  rcases hθ with ⟨s, hs⟩
  obtain ⟨hθpos, hθlt⟩ := winning_strategy_open_interval s θ hs t₀
  apply (answer_iff_not_pi_multiple θ hθpos hθlt).2
  intro hpi
  have hinit := equilateral_hinit_all heq θ hpi
  have hmem := winning_mem_answer_of_hinit s t₀ θ hθpos hθlt hinit hs
  exact (answer_mem_pi_multiple θ hmem) hpi

private lemma winsNow_of_explicit_angle
    (t : Triangle ℝ P) (θ : ℝ) (i : Fin 3)
    (h : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) = θ) :
    WinsNow t θ := by
  exact ⟨i, h⟩

private lemma equilateral_triangle_with_cyclic_angles {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] :
    ∃ t₀ : Triangle ℝ P, ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3 := by
  obtain ⟨q, hq⟩ := exists_equilateral_triangle (V := V) (P := P)
  have hqa : AffineIndependent ℝ q :=
    affineIndependent_of_pairwise_dist_one q hq
  let t₀ : Triangle ℝ P := ⟨q, hqa⟩
  have ht_eq : t₀.Equilateral := by
    refine ⟨1, ?_⟩
    intro i j hij
    simpa [t₀] using hq i j hij
  refine ⟨t₀, ?_⟩
  intro i
  apply ht_eq.angle_eq_pi_div_three
  all_goals fin_cases i <;> decide

private lemma canonical_rank_premise_reduces
    (n : ℕ) (a b : ℝ) (hn : 2 ≤ n)
    (hsum : a + b + (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi) :
    a + b = Real.pi / ((n + 1 : ℕ) : ℝ) := by
  have hπ := successor_pi_rank_identity n hn
  linarith

private lemma result_altitudeFoot_orthogonality (t : Triangle ℝ P) (i : Fin 3) :
    @inner ℝ V _ (t.points ((i + 1 : Fin 3)) -ᵥ t.altitudeFoot i)
      (t.points i -ᵥ t.altitudeFoot i) = 0 := by
  apply t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
  fin_cases i <;> decide

private lemma result_altitudeFoot_right_angle (t : Triangle ℝ P) (i : Fin 3)
    (hxy : t.points (i + 1) ≠ t.altitudeFoot i)
    (hzy : t.points i ≠ t.altitudeFoot i)
    (h : @inner ℝ V _ (t.points (i + 1) -ᵥ t.altitudeFoot i)
      (t.points i -ᵥ t.altitudeFoot i) = 0) :
    ∠ (t.points (i + 1)) (t.altitudeFoot i) (t.points i) = Real.pi / 2 := by
  change InnerProductGeometry.angle (t.points (i + 1) -ᵥ t.altitudeFoot i)
      (t.points i -ᵥ t.altitudeFoot i) = Real.pi / 2
  exact (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp h

private lemma result_strategy_winning_const (s : Strategy P) (θ : ℝ) :
    Strategy.Winning (fun {k} => s) θ = s.Winning θ := by
  rfl

private lemma result_strategy_const_use (s : Strategy P) (θ : ℝ) (h : s.Winning θ) :
    Strategy.Winning (fun {k} => s) θ := by
  rw [result_strategy_winning_const]
  exact h

private lemma result_true_half_altitude_right_angle
    (t : Triangle ℝ P) (i : Fin 3)
    (hp : Sbtw ℝ (t.points (i + 1)) (t.altitudeFoot i) (t.points (i + 2)))
    (hxy : t.points (i + 1) ≠ t.altitudeFoot i)
    (hzy : t.points i ≠ t.altitudeFoot i)
    (hperp : @inner ℝ V _ (t.points (i + 1) -ᵥ t.altitudeFoot i)
      (t.points i -ᵥ t.altitudeFoot i) = 0) :
    WinsNow ((⟨i, t.altitudeFoot i, hp⟩ : Move t).half True) (Real.pi / 2) := by
  refine ⟨1, ?_⟩
  simpa [WinsNow, Move.half] using
    (result_altitudeFoot_right_angle t i hxy hzy hperp)

private lemma result_altitudeFoot_mem_affineSpan (t : Triangle ℝ P) (i : Fin 3) :
    t.altitudeFoot i ∈ affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
  exact t.altitudeFoot_mem_affineSpan_faceOpposite i

private lemma candidate_targeted_move_witness
    (t : Triangle ℝ P) (i : Fin 3) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    Sbtw ℝ (t.points (i + 1))
      (AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
      (t.points (i + 2)) := by
  refine (sbtw_iff_mem_image_Ioo_and_ne).2 ⟨?_, ?_⟩
  · exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
  · intro h
    have h' : i + 1 = i + 2 := t.independent.injective h
    omega

private lemma candidate_targeted_move_transport
    (t : Triangle ℝ P) (i : Fin 3) (r b θ : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hangle :
      ∠ (t.points (i + 1))
        (AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
        (t.points i) = b + θ) :
    ∃ m : Move t,
      m.i = i ∧
      m.p = AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r ∧
      ∠ (t.points (i + 1)) m.p (t.points i) = b + θ := by
  have hp :
      Sbtw ℝ (t.points (i + 1))
        (AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
        (t.points (i + 2)) := by
    refine (sbtw_iff_mem_image_Ioo_and_ne).2 ⟨?_, ?_⟩
    · exact ⟨r, ⟨hr0, hr1⟩, rfl⟩
    · intro h
      have h' : i + 1 = i + 2 := t.independent.injective h
      omega
  let m : Move t :=
    { i := i
      p := AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r
      sbtw_p := hp }
  refine ⟨m, rfl, rfl, ?_⟩
  simpa [m] using hangle

private lemma parametric_pi_sub_div_nat (n : ℕ) (hn : 0 < n) :
    Real.pi - Real.pi / (n : ℝ) =
      ((n - 1 : ℕ) : ℝ) * (Real.pi / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))]
    norm_num
  rw [hcast]
  field_simp [hn0]

private lemma result_forward_from_cyclic_angles (t₀ : Triangle ℝ P)
    (heq : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3) :
    ∀ θ : ℝ, (∃ s : Strategy P, s.Winning θ) → θ ∈ answer := by
  simpa using (result_forward_helper t₀ heq)

private lemma equilateral_triangle_exists_for_result {V P : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] :
    ∃ t₀ : Triangle ℝ P, ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = Real.pi / 3 := by
  simpa using (equilateral_triangle_with_cyclic_angles (V := V) (P := P))

private lemma result_triangle_not_collinear (t : Triangle ℝ P) :
    ¬ Collinear ℝ ({t.points 0, t.points 1, t.points 2} : Set P) := by
  have h := (affineIndependent_iff_not_collinear (k := ℝ) (p := t.points)).mp t.independent
  intro hcol
  have hs : Set.range t.points = ({t.points 0, t.points 1, t.points 2} : Set P) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  apply h
  simpa [hs] using hcol

private lemma result_two_acute_angles_v2 (t : Triangle ℝ P) :
    ∃ i : Fin 3,
      ∠ (t.points (i + 1)) (t.points (i + 2)) (t.points i) < Real.pi / 2 ∧
      ∠ (t.points (i + 2)) (t.points i) (t.points (i + 1)) < Real.pi / 2 := by
  let a : ℝ := ∠ (t.points 0) (t.points 1) (t.points 2)
  let b : ℝ := ∠ (t.points 1) (t.points 2) (t.points 0)
  let c : ℝ := ∠ (t.points 2) (t.points 0) (t.points 1)
  have hcol := result_triangle_not_collinear t
  have h0 : 0 < a := by
    simpa [a] using angle_pos_of_not_collinear hcol
  have h1 : 0 < b := by
    apply angle_pos_of_not_collinear
    rw [show ({t.points 1, t.points 2, t.points 0} : Set P) =
        {t.points 0, t.points 1, t.points 2} by
      apply Set.ext
      intro x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact hcol
  have h2 : 0 < c := by
    apply angle_pos_of_not_collinear
    rw [show ({t.points 2, t.points 0, t.points 1} : Set P) =
        {t.points 0, t.points 1, t.points 2} by
      apply Set.ext
      intro x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto]
    exact hcol
  have hne : t.points 1 ≠ t.points 0 := by
    intro h
    have hi : (1 : Fin 3) = 0 := t.independent.injective h
    omega
  have hsum : a + b + c = Real.pi := by
    simpa [a, b, c] using
      (angle_add_angle_add_angle_eq_pi (t.points 2) hne)
  by_cases ha : a < Real.pi / 2
  · by_cases hb : b < Real.pi / 2
    · refine ⟨2, ?_, ?_⟩
      · simpa [a] using ha
      · simpa [b] using hb
    · have hc : c < Real.pi / 2 := by
        have hb' : Real.pi / 2 ≤ b := le_of_not_gt hb
        nlinarith [Real.pi_pos]
      refine ⟨1, ?_, ?_⟩
      · simpa [c] using hc
      · simpa [a] using ha
  · by_cases hb : b < Real.pi / 2
    · have hc : c < Real.pi / 2 := by
        have ha' : Real.pi / 2 ≤ a := le_of_not_gt ha
        nlinarith [Real.pi_pos]
      refine ⟨0, ?_, ?_⟩
      · simpa [b] using hb
      · simpa [c] using hc
    · have ha' : Real.pi / 2 ≤ a := le_of_not_gt ha
      have hb' : Real.pi / 2 ≤ b := le_of_not_gt hb
      nlinarith [Real.pi_pos]

private lemma result_altitudeFoot_both_halves
    (t : Triangle ℝ P) (i : Fin 3)
    (hp : Sbtw ℝ (t.points (i + 1)) (t.altitudeFoot i) (t.points (i + 2))) :
    ∃ m : Move t,
      WinsNow (m.half True) (Real.pi / 2) ∧
      WinsNow (m.half False) (Real.pi / 2) := by
  have hxy1 : t.points (i + 1) ≠ t.altitudeFoot i := by aesop
  have hxy2 : t.points (i + 2) ≠ t.altitudeFoot i := by aesop
  have hzy : t.points i ≠ t.altitudeFoot i := by aesop
  let m : Move t := ⟨i, t.altitudeFoot i, hp⟩
  refine ⟨m, ?_, ?_⟩
  · simpa [m] using
      (result_true_half_altitude_right_angle t i hp hxy1 hzy
        (result_altitudeFoot_orthogonality t i))
  · refine ⟨1, ?_⟩
    simp [m, WinsNow, Move.half]
    change InnerProductGeometry.angle (t.points (i + 2) -ᵥ t.altitudeFoot i)
        (t.points i -ᵥ t.altitudeFoot i) = Real.pi / 2
    apply (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp
    apply t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
    fin_cases i <;> decide

private lemma result_angle_inner_pos
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {p q r : P} (hpq : p ≠ q) (hrq : r ≠ q)
    (h : ∠ p q r < Real.pi / 2) :
    @inner ℝ V _ (p -ᵥ q) (r -ᵥ q) > 0 := by
  change Real.arccos (@inner ℝ V _ (p -ᵥ q) (r -ᵥ q) /
      (‖p -ᵥ q‖ * ‖r -ᵥ q‖)) < Real.pi / 2 at h
  rw [Real.arccos_lt_pi_div_two] at h
  have hnorm : 0 < ‖p -ᵥ q‖ * ‖r -ᵥ q‖ := by
    exact mul_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hpq))
      (norm_pos_iff.mpr (vsub_ne_zero.mpr hrq))
  have hh : 0 < @inner ℝ V _ (p -ᵥ q) (r -ᵥ q) /
      (‖p -ᵥ q‖ * ‖r -ᵥ q‖) := h
  rcases (div_pos_iff.mp hh) with hpos | hneg
  · exact hpos.1
  · exfalso
    nlinarith [hnorm, hneg.2]

private lemma result_sbtw_from_projection
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    {A X Y F : P}
    (hmem : F ∈ affineSpan ℝ ({X, Y} : Set P))
    (hAX : A ≠ X) (hYX : Y ≠ X) (hXY : X ≠ Y) (hAY : A ≠ Y)
    (hinner1 : @inner ℝ V _ (A -ᵥ X) (Y -ᵥ X) > 0)
    (hinner2 : @inner ℝ V _ (X -ᵥ Y) (A -ᵥ Y) > 0)
    (horthX : @inner ℝ V _ (X -ᵥ F) (A -ᵥ F) = 0)
    (horthY : @inner ℝ V _ (Y -ᵥ F) (A -ᵥ F) = 0) :
    Sbtw ℝ X F Y := by
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).mp hmem
  have hFX : F ≠ X := by
    intro h
    have hz := horthY
    rw [h] at hz
    rw [real_inner_comm] at hz
    linarith
  have hFY : F ≠ Y := by
    intro h
    have hz := horthX
    rw [h] at hz
    linarith
  have hr0 : r ≠ 0 := by
    intro hz
    apply hFX
    rw [← hr]
    simp [hz]
  have hr1 : r ≠ 1 := by
    intro hz
    apply hFY
    rw [← hr]
    simp [hz]
  have horth : @inner ℝ V _ (X -ᵥ (AffineMap.lineMap X Y r))
      (A -ᵥ (AffineMap.lineMap X Y r)) = 0 := by
    rw [hr]
    exact horthX
  rw [AffineMap.lineMap_apply] at horth
  rw [vsub_vadd_eq_vsub_sub, vsub_vadd_eq_vsub_sub] at horth
  simp only [vsub_self, zero_sub] at horth
  rw [inner_neg_left, real_inner_smul_left, inner_sub_right,
    real_inner_smul_right] at horth
  have hprod : r * (@inner ℝ V _ (Y -ᵥ X) (A -ᵥ X) -
      r * @inner ℝ V _ (Y -ᵥ X) (Y -ᵥ X)) = 0 := by
    nlinarith [horth]
  have hrel : @inner ℝ V _ (X -ᵥ Y) (A -ᵥ Y) =
      @inner ℝ V _ (Y -ᵥ X) (Y -ᵥ X) -
        @inner ℝ V _ (Y -ᵥ X) (A -ᵥ X) := by
    have hAYvec : A -ᵥ Y = (A -ᵥ X) - (Y -ᵥ X) :=
      (vsub_sub_vsub_cancel_right A Y X).symm
    have hXYvec : X -ᵥ Y = -(Y -ᵥ X) :=
      (neg_vsub_eq_vsub_rev Y X).symm
    rw [hXYvec, hAYvec, inner_neg_left, inner_sub_right]
    ring
  have hnorm : 0 < @inner ℝ V _ (Y -ᵥ X) (Y -ᵥ X) :=
    real_inner_self_pos.mpr (vsub_ne_zero.mpr hYX)
  have heq : @inner ℝ V _ (Y -ᵥ X) (A -ᵥ X) =
      r * @inner ℝ V _ (Y -ᵥ X) (Y -ᵥ X) := by
    rcases mul_eq_zero.mp hprod with hz | hz
    · exact False.elim (hr0 hz)
    · linarith
  have hrpos : 0 < r := by
    rw [real_inner_comm] at hinner1
    rw [heq] at hinner1
    nlinarith
  have hrlt : r < 1 := by
    rw [hrel, heq] at hinner2
    nlinarith
  refine (sbtw_iff_mem_image_Ioo_and_ne).2 ⟨?_, hXY⟩
  exact ⟨r, ⟨hrpos, hrlt⟩, hr⟩

private lemma result_altitudeFoot_mem_pair (t : Triangle ℝ P) (i : Fin 3) :
    t.altitudeFoot (i + 1) ∈
      affineSpan ℝ ({t.points (i + 2), t.points i} : Set P) := by
  have hrange :
      Set.range (t.faceOpposite (i + 1)).points =
        ({t.points (i + 2), t.points i} : Set P) := by
    rw [Affine.Simplex.range_faceOpposite_points]
    fin_cases i
    · ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp_all
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨2, by decide, rfl⟩
        · exact ⟨0, by decide, rfl⟩
    · ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp_all
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨0, by decide, rfl⟩
        · exact ⟨1, by decide, rfl⟩
    · ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        fin_cases j <;> simp_all
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨1, by decide, rfl⟩
        · exact ⟨2, by decide, rfl⟩
  rw [← hrange]
  exact result_altitudeFoot_mem_affineSpan t (i + 1)

private lemma result_altitudeFoot_c_orthogonality (t : Triangle ℝ P) (i : Fin 3) :
    @inner ℝ V _ (t.points ((i + 2 : Fin 3)) -ᵥ t.altitudeFoot i)
      (t.points i -ᵥ t.altitudeFoot i) = 0 := by
  apply t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
  fin_cases i <;> decide

private lemma result_false_half_right_angle {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Triangle ℝ P) (i : Fin 3)
    (p : P) (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2)))
    (hangle : ∠ (t.points (i + 1)) p (t.points i) = Real.pi / 2) :
    WinsNow ((⟨i, p, hp⟩ : Move t).half False) (Real.pi / 2) := by
  have hinner : @inner ℝ V _ (t.points (i + 1) -ᵥ p) (t.points i -ᵥ p) = 0 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mpr hangle
  obtain ⟨⟨r, hr, rfl⟩, hne⟩ := (sbtw_iff_mem_image_Ioo_and_ne).1 hp
  have hr0 : r ≠ 0 := ne_of_gt hr.1
  have hrel :
      t.points (i + 2) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r =
        ((r - 1) / r) •
          (t.points (i + 1) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r) := by
    have hscalar : ((r - 1) / r) * r = r - 1 := by
      field_simp [hr0]
    simp [AffineMap.lineMap, vsub_vadd_eq_vsub_sub]
    rw [smul_smul, hscalar]
    module
  have hinner' : @inner ℝ V _
      (t.points (i + 2) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
      (t.points i -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r) = 0 := by
    calc
      _ = ((r - 1) / r) * @inner ℝ V _
          (t.points (i + 1) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
          (t.points i -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r) := by
        rw [hrel, real_inner_smul_left]
      _ = 0 := by rw [hinner]; ring
  have hangle' :
      ∠ (t.points (i + 2)) (AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r) (t.points i) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp hinner'
  refine ⟨1, ?_⟩
  simpa [WinsNow, Move.half] using hangle'

private lemma result_base_immediate_halves {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Triangle ℝ P) (i : Fin 3)
    (p : P) (hp : Sbtw ℝ (t.points (i + 2)) p (t.points i))
    (horthX : @inner ℝ V _ (t.points (i + 2) -ᵥ p) (t.points (i + 1) -ᵥ p) = 0) :
    ∃ m : Move t, WinsNow (m.half True) (Real.pi / 2) ∧ WinsNow (m.half False) (Real.pi / 2) := by
  have hm : Sbtw ℝ (t.points ((i + 1) + 1)) p (t.points ((i + 1) + 2)) := by
    convert hp using 1 <;> fin_cases i <;> rfl
  let m : Move t := ⟨i + 1, p, hm⟩
  have hangleX : ∠ (t.points (i + 2)) p (t.points (i + 1)) = Real.pi / 2 :=
    (InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two _ _).mp horthX
  refine ⟨m, ?_⟩
  constructor
  · refine ⟨1, ?_⟩
    change ∠ (t.points ((i + 1) + 1)) p (t.points (i + 1)) = Real.pi / 2
    convert hangleX using 1 <;> fin_cases i <;> rfl
  · apply result_false_half_right_angle t (i + 1) p hm
    convert hangleX using 1 <;> fin_cases i <;> rfl

private lemma result_collinear_vsub_relation {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] (t : Triangle ℝ P) (i : Fin 3)
    (r : ℝ) (hr0 : r ≠ 0) :
      t.points (i + 2) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r =
        ((r - 1) / r) •
          (t.points (i + 1) -ᵥ AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r) := by
  have hscalar : ((r - 1) / r) * r = r - 1 := by
    field_simp [hr0]
  simp [AffineMap.lineMap, vsub_vadd_eq_vsub_sub]
  rw [smul_smul, hscalar]
  module

private lemma result_predecessor_successor_angles_ne (n : ℕ) (hn : 2 ≤ n) :
    Real.pi / (n : ℝ) ≠ Real.pi / ((n + 1 : ℕ) : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnp0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  intro h
  field_simp [hn0, hnp0] at h
  norm_num at h

private lemma result_scalar_cancel (r : ℝ) (hr0 : r ≠ 0) : ((r - 1) / r) * r = r - 1 := by
  field_simp [hr0]

private lemma result_base_strategy {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] :
    ∃ s : Strategy P, s.Winning (Real.pi / (2 : ℝ)) := by
  apply winning_of_immediate_strategy_pre
  intro t
  obtain ⟨i, hi1, hi2⟩ := result_two_acute_angles_v2 t
  have hAX : t.points (i + 1) ≠ t.points (i + 2) := by
    intro h
    have h' : i + 1 = i + 2 := t.independent.injective h
    omega
  have hYX : t.points i ≠ t.points (i + 2) := by
    intro h
    have h' : i = i + 2 := t.independent.injective h
    omega
  have hXY : t.points (i + 2) ≠ t.points i := by
    intro h
    have h' : i + 2 = i := t.independent.injective h
    omega
  have hAY : t.points (i + 1) ≠ t.points i := by
    intro h
    have h' : i + 1 = i := t.independent.injective h
    omega
  have hinner1 := result_angle_inner_pos hAX hYX hi1
  have hinner2 := result_angle_inner_pos hXY hAY hi2
  have horthX :
      @inner ℝ V _ (t.points (i + 2) -ᵥ t.altitudeFoot (i + 1))
        (t.points (i + 1) -ᵥ t.altitudeFoot (i + 1)) = 0 := by
    fin_cases i
    · simpa using (result_altitudeFoot_orthogonality t (1 : Fin 3))
    · simpa using (result_altitudeFoot_orthogonality t (2 : Fin 3))
    · simpa using (result_altitudeFoot_orthogonality t (0 : Fin 3))
  have horthY :
      @inner ℝ V _ (t.points i -ᵥ t.altitudeFoot (i + 1))
        (t.points (i + 1) -ᵥ t.altitudeFoot (i + 1)) = 0 := by
    apply t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero
    fin_cases i <;> decide
  have hp : Sbtw ℝ (t.points (i + 2))
      (t.altitudeFoot (i + 1)) (t.points i) :=
    result_sbtw_from_projection
      (result_altitudeFoot_mem_pair t i) hAX hYX hXY hAY
      hinner1 hinner2 horthX horthY
  exact result_base_immediate_halves t i (t.altitudeFoot (i + 1)) hp horthX

private lemma parametric_successor_pi_rank_identity (n : ℕ) :
    Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) =
      (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn0]
  norm_num [Nat.cast_add]

private lemma result_targeted_true_winsNow {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]
    (t : Triangle ℝ P) (i : Fin 3) (r b θ : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hangle : ∠ (t.points (i + 1))
        ((AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2))) r)
        (t.points i) = b + θ) :
    ∃ m : Move t, WinsNow (m.half True) (b + θ) := by
  obtain ⟨m, him, hpm, hmangle⟩ :=
    candidate_targeted_move_transport t i r b θ hr0 hr1 hangle
  refine ⟨m, ?_⟩
  refine ⟨1, ?_⟩
  simpa [WinsNow, Move.half, him, hpm] using hmangle

private lemma parametric_rank_remainder
    (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n + 1) (a b : ℝ)
    (hsum : a + b + (k : ℝ) *
        (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi) :
    a + b = ((n + 1 - k : ℕ) : ℝ) *
      (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hπ : Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) =
      (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) :=
    successor_pi_rank_identity n hn
  have hkcast : ((n + 1 - k : ℕ) : ℝ) =
      (n : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_add]
    norm_num
  rw [hkcast]
  linarith [hπ, hsum]

private lemma result_successor_rank
    (n : ℕ) (hn : 2 ≤ n) :
    Real.pi - (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) =
      Real.pi / ((n + 1 : ℕ) : ℝ) := by
  have h := parametric_rank_remainder n n hn (by omega) (0 : ℝ)
    (Real.pi - (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ))) (by ring)
  convert h using 1 <;> norm_num

private lemma result_successor_true_target {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)]
    (t : Triangle ℝ P) (i : Fin 3) (r : ℝ) (n : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hangle : ∠ (t.points (i + 1))
        ((AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2))) r)
        (t.points i) = 0 + Real.pi / ((n + 1 : ℕ) : ℝ)) :
    ∃ m : Move t, WinsNow (m.half True) (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨m, hm⟩ := result_targeted_true_winsNow t i r 0
    (Real.pi / ((n + 1 : ℕ) : ℝ)) hr0 hr1 hangle
  refine ⟨m, ?_⟩
  simpa using hm

private lemma result_unit_transfer_false_target {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [Fact (finrank ℝ V = 2)] (t : Triangle ℝ P) (m : Move t)
    (a b c θ : ℝ)
    (ha : ∠ (t.points m.i) (t.points (m.i + 1))
        (t.points (m.i + 2)) = a)
    (hb : ∠ (t.points m.i) (t.points (m.i + 2))
        (t.points (m.i + 1)) = b)
    (hp : ∠ (t.points (m.i + 1)) m.p (t.points m.i) = b + θ)
    (hsum : a + b + c = Real.pi) :
    WinsNow (m.half False) θ := by
  obtain ⟨_, _, _, hfalse0, hfalse1, hfalse2⟩ :=
    candidate_unit_transfer_branch_angles t m a b c θ ha hb hp hsum
  refine ⟨2, ?_⟩
  simpa [WinsNow] using hfalse2

private lemma parametric_pi_div_succ_gap (n : ℕ) (hn : 2 ≤ n) :
    Real.pi / (n : ℝ) - Real.pi / ((n + 1 : ℕ) : ℝ) =
      Real.pi / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))
  have hn10 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  field_simp [hn0, hn10]
  norm_num [Nat.cast_add]

private lemma parametric_rank_defect (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) -
        ((n - 1 : ℕ) : ℝ) * (Real.pi / (n : ℝ)) =
      Real.pi / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hn))
  have hn10 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hn1 : 1 ≤ n := by omega
  field_simp [hn0, hn10]
  norm_num [Nat.cast_add, Nat.cast_sub hn1]
  ring

private lemma researched_parametric_rank_remainder
    (n k : ℕ) (hk : k ≤ n + 1) (a b : ℝ)
    (hsum : a + b + (k : ℝ) *
        (Real.pi / ((n + 1 : ℕ) : ℝ)) = Real.pi) :
    a + b = ((n + 1 - k : ℕ) : ℝ) *
      (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hπ : Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) =
      (n : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) :=
    parametric_successor_pi_rank_identity n
  have hkcast : ((n + 1 - k : ℕ) : ℝ) =
      (n : ℝ) + 1 - (k : ℝ) := by
    rw [Nat.cast_sub hk, Nat.cast_add]
    norm_num
  rw [hkcast]
  linarith [hπ, hsum]

private lemma winning_after_one_move_true
    (θ : ℝ)
    (M : ∀ t : Triangle ℝ P, Move t)
    (sT : Strategy P) (hT : sT.Winning θ)
    (hTbranch : ∀ t : Triangle ℝ P, WinsNow ((M t).half True) θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let lift : Strategy P := fun {k} h =>
    match k with
    | 0 => by simpa using M (h (Fin.last 0))
    | k + 1 =>
        let htail : Fin (k + 1) → Triangle ℝ P := fun j => h j.succ
        have he : htail (Fin.last k) = h (Fin.last (k + 1)) := by
          apply congrArg h
          apply Fin.ext
          simp
        let q := sT (k := k) htail
        ⟨q.i, q.p, by
          rw [← he]
          exact q.sbtw_p⟩
  refine ⟨lift, ?_⟩
  intro t₀ c
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable _
  by_cases hc : c 0
  · refine ⟨1, ?_⟩
    have hm := hTbranch t₀
    have hlast := play_last_succ lift t₀ c 0
    rw [hlast]
    simpa [lift, Strategy.play, hc] using hm
  · let child := (M t₀).half False
    let d : ℕ → Prop := fun j => c (j + 1)
    letI : ∀ k, Decidable (d k) := fun k => Classical.propDecidable _
    obtain ⟨k, hk⟩ := hT child d
    refine ⟨k + 1, ?_⟩
    have htail : ∀ n : ℕ, ∀ i : Fin (n + 1),
        lift.play t₀ c (n + 2) i.succ = sT.play child d (n + 1) i := by
      intro n
      induction n with
      | zero =>
          intro i
          fin_cases i
          simp [lift, child, Strategy.play, hc]
      | succ n ih =>
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · let h : Fin (n + 2) → Triangle ℝ P :=
                Fin.snoc (lift.play t₀ c (n + 1))
                  ((lift (lift.play t₀ c (n + 1))).half (c n))
            have hfun : (fun j : Fin (n + 1) => h j.succ) =
                sT.play child d (n + 1) := by
              funext j
              dsimp [h]
              exact ih j
            have hidx : (Fin.last n).succ = Fin.last (n + 1) := by
              apply Fin.ext
              simp
            have htri : h (Fin.last (n + 1)) =
                sT.play child d (n + 1) (Fin.last n) := by
              rw [← hidx]
              exact congrFun hfun (Fin.last n)
            have hpts : (h (Fin.last (n + 1))).points =
                (sT.play child d (n + 1) (Fin.last n)).points :=
              congrArg (fun t : Triangle ℝ P => t.points) htri
            have hi := congrArg (fun x : Fin (n + 1) → Triangle ℝ P =>
              (sT x).i) hfun
            have hp := congrArg (fun x : Fin (n + 1) → Triangle ℝ P =>
              (sT x).p) hfun
            have hi' : (lift h).i = (sT (sT.play child d (n + 1))).i := by
              simpa only [lift] using hi
            have hp' : (lift h).p = (sT (sT.play child d (n + 1))).p := by
              simpa only [lift] using hp
            have hhalf : (lift h).half (c (n + 1)) =
                (sT (sT.play child d (n + 1))).half (c (n + 1)) := by
              obtain ⟨l0, l1, l2⟩ :=
                move_half_points (h (Fin.last (n + 1))) (lift h) (c (n + 1))
              obtain ⟨r0, r1, r2⟩ :=
                move_half_points (sT.play child d (n + 1) (Fin.last n))
                  (sT (sT.play child d (n + 1))) (c (n + 1))
              have e0mid : (h (Fin.last (n + 1))).points (lift h).i =
                  (sT.play child d (n + 1) (Fin.last n)).points
                    (sT (sT.play child d (n + 1))).i := by
                rw [hpts, hi']
              have e1mid :
                  (if c (n + 1) then
                    (h (Fin.last (n + 1))).points ((lift h).i + 1)
                   else (h (Fin.last (n + 1))).points ((lift h).i + 2)) =
                    (if c (n + 1) then
                      (sT.play child d (n + 1) (Fin.last n)).points
                        ((sT (sT.play child d (n + 1))).i + 1)
                     else (sT.play child d (n + 1) (Fin.last n)).points
                        ((sT (sT.play child d (n + 1))).i + 2)) := by
                rw [hpts, hi']
              have e2mid : (lift h).p =
                  (sT (sT.play child d (n + 1))).p := hp'
              have e0 : ((lift h).half (c (n + 1))).points 0 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 0 :=
                l0.trans (e0mid.trans r0.symm)
              have e1 : ((lift h).half (c (n + 1))).points 1 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 1 :=
                l1.trans (e1mid.trans r1.symm)
              have e2 : ((lift h).half (c (n + 1))).points 2 =
                    ((sT (sT.play child d (n + 1))).half (c (n + 1))).points 2 :=
                l2.trans (e2mid.trans r2.symm)
              ext z
              fin_cases z
              · simpa using e0
              · simpa using e1
              · simpa using e2
            simp [Strategy.play]
            simpa [h] using hhalf
          · rw [show lift.play t₀ c (n + 1 + 2) =
                Fin.snoc (lift.play t₀ c (n + 1 + 1))
                  ((lift (lift.play t₀ c (n + 1 + 1))).half (c (n + 1))) from rfl]
            rw [show sT.play child d (n + 1 + 1) =
                Fin.snoc (sT.play child d (n + 1))
                  ((sT (sT.play child d (n + 1))).half (d n)) from rfl]
            have hidx : j.castSucc.succ = (j.succ).castSucc := by rfl
            rw [hidx]
            rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
            simpa [Nat.add_assoc] using ih j
    rw [show lift.play t₀ c (k + 1 + 1) (Fin.last (k + 1)) =
        sT.play child d (k + 1) (Fin.last k) from by
          simpa [Nat.add_assoc] using htail k (Fin.last k)]
    exact hk

private lemma general_nat_rank_remainder
    (N k : ℕ) (hk : k ≤ N) (a b x : ℝ)
    (hsum : a + b + (k : ℝ) * x = (N : ℝ) * x) :
    a + b = ((N - k : ℕ) : ℝ) * x := by
  have hkcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hk]
  rw [hkcast]
  linarith [hsum]

private lemma immediate_strategy_of_two_branch {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] [Fact (finrank ℝ V = 2)] :
    ∀ θ : ℝ, (∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ) →
      ∃ s : Strategy P, s.Winning θ := by
  intro θ h
  exact winning_of_immediate_strategy_pre θ h

private lemma pi_div_nat_remainder_research
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) (a b : ℝ)
    (hsum : a + b + (k : ℝ) * (Real.pi / (N : ℝ)) = Real.pi) :
    a + b = ((N - k : ℕ) : ℝ) * (Real.pi / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hπ : (N : ℝ) * (Real.pi / (N : ℝ)) = Real.pi := by
    field_simp [hN0]
  have hkcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hk]
  rw [hkcast]
  linarith [hsum, hπ]

private lemma pi_div_succ_gap_pos_research
    (N : ℕ) (hN : 0 < N) :
    Real.pi / (N : ℝ) - Real.pi / ((N + 1 : ℕ) : ℝ) =
      Real.pi / ((N : ℝ) * ((N + 1 : ℕ) : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hN10 : ((N + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero N)
  field_simp [hN0, hN10]
  norm_num [Nat.cast_add]

private lemma pi_div_succ_ne_research
    (N : ℕ) (hN : 0 < N) :
    Real.pi / (N : ℝ) ≠ Real.pi / ((N + 1 : ℕ) : ℝ) := by
  intro heq
  have hgap := pi_div_succ_gap_pos_research N hN
  have hpos : 0 < Real.pi / ((N : ℝ) * ((N + 1 : ℕ) : ℝ)) := by
    positivity
  linarith [hgap]

private lemma pi_nat_remainder_identity_research
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    ((N - k : ℕ) : ℝ) * (Real.pi / (N : ℝ)) =
      Real.pi - (k : ℝ) * (Real.pi / (N : ℝ)) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hkcast : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hk]
  rw [hkcast]
  field_simp [hN0]

private lemma exists_strategy_of_uniform_true_move
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (finrank ℝ V = 2)]
    (θ : ℝ)
    (Mspec : ∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) θ)
    (sT : Strategy P) (hT : sT.Winning θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let M : ∀ t : Triangle ℝ P, Move t := fun t => Classical.choose (Mspec t)
  have hM : ∀ t : Triangle ℝ P, WinsNow ((M t).half True) θ := by
    intro t
    exact Classical.choose_spec (Mspec t)
  exact winning_after_one_move_true θ M sT hT hM

private lemma uniform_true_branch_of_targeted_geometry
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (finrank ℝ V = 2)]
    (θ : ℝ)
    (hgeom : ∀ t : Triangle ℝ P, ∃ i : Fin 3, ∃ r : ℝ,
      0 < r ∧ r < 1 ∧
      ∠ (t.points (i + 1))
          (AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) r)
          (t.points i) = 0 + θ) :
    ∀ t : Triangle ℝ P, ∃ m : Move t, WinsNow (m.half True) θ := by
  intro t
  obtain ⟨i, r, hr0, hr1, hangle⟩ := hgeom t
  simpa only [zero_add] using
    (result_targeted_true_winsNow t i r 0 θ hr0 hr1 hangle)

private lemma strategy_winning_congr
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (finrank ℝ V = 2)]
    (s : Strategy P) {θ θ' : ℝ} (hθ : θ = θ')
    (hs : s.Winning θ) : s.Winning θ' := by
  subst θ'
  exact hs

theorem result : {θ : ℝ | 0 < θ ∧ θ < π ∧ ∃ s : Strategy P, s.Winning θ} = answer := by
  classical
  obtain ⟨t₀, heq⟩ :=
    equilateral_triangle_exists_for_result (V := V) (P := P)
  apply result_of_game_characterization
  · intro θ hθ
    have hforward : θ ∈ answer := result_forward_from_cyclic_angles t₀ heq θ hθ
    simpa [answer] using hforward
  · intro n hn
    have hrank : Real.pi - Real.pi / (n : ℝ) =
        ((n - 1 : ℕ) : ℝ) * (Real.pi / (n : ℝ)) :=
      parametric_pi_sub_div_nat n (by omega)
    have hbase : ∃ s : Strategy P, s.Winning (Real.pi / (2 : ℝ)) :=
      result_base_strategy (V := V) (P := P)
    exact hreverse_of_explicit_successor_check (hbase := hbase) (hstep := by
      intro n hn h
      obtain ⟨s, hs⟩ := h
      refine ⟨s, ?_⟩
      simpa only [Strategy.Winning] using hs) n hn

private lemma winning_of_immediate_strategy (θ : ℝ)
    (h : ∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (h (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  letI : ∀ k, Decidable (c k) := fun k => Classical.propDecidable _
  by_cases hc : c 0
  · refine ⟨1, ?_⟩
    have hm := Classical.choose_spec (h ((s.play t₀ c) (0 + 1) (Fin.last 0)))
    have hlast := play_last_succ s t₀ c 0
    rw [hlast]
    simpa [s, hc] using hm.1
  · refine ⟨1, ?_⟩
    have hm := Classical.choose_spec (h ((s.play t₀ c) (0 + 1) (Fin.last 0)))
    have hlast := play_last_succ s t₀ c 0
    rw [hlast]
    simpa [s, hc] using hm.2

end IMO2026P4
