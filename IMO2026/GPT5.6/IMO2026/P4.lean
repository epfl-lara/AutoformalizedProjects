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
def answer : Set ℝ := {θ | ∃ n : ℕ, 2 ≤ n ∧ θ = π / (n : ℝ)}
/-- A one-step geometric forcing move suffices to construct a winning strategy for the right angle. -/
theorem winning_of_one_step
    (h : ∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2)) :
    ∃ s : Strategy P, s.Winning (π / 2) := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (h (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  refine ⟨1, ?_⟩
  simp only [Strategy.play, Fin.snoc_last]
  dsimp only [s]
  by_cases hc : c 0
  · simpa [Move.half, hc] using (Classical.choose_spec (h t₀)).1
  · simpa [Move.half, hc] using (Classical.choose_spec (h t₀)).2

omit [Fact (finrank ℝ V = 2)] in
/-- An altitude foot forms a right angle with every other vertex. -/
private theorem angle_altitudeFoot_eq_pi_div_two (t : Triangle ℝ P) (i j : Fin 3)
    (hji : j ≠ i) :
    ∠ (t.points j) (t.altitudeFoot i) (t.points i) = π / 2 := by
  rw [Affine.Simplex.altitudeFoot]
  apply EuclideanGeometry.angle_orthogonalProjection_self
  rw [t.range_faceOpposite_points]
  exact mem_affineSpan ℝ ⟨j, by simp [hji], rfl⟩

/-- A legal altitude-foot move makes both resulting triangles contain a right angle. -/
private theorem altitudeMove_halves_win (t : Triangle ℝ P) (i : Fin 3)
    (hs : Sbtw ℝ (t.points (i + 1)) (t.altitudeFoot i) (t.points (i + 2))) :
    let m : Move t := ⟨i, t.altitudeFoot i, hs⟩
    WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2) := by
  let m : Move t := ⟨i, t.altitudeFoot i, hs⟩
  change WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2)
  constructor
  · refine ⟨1, ?_⟩
    simpa [Move.half, m] using
      angle_altitudeFoot_eq_pi_div_two t i (i + 1) (by fin_cases i <;> decide)
  · refine ⟨1, ?_⟩
    simpa [Move.half, m] using
      angle_altitudeFoot_eq_pi_div_two t i (i + 2) (by fin_cases i <;> decide)

/-- The right-angle strategy follows once every triangle supplies an interior altitude foot. -/
private theorem right_angle_winning_of_interior_altitude
    (h : ∀ t : Triangle ℝ P, ∃ i : Fin 3,
      Sbtw ℝ (t.points (i + 1)) (t.altitudeFoot i) (t.points (i + 2))) :
    ∃ s : Strategy P, s.Winning (π / 2) := by
  apply winning_of_one_step
  intro t
  obtain ⟨i, hi⟩ := h t
  let m : Move t := ⟨i, t.altitudeFoot i, hi⟩
  exact ⟨m, altitudeMove_halves_win t i hi⟩

/-- A cevian can realize any strictly intermediate angle at a triangle vertex. -/
private theorem exists_cevian_with_angle (t : Triangle ℝ P) (i : Fin 3) (x : ℝ)
    (hx0 : 0 < x)
    (hxA : x < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2))) :
    ∃ p, Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2)) ∧
      ∠ (t.points (i + 1)) (t.points i) p = x := by
  let A := t.points i
  let B := t.points (i + 1)
  let C := t.points (i + 2)
  let f : ℝ → ℝ := fun r => ∠ B A ((AffineMap.lineMap B C) r)
  have hBA : B ≠ A := t.independent.injective.ne (by fin_cases i <;> decide)
  have hBC : B ≠ C := t.independent.injective.ne (by fin_cases i <;> decide)
  have hB : B ∈ affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
    rw [t.range_faceOpposite_points]
    exact mem_affineSpan ℝ ⟨i + 1, by fin_cases i <;> simp, rfl⟩
  have hC : C ∈ affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
    rw [t.range_faceOpposite_points]
    exact mem_affineSpan ℝ ⟨i + 2, by fin_cases i <;> simp, rfl⟩
  have hpA (r : ℝ) : (AffineMap.lineMap B C) r ≠ A := by
    intro hr
    apply t.points_notMem_affineSpan_faceOpposite i
    change A ∈ affineSpan ℝ (Set.range (t.faceOpposite i).points)
    rw [← hr]
    exact AffineMap.lineMap_mem r hB hC
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro r
    have htrip : ContinuousAt (fun r : ℝ => (B, A, (AffineMap.lineMap B C) r)) r :=
      continuousAt_const.prodMk
        (continuousAt_const.prodMk (continuousAt_const.lineMap continuousAt_const continuousAt_id))
    change ContinuousAt ((fun y : P × P × P => ∠ y.1 y.2.1 y.2.2) ∘
      fun r : ℝ => (B, A, (AffineMap.lineMap B C) r)) r
    exact (EuclideanGeometry.continuousAt_angle hBA (hpA r)).comp htrip
  have hf0 : f 0 = 0 := by
    simp [f, EuclideanGeometry.angle_self_of_ne hBA]
  have hf1 : f 1 = ∠ B A C := by simp [f]
  have hxI : x ∈ Set.Icc (f 0) (f 1) := by
    rw [hf0, hf1]
    exact ⟨hx0.le, hxA.le⟩
  obtain ⟨r, hrI, hrx⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 1) (by norm_num)
    hf.continuousOn hxI
  have hr0 : 0 < r := by
    apply lt_of_le_of_ne hrI.1
    intro h0r
    have hre : r = 0 := h0r.symm
    subst r
    rw [hf0] at hrx
    linarith
  have hr1 : r < 1 := by
    apply lt_of_le_of_ne hrI.2
    intro hre
    subst r
    rw [hf1] at hrx
    linarith
  refine ⟨(AffineMap.lineMap B C) r, ?_, hrx⟩
  exact sbtw_lineMap_iff.mpr ⟨hBC, hr0, hr1⟩

omit [Fact (finrank ℝ V = 2)] in
/-- The angle at the cut point in the opposite child is the adjacent original angle
plus the angle cut off at the chosen vertex. -/
private theorem cevian_opposite_child_angle (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2))) :
    ∠ (t.points i) p (t.points (i + 2)) =
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) +
        ∠ (t.points (i + 1)) (t.points i) p := by
  let A := t.points i
  let B := t.points (i + 1)
  let C := t.points (i + 2)
  have hBA : B ≠ A := t.independent.injective.ne (by fin_cases i <;> decide)
  have hBpC : ∠ A B p = ∠ A B C :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := A) (p₂ := B) p hBA
  have hsupp := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  rw [EuclideanGeometry.angle_comm p A B] at htri
  rw [EuclideanGeometry.angle_comm A p B] at hsupp
  change ∠ A p C = ∠ A B C + ∠ B A p
  change ∠ B p A + ∠ A p C = π at hsupp
  linarith

open scoped Classical in
omit [Fact (finrank ℝ V = 2)] in
/-- A bounded two-move construction suffices for a winning strategy. -/
private theorem winning_of_at_most_two_moves (θ : ℝ) (s : Strategy P)
    (h : ∀ (t₀ : Triangle ℝ P) (c : ℕ → Prop),
      WinsNow ((s.play t₀ c) 1 (Fin.last 0)) θ ∨
      WinsNow ((s.play t₀ c) 2 (Fin.last 1)) θ ∨
      WinsNow ((s.play t₀ c) 3 (Fin.last 2)) θ) :
    s.Winning θ := by
  intro t₀ c
  rcases h t₀ c with h0 | h1 | h2
  · exact ⟨0, h0⟩
  · exact ⟨1, h1⟩
  · exact ⟨2, h2⟩

theorem winning_of_one_step_parametric (θ : ℝ)
    (h : ∀ t : Triangle ℝ P, ∃ m : Move t,
      WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (h (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  refine ⟨1, ?_⟩
  simp only [Strategy.play, Fin.snoc_last]
  dsimp only [s]
  by_cases hc : c 0
  · simpa [Move.half, hc] using (Classical.choose_spec (h t₀)).1
  · simpa [Move.half, hc] using (Classical.choose_spec (h t₀)).2

private theorem cevian_move_parametric_outcomes (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2))) (x : ℝ)
    (hx : ∠ (t.points (i + 1)) (t.points i) p = x) :
    let m : Move t := ⟨i, p, hp⟩
    WinsNow (m.half True) x ∧
      WinsNow (m.half False)
        (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) + x) := by
  let m : Move t := ⟨i, p, hp⟩
  change WinsNow (m.half True) x ∧
    WinsNow (m.half False)
      (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) + x)
  have hx' : ∠ p (t.points i) (t.points (i + 1)) = x := by
    rw [EuclideanGeometry.angle_comm]
    exact hx
  constructor
  · refine ⟨2, ?_⟩
    simpa [Move.half, m] using hx'
  · refine ⟨1, ?_⟩
    simpa [Move.half, m, EuclideanGeometry.angle_comm, hx'] using
      (cevian_opposite_child_angle t i p hp)

private theorem cevian_halves_win_of_equal_split (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2))) (θ : ℝ)
    (hleft : ∠ (t.points (i + 1)) (t.points i) p = θ)
    (hright : ∠ p (t.points i) (t.points (i + 2)) = θ) :
    let m : Move t := ⟨i, p, hp⟩
    WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ := by
  let m : Move t := ⟨i, p, hp⟩
  change WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ
  constructor
  · refine ⟨2, ?_⟩
    simpa [Move.half, m, EuclideanGeometry.angle_comm] using hleft
  · refine ⟨2, ?_⟩
    simpa [Move.half, m] using hright

private theorem exists_forcing_move_of_double_angle (t : Triangle ℝ P) (i : Fin 3) (θ : ℝ)
    (hθ : 0 < θ)
    (hA : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) = 2 * θ) :
    ∃ m : Move t, WinsNow (m.half True) θ ∧ WinsNow (m.half False) θ := by
  have hθA : θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) := by
    rw [hA]
    linarith
  obtain ⟨p, hp, hleft⟩ := exists_cevian_with_angle t i θ hθ hθA
  have hsum :
      ∠ (t.points (i + 1)) (t.points i) p +
        ∠ p (t.points i) (t.points (i + 2)) =
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hp
  have hright : ∠ p (t.points i) (t.points (i + 2)) = θ := by
    rw [hleft, hA] at hsum
    linarith
  let m : Move t := ⟨i, p, hp⟩
  exact ⟨m, cevian_halves_win_of_equal_split t i p hp θ hleft hright⟩

theorem setOf_eq_singleton_iff {α : Type*} (p : α → Prop) (a : α) :
    {x | p x} = ({a} : Set α) ↔ p a ∧ ∀ x, p x → x = a := by
  constructor
  · intro h
    have ha : a ∈ {x | p x} := by rw [h]; simp
    refine ⟨ha, ?_⟩
    intro x hx
    have : x ∈ ({a} : Set α) := by rw [← h]; exact hx
    simpa using this
  · rintro ⟨ha, hu⟩
    ext x
    constructor
    · intro hx
      simpa [hu x hx]
    · intro hx
      have hxa : x = a := by simpa using hx
      simpa [hxa] using ha

theorem exists_eventually_of_natRank_descent {α : Type*} (W : α → Prop)
    (rank : α → ℕ) (T : ℕ → α)
    (hstep : ∀ k, W (T k) ∨ W (T (k + 1)) ∨ rank (T (k + 1)) < rank (T k)) :
    ∃ k, W (T k) := by
  have aux : ∀ r : ℕ, ∀ U : ℕ → α, rank (U 0) < r →
      (∀ k, W (U k) ∨ W (U (k + 1)) ∨ rank (U (k + 1)) < rank (U k)) →
      ∃ k, W (U k) := by
    intro r
    induction r with
    | zero =>
        intro U hr
        omega
    | succ r ih =>
        intro U hr hs
        rcases hs 0 with h0 | h1 | hlt
        · exact ⟨0, h0⟩
        · exact ⟨1, by simpa using h1⟩
        · simp only [Nat.zero_add] at hlt
          have hr' : rank (U 1) < r := by omega
          obtain ⟨k, hk⟩ := ih (fun j => U (j + 1)) (by simpa using hr') (by
            intro j
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs (j + 1))
          exact ⟨k + 1, hk⟩
  exact aux (rank (T 0) + 1) T (by omega) hstep

theorem play_last_succ_identity (s : Strategy P) (t₀ : Triangle ℝ P)
    (c : ℕ → Prop) [∀ k, Decidable (c k)] (k : ℕ) :
    (s.play t₀ c (k + 2)) (Fin.last (k + 1)) =
      (s (s.play t₀ c (k + 1))).half (c k) := by
  simp [Strategy.play]

/-- A local move which wins immediately or strictly decreases a natural rank
on either reply yields a winning strategy. -/
theorem winning_of_natRank_descent (θ : ℝ) (rank : Triangle ℝ P → ℕ)
    (hstep : ∀ t : Triangle ℝ P, ∃ m : Move t,
      (WinsNow t θ ∨ WinsNow (m.half True) θ ∨ rank (m.half True) < rank t) ∧
      (WinsNow t θ ∨ WinsNow (m.half False) θ ∨ rank (m.half False) < rank t)) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (hstep (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  let T : ℕ → Triangle ℝ P := fun k => (s.play t₀ c (k + 1)) (Fin.last k)
  apply exists_eventually_of_natRank_descent (fun t => WinsNow t θ) rank T
  intro k
  by_cases hc : c k
  · simpa only [T, play_last_succ_identity, s, Move.half, hc] using
      (Classical.choose_spec (hstep (T k))).1
  · simpa only [T, play_last_succ_identity, s, Move.half, hc] using
      (Classical.choose_spec (hstep (T k))).2

/-- Cutting off `θ` realizes one step of an arbitrary affine angle progression
in the opposite child. -/
private theorem exists_forcing_move_with_parametric_increment
    (t : Triangle ℝ P) (i : Fin 3) (θ β : ℝ) (k : ℕ) (hθ : 0 < θ)
    (hθA : θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)))
    (hB : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) =
      β + (k : ℝ) * θ) :
    ∃ m : Move t,
      WinsNow (m.half True) θ ∧
      WinsNow (m.half False) (β + ((k + 1 : ℕ) : ℝ) * θ) := by
  obtain ⟨p, hp, hx⟩ := exists_cevian_with_angle t i θ hθ hθA
  let m : Move t := ⟨i, p, hp⟩
  refine ⟨m, (cevian_move_parametric_outcomes t i p hp θ hx).1, ?_⟩
  convert (cevian_move_parametric_outcomes t i p hp θ hx).2 using 1
  rw [hB]
  push_cast
  ring

private theorem exists_forcing_move_of_smaller_angle
    (t : Triangle ℝ P) (i : Fin 3) (θ : ℝ) (hθ : 0 < θ)
    (hθA : θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2))) :
    ∃ m : Move t,
      WinsNow (m.half True) θ ∧
      WinsNow (m.half False)
        (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) + θ) := by
  obtain ⟨p, hp, hx⟩ := exists_cevian_with_angle t i θ hθ hθA
  let m : Move t := ⟨i, p, hp⟩
  exact ⟨m, cevian_move_parametric_outcomes t i p hp θ hx⟩

theorem cut_hits_addSubgroup
    {G : Type*} [AddCommGroup G] (S : AddSubgroup G)
    {α β γ δ ε φ ψ p : G}
    (hα : α = δ + ε) (hp : p = φ + ψ)
    (hleft : δ + β + φ = p) (hright : ε + γ + ψ = p)
    (h₁ : δ ∈ S ∨ β ∈ S ∨ φ ∈ S)
    (h₂ : ε ∈ S ∨ γ ∈ S ∨ ψ ∈ S) :
    α ∈ S ∨ β ∈ S ∨ γ ∈ S ∨ p ∈ S := by
  rcases h₁ with hδ | hβ | hφ
  · rcases h₂ with hε | hγ | hψ
    · exact Or.inl (hα ▸ S.add_mem hδ hε)
    · exact Or.inr (Or.inr (Or.inl hγ))
    · right; left
      have hb : β = ψ - δ := by
        calc
          β = (δ + β + φ) - φ - δ := by abel
          _ = p - φ - δ := by rw [hleft]
          _ = (φ + ψ) - φ - δ := by rw [hp]
          _ = ψ - δ := by abel
      rw [hb]
      exact S.sub_mem hψ hδ
  · exact Or.inr (Or.inl hβ)
  · rcases h₂ with hε | hγ | hψ
    · right; right; left
      have hg : γ = φ - ε := by
        calc
          γ = (ε + γ + ψ) - ψ - ε := by abel
          _ = p - ψ - ε := by rw [hright]
          _ = (φ + ψ) - ψ - ε := by rw [hp]
          _ = φ - ε := by abel
      rw [hg]
      exact S.sub_mem hφ hε
    · exact Or.inr (Or.inr (Or.inl hγ))
    · exact Or.inr (Or.inr (Or.inr (hp ▸ S.add_mem hφ hψ)))

private theorem move_half_points_parametric {t : Triangle ℝ P} (m : Move t)
    (c : Prop) [Decidable c] :
    (m.half c).points = ![t.points m.i,
      if c then t.points (m.i + 1) else t.points (m.i + 2), m.p] := by
  by_cases hc : c <;> simp [Move.half, hc]

private theorem altitude_move_wins_parametric (t : Triangle ℝ P) (i : Fin 3)
    (hi : Sbtw ℝ (t.points (i + 1)) (t.altitudeFoot i) (t.points (i + 2))) :
    let m : Move t := ⟨i, t.altitudeFoot i, hi⟩
    WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2) := by
  let m : Move t := ⟨i, t.altitudeFoot i, hi⟩
  change WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2)
  constructor
  · refine ⟨1, ?_⟩
    simpa [m, Move.half] using
      (angle_altitudeFoot_eq_pi_div_two t i (i + 1) (by omega))
  · refine ⟨1, ?_⟩
    simpa [m, Move.half] using
      (angle_altitudeFoot_eq_pi_div_two t i (i + 2) (by omega))

private theorem play_last_succ (s : Strategy P) (t₀ : Triangle ℝ P)
    (c : ℕ → Prop) [∀ j, Decidable (c j)] (k : ℕ) :
    (s.play t₀ c (k + 2)) (Fin.last (k + 1)) =
      (s (s.play t₀ c (k + 1))).half (c k) := by
  simp [Strategy.play]

private theorem cut_avoids_addSubgroup_branch
    {G : Type*} [AddCommGroup G] (S : AddSubgroup G)
    {α β γ δ ε φ ψ p : G}
    (hα : α = δ + ε) (hp : p = φ + ψ)
    (hleft : δ + β + φ = p) (hright : ε + γ + ψ = p)
    (havoid : α ∉ S ∧ β ∉ S ∧ γ ∉ S ∧ p ∉ S) :
    (δ ∉ S ∧ β ∉ S ∧ φ ∉ S) ∨
      (ε ∉ S ∧ γ ∉ S ∧ ψ ∉ S) := by
  classical
  by_cases h₁ : δ ∈ S ∨ β ∈ S ∨ φ ∈ S
  · right
    have h₂ : ¬(ε ∈ S ∨ γ ∈ S ∨ ψ ∈ S) := by
      intro h₂
      rcases cut_hits_addSubgroup S hα hp hleft hright h₁ h₂ with hαS | hβS | hγS | hpS
      · exact havoid.1 hαS
      · exact havoid.2.1 hβS
      · exact havoid.2.2.1 hγS
      · exact havoid.2.2.2 hpS
    push_neg at h₂
    exact h₂
  · left
    push_neg at h₁
    exact ⟨h₁.1, h₁.2.1, h₁.2.2⟩

private lemma lt_int_ceil_of_not_int {x : ℝ}
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    x < ((⌈x⌉ : ℤ) : ℝ) := by
  refine lt_of_le_of_ne (Int.le_ceil x) ?_
  intro h
  exact hx ⟨⌈x⌉, h.symm⟩

private lemma normalized_integer_crossing
    {A B C : ℝ} {n : ℕ}
    (hn : 3 ≤ n)
    (_hpos : 0 < A ∧ 0 < B ∧ 0 < C)
    (hsum : A + B + C = (n : ℝ))
    (hnint : ∀ x ∈ ({A, B, C} : Set ℝ),
      x ∉ Set.range ((↑) : ℤ → ℝ)) :
    (∃ k : ℤ, B < (k : ℝ) ∧ (k : ℝ) < A + B) ∨
    (∃ k : ℤ, C < (k : ℝ) ∧ (k : ℝ) < B + C) ∨
    (∃ k : ℤ, A < (k : ℝ) ∧ (k : ℝ) < C + A) := by
  have hAn : A ∉ Set.range ((↑) : ℤ → ℝ) := hnint A (by simp)
  have hBn : B ∉ Set.range ((↑) : ℤ → ℝ) := hnint B (by simp)
  have hCn : C ∉ Set.range ((↑) : ℤ → ℝ) := hnint C (by simp)
  have hAceil := lt_int_ceil_of_not_int hAn
  have hBceil := lt_int_ceil_of_not_int hBn
  have hCceil := lt_int_ceil_of_not_int hCn
  have hAupper : ((⌈A⌉ : ℤ) : ℝ) < A + 1 := by
    exact_mod_cast Int.ceil_lt_add_one A
  have hBupper : ((⌈B⌉ : ℤ) : ℝ) < B + 1 := by
    exact_mod_cast Int.ceil_lt_add_one B
  have hCupper : ((⌈C⌉ : ℤ) : ℝ) < C + 1 := by
    exact_mod_cast Int.ceil_lt_add_one C
  by_contra h
  push_neg at h
  have hAB : A + B ≤ ((⌈B⌉ : ℤ) : ℝ) := by
    have := h.1 ⌈B⌉ hBceil
    linarith
  have hBC : B + C ≤ ((⌈C⌉ : ℤ) : ℝ) := by
    have := h.2.1 ⌈C⌉ hCceil
    linarith
  have hCA : C + A ≤ ((⌈A⌉ : ℤ) : ℝ) := by
    have := h.2.2 ⌈A⌉ hAceil
    linarith
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

private theorem cevian_cut_preserves_angle_avoidance
    (S : AddSubgroup ℝ) (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2)))
    (havoid :
      ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) ∉ S ∧
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ∉ S ∧
      ∠ (t.points i) (t.points (i + 2)) (t.points (i + 1)) ∉ S ∧
      π ∉ S) :
    (∠ (t.points (i + 1)) (t.points i) p ∉ S ∧
      ∠ (t.points i) (t.points (i + 1)) p ∉ S ∧
      ∠ (t.points i) p (t.points (i + 1)) ∉ S) ∨
    (∠ p (t.points i) (t.points (i + 2)) ∉ S ∧
      ∠ (t.points i) (t.points (i + 2)) p ∉ S ∧
      ∠ (t.points i) p (t.points (i + 2)) ∉ S) := by
  let A := t.points i
  let B := t.points (i + 1)
  let C := t.points (i + 2)
  have hBA : B ≠ A := t.independent.injective.ne (by fin_cases i <;> decide)
  have hCA : C ≠ A := t.independent.injective.ne (by fin_cases i <;> decide)
  have hα : ∠ B A C = ∠ B A p + ∠ p A C :=
    (EuclideanGeometry.angle_add_angle_eq_of_sbtw hp).symm
  have hβ : ∠ A B p = ∠ A B C :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  have hγ : ∠ A C p = ∠ A C B :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.symm.angle₁₂₃_eq_pi
  have hpi : π = ∠ A p B + ∠ A p C := by
    have hs := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
    simpa [B, C] using hs.symm
  have hleft : ∠ B A p + ∠ A B p + ∠ A p B = π := by
    have ht := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := A) (p₂ := B) p hBA
    rw [EuclideanGeometry.angle_comm p A B,
      EuclideanGeometry.angle_comm B p A] at ht
    linarith
  have hright : ∠ p A C + ∠ A C p + ∠ A p C = π := by
    have ht := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := A) (p₂ := C) p hCA
    rw [EuclideanGeometry.angle_comm C p A] at ht
    linarith
  have havoid' : ∠ B A C ∉ S ∧ ∠ A B p ∉ S ∧ ∠ A C p ∉ S ∧ π ∉ S := by
    refine ⟨havoid.1, ?_, ?_, havoid.2.2.2⟩
    · rw [hβ]
      exact havoid.2.1
    · rw [hγ]
      exact havoid.2.2.1
  exact cut_avoids_addSubgroup_branch S hα hpi hleft hright havoid'

open scoped Classical in
private theorem not_winning_iff_exists_avoiding_play (s : Strategy P) (θ : ℝ) :
    ¬ s.Winning θ ↔
      ∃ t₀ : Triangle ℝ P, ∃ c : ℕ → Prop,
        ∀ k : ℕ, ¬ WinsNow ((s.play t₀ c) (k + 1) (Fin.last k)) θ := by
  simp only [Strategy.Winning]
  push Not
  rfl

open scoped Classical in
private theorem no_winning_strategy_of_universal_subgroup_avoidance
    (S : AddSubgroup ℝ) (θ : ℝ) (hθ : θ ∈ S)
    (havoid : ∀ s : Strategy P,
      ∃ t₀ : Triangle ℝ P, ∃ c : ℕ → Prop,
        ∀ (k : ℕ) (i : Fin 3),
          ∠ (((s.play t₀ c) (k + 1) (Fin.last k)).points i)
            (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 1))
            (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 2)) ∉ S) :
    ¬ ∃ s : Strategy P, s.Winning θ := by
  rintro ⟨s, hs⟩
  obtain ⟨t₀, c, hc⟩ := havoid s
  obtain ⟨k, i, hi⟩ := hs t₀ c
  exact hc k i (hi ▸ hθ)

private lemma cyclic_right_angle_choice (A B C : ℝ)
    (hpos : 0 < A ∧ 0 < B ∧ 0 < C)
    (hsum : A + B + C = π) :
    A = π / 2 ∨ B = π / 2 ∨ C = π / 2 ∨
      ((B < π / 2 ∧ C < π / 2 ∧
          0 < π / 2 - B ∧ π / 2 - B < A ∧
          A - (π / 2 - B) = π / 2 - C) ∨
       (C < π / 2 ∧ A < π / 2 ∧
          0 < π / 2 - C ∧ π / 2 - C < B ∧
          B - (π / 2 - C) = π / 2 - A) ∨
       (A < π / 2 ∧ B < π / 2 ∧
          0 < π / 2 - A ∧ π / 2 - A < C ∧
          C - (π / 2 - A) = π / 2 - B)) := by
  rcases hpos with ⟨hA, hB, hC⟩
  by_cases hAe : A = π / 2
  · exact Or.inl hAe
  by_cases hBe : B = π / 2
  · exact Or.inr (Or.inl hBe)
  by_cases hCe : C = π / 2
  · exact Or.inr (Or.inr (Or.inl hCe))
  by_cases hAgt : π / 2 < A
  · right; right; right; left
    constructor
    · linarith [hsum]
    constructor
    · linarith [hsum]
    constructor
    · linarith
    constructor <;> linarith [hsum]
  have hAlt : A < π / 2 := lt_of_le_of_ne (le_of_not_gt hAgt) hAe
  by_cases hBgt : π / 2 < B
  · right; right; right; right; left
    constructor
    · linarith [hsum]
    constructor
    · exact hAlt
    constructor
    · linarith
    constructor <;> linarith [hsum]
  have hBlt : B < π / 2 := lt_of_le_of_ne (le_of_not_gt hBgt) hBe
  right; right; right; right; right
  exact ⟨hAlt, hBlt, by linarith, by linarith [hsum], by linarith [hsum]⟩

private theorem answer_angle_sum_parametric (θ : ℝ) (hθ : θ ∈ answer) :
    ∃ n : ℕ, 2 ≤ n ∧ ∀ t : Triangle ℝ P,
      ∠ (t.points 0) (t.points 1) (t.points 2) +
        ∠ (t.points 1) (t.points 2) (t.points 0) +
          ∠ (t.points 2) (t.points 0) (t.points 1) = (n : ℝ) * θ := by
  rcases hθ with ⟨n, hn, rfl⟩
  refine ⟨n, hn, ?_⟩
  intro t
  rw [EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := t.points 0) (p₂ := t.points 1) (t.points 2)
    (t.independent.injective.ne (by decide : (1 : Fin 3) ≠ 0))]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

private theorem answer_subset_winning_of_nat_family
    (hwin : ∀ n : ℕ, 2 ≤ n → ∃ s : Strategy P, s.Winning (π / (n : ℝ))) :
    answer ⊆ {θ : ℝ | 0 < θ ∧ θ < π ∧ ∃ s : Strategy P, s.Winning θ} := by
  rintro θ ⟨n, hn, rfl⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  refine ⟨div_pos Real.pi_pos hn0, ?_, hwin n hn⟩
  rw [div_lt_iff₀ hn0]
  nlinarith [Real.pi_pos]

private theorem result_exact_obligations :
    ({θ : ℝ | 0 < θ ∧ θ < π ∧ ∃ s : Strategy P, s.Winning θ} = answer) ↔
      ((∀ θ : ℝ, 0 < θ → θ < π → (∃ s : Strategy P, s.Winning θ) →
          ∃ n : ℕ, 2 ≤ n ∧ θ = π / (n : ℝ)) ∧
       (∀ n : ℕ, 2 ≤ n → ∃ s : Strategy P, s.Winning (π / (n : ℝ)))) := by
  constructor
  · intro h
    constructor
    · intro θ hθ0 hθπ hs
      have hm : θ ∈ answer := by
        rw [← h]
        exact ⟨hθ0, hθπ, hs⟩
      exact hm
    · intro n hn
      have hn0nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0nat
      have hn1nat : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1nat
      have hm : π / (n : ℝ) ∈ answer := ⟨n, hn, rfl⟩
      rw [← h] at hm
      exact hm.2.2
  · rintro ⟨hnecessary, hsufficient⟩
    ext θ
    constructor
    · rintro ⟨hθ0, hθπ, hs⟩
      exact hnecessary θ hθ0 hθπ hs
    · rintro ⟨n, hn, rfl⟩
      have hn0nat : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0nat
      have hn1nat : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn1nat
      refine ⟨div_pos Real.pi_pos hn0, ?_, hsufficient n hn⟩
      rw [div_lt_iff₀ hn0]
      nlinarith [Real.pi_pos]

private theorem triangle_angle_sum_as_nat_multiple (t : Triangle ℝ P) (n : ℕ) (θ : ℝ)
    (hn : 0 < n) (hθ : θ = π / (n : ℝ)) :
    ∠ (t.points 0) (t.points 1) (t.points 2) +
        ∠ (t.points 1) (t.points 2) (t.points 0) +
        ∠ (t.points 2) (t.points 0) (t.points 1) = (n : ℝ) * θ := by
  have h10 : t.points 1 ≠ t.points 0 :=
    t.independent.injective.ne (by decide)
  rw [EuclideanGeometry.angle_add_angle_add_angle_eq_pi (p₁ := t.points 0)
    (p₂ := t.points 1) (p₃ := t.points 2) h10]
  rw [hθ]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

private theorem some_triangle_angle_at_least_pi_over_n (t : Triangle ℝ P) (n : ℕ)
    (hn : 3 ≤ n) :
    π / (n : ℝ) ≤ ∠ (t.points 0) (t.points 1) (t.points 2) ∨
    π / (n : ℝ) ≤ ∠ (t.points 1) (t.points 2) (t.points 0) ∨
    π / (n : ℝ) ≤ ∠ (t.points 2) (t.points 0) (t.points 1) := by
  have h10 : t.points 1 ≠ t.points 0 :=
    t.independent.injective.ne (by decide)
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := t.points 0) (p₂ := t.points 1) (p₃ := t.points 2) h10
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hratio : 3 * (π / (n : ℝ)) ≤ π := by
    calc
      3 * (π / (n : ℝ)) = (3 * π) / (n : ℝ) := by ring
      _ ≤ π := (div_le_iff₀ hnpos).2 (by nlinarith [Real.pi_pos])
  by_contra h
  push_neg at h
  linarith

private theorem exists_forcing_move_decrement_multiple
    (t : Triangle ℝ P) (i : Fin 3) (θ : ℝ) (k : ℕ)
    (hθ : 0 < θ) (hk : 1 ≤ k)
    (hA : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) =
      ((k + 1 : ℕ) : ℝ) * θ) :
    ∃ m : Move t,
      WinsNow (m.half True) θ ∧ WinsNow (m.half False) ((k : ℝ) * θ) := by
  have hθA : θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) := by
    rw [hA]
    push_cast
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  obtain ⟨p, hp, hx⟩ := exists_cevian_with_angle t i θ hθ hθA
  let m : Move t := ⟨i, p, hp⟩
  refine ⟨m, (cevian_move_parametric_outcomes t i p hp θ hx).1, ?_⟩
  have hsplit :
      ∠ (t.points (i + 1)) (t.points i) p +
        ∠ p (t.points i) (t.points (i + 2)) =
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hp
  have hrem : ∠ p (t.points i) (t.points (i + 2)) = (k : ℝ) * θ := by
    rw [hA, hx] at hsplit
    push_cast at hsplit
    linarith
  refine ⟨2, ?_⟩
  simpa [Move.half, m] using hrem

private theorem exists_forcing_move_of_crossing
    (t : Triangle ℝ P) (i : Fin 3) (θ q : ℝ) (hθ : 0 < θ)
    (hBq : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < q)
    (hqAB : q <
      ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) +
        ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) :
    ∃ m : Move t,
      WinsNow (m.half True) (π - q) ∧ WinsNow (m.half False) q := by
  let A := t.points i
  let B := t.points (i + 1)
  let C := t.points (i + 2)
  let β := ∠ A B C
  let x := q - β
  have hx0 : 0 < x := by simpa [x, β, A, B, C] using sub_pos.mpr hBq
  have hxA : x < ∠ B A C := by
    dsimp only [x, β, A, B, C]
    linarith
  obtain ⟨p, hp, hx⟩ := exists_cevian_with_angle t i x hx0 hxA
  let m : Move t := ⟨i, p, hp⟩
  have hBA : B ≠ A := t.independent.injective.ne (by fin_cases i <;> decide)
  have hβ : ∠ A B p = β := by
    dsimp only [A, B, C, β]
    exact EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  have hleft : ∠ B A p + ∠ A B p + ∠ A p B = π := by
    have ht := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := A) (p₂ := B) p hBA
    rw [EuclideanGeometry.angle_comm p A B,
      EuclideanGeometry.angle_comm B p A] at ht
    linarith
  have hcut : ∠ A p B = π - q := by
    rw [hx, hβ] at hleft
    change ∠ A p B = π - q
    dsimp only [x] at hleft
    linarith
  refine ⟨m, ?_, ?_⟩
  · refine ⟨1, ?_⟩
    simpa [m, Move.half, A, B, EuclideanGeometry.angle_comm] using hcut
  · convert (cevian_move_parametric_outcomes t i p hp x hx).2 using 1
    dsimp only [x, β, A, B, C]
    ring

private lemma exists_invariant_binary_path {α : Type*} (Q : α → Prop)
    (next : α → Bool → α) (a₀ : α) (ha₀ : Q a₀)
    (hstep : ∀ a, Q a → Q (next a true) ∨ Q (next a false)) :
    ∃ T : ℕ → α, T 0 = a₀ ∧
      (∀ k, T (k + 1) = next (T k) true ∨ T (k + 1) = next (T k) false) ∧
      ∀ k, Q (T k) := by
  classical
  let step : {a // Q a} → {a // Q a} := fun a =>
    if h : Q (next a.1 true) then ⟨next a.1 true, h⟩
    else ⟨next a.1 false, (hstep a.1 a.2).resolve_left h⟩
  let U : ℕ → {a // Q a} := fun k => step^[k] ⟨a₀, ha₀⟩
  refine ⟨fun k => (U k).1, ?_, ?_, fun k => (U k).2⟩
  · rfl
  · intro k
    change (U (k + 1)).1 = next (U k).1 true ∨
      (U (k + 1)).1 = next (U k).1 false
    have hsucc : U (k + 1) = step (U k) := by
      simp [U, Function.iterate_succ_apply']
    rw [hsucc]
    simp only [step]
    split <;> simp_all

private lemma pi_not_mem_zmultiples_of_not_mem_answer (θ : ℝ)
    (hθ0 : 0 < θ) (hθπ : θ < π) (hnot : θ ∉ answer) :
    π ∉ AddSubgroup.zmultiples θ := by
  intro hpi
  rw [AddSubgroup.mem_zmultiples_iff] at hpi
  obtain ⟨z, hz⟩ := hpi
  rw [zsmul_eq_mul] at hz
  have hzpos : 0 < z := by
    by_contra h
    have hznonpos : (z : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt h)
    have hmul : (z : ℝ) * θ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hznonpos hθ0.le
    linarith [Real.pi_pos]
  let n : ℕ := z.toNat
  have hzInt : z = (n : ℤ) := by
    simpa [n] using (Int.eq_natCast_toNat.mpr hzpos.le)
  have hzn : (z : ℝ) = (n : ℝ) := by exact_mod_cast hzInt
  have hzgt1 : (1 : ℝ) < (z : ℝ) := by
    by_contra h
    have hzle1 : (z : ℝ) ≤ 1 := le_of_not_gt h
    have hmul : (z : ℝ) * θ ≤ 1 * θ :=
      mul_le_mul_of_nonneg_right hzle1 hθ0.le
    linarith
  have hn2 : 2 ≤ n := by
    have : (1 : ℝ) < (n : ℝ) := hzn ▸ hzgt1
    exact_mod_cast this
  apply hnot
  refine ⟨n, hn2, ?_⟩
  apply (eq_div_iff (show (n : ℝ) ≠ 0 by positivity)).2
  simpa [← hzn, mul_comm] using hz

private theorem winning_of_uniform_double_angle (θ : ℝ) (hθ : 0 < θ)
    (h : ∀ t : Triangle ℝ P, WinsNow t (2 * θ)) :
    ∃ s : Strategy P, s.Winning θ := by
  apply winning_of_one_step_parametric θ
  intro t
  obtain ⟨i, hi⟩ := h t
  apply exists_forcing_move_of_double_angle t (i + 1) θ hθ
  simpa [EuclideanGeometry.angle_comm, add_assoc] using hi

private theorem angle_increment_iterate_identity (β θ : ℝ) (k : ℕ) :
    (β + (k : ℝ) * θ) + θ = β + ((k + 1 : ℕ) : ℝ) * θ := by
  push_cast
  ring

private theorem cevian_move_preserves_angle_avoidance_branch
    (S : AddSubgroup ℝ) (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2)))
    (havoid : ∀ j : Fin 3,
      ∠ (t.points j) (t.points (j + 1)) (t.points (j + 2)) ∉ S)
    (hpi : π ∉ S) :
    let m : Move t := ⟨i, p, hp⟩
    (∀ j : Fin 3,
      ∠ ((m.half True).points j) ((m.half True).points (j + 1))
        ((m.half True).points (j + 2)) ∉ S) ∨
    (∀ j : Fin 3,
      ∠ ((m.half False).points j) ((m.half False).points (j + 1))
        ((m.half False).points (j + 2)) ∉ S) := by
  let m : Move t := ⟨i, p, hp⟩
  have hA : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) ∉ S := by
    fin_cases i
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 2
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 0
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 1
  have hB : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ∉ S := havoid i
  have hC : ∠ (t.points i) (t.points (i + 2)) (t.points (i + 1)) ∉ S := by
    fin_cases i
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 1
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 2
    · rw [EuclideanGeometry.angle_comm]; simpa using havoid 0
  rcases cevian_cut_preserves_angle_avoidance S t i p hp ⟨hA, hB, hC, hpi⟩ with h | h
  · left
    intro j
    fin_cases j
    · simpa [m, Move.half] using h.2.1
    · simpa [m, Move.half, EuclideanGeometry.angle_comm] using h.2.2
    · simpa [m, Move.half, EuclideanGeometry.angle_comm] using h.1
  · right
    intro j
    fin_cases j
    · simpa [m, Move.half] using h.2.1
    · simpa [m, Move.half, EuclideanGeometry.angle_comm] using h.2.2
    · simpa [m, Move.half, EuclideanGeometry.angle_comm] using h.1

open scoped Classical in
private theorem exists_strategy_play_preserving_invariant
    (Q : Triangle ℝ P → Prop) (s : Strategy P) (t₀ : Triangle ℝ P) (ht₀ : Q t₀)
    (hstep : ∀ (k : ℕ) (h : Fin (k + 1) → Triangle ℝ P),
      Q (h (Fin.last k)) →
        Q ((s h).half True) ∨ Q ((s h).half False)) :
    ∃ c : ℕ → Prop, ∀ k : ℕ,
      Q ((s.play t₀ c (k + 1)) (Fin.last k)) := by
  let H : (k : ℕ) → {h : Fin (k + 1) → Triangle ℝ P // Q (h (Fin.last k))} :=
    fun k => Nat.rec (motive := fun k =>
      {h : Fin (k + 1) → Triangle ℝ P // Q (h (Fin.last k))})
      ⟨![t₀], by simpa using ht₀⟩
      (fun k H =>
        if hT : Q ((s H.1).half True) then
          ⟨Fin.snoc H.1 ((s H.1).half True), by simpa using hT⟩
        else
          ⟨Fin.snoc H.1 ((s H.1).half False), by
            simpa using (hstep k H.1 H.2).resolve_left hT⟩) k
  let c : ℕ → Prop := fun k => Q ((s (H k).1).half True)
  letI : ∀ k, Decidable (c k) := fun _ => Classical.propDecidable _
  have hH : ∀ k : ℕ,
      (H (k + 1)).1 = Fin.snoc (H k).1 ((s (H k).1).half (c k)) := by
    intro k
    simp only [H]
    split
    · have hc : c k := by simpa only [c, H] using ‹Q ((s _).half True)›
      simp [Move.half, hc]
    · have hnc : ¬ c k := by simpa only [c, H] using ‹¬ Q ((s _).half True)›
      simp [Move.half, hnc]
  have hplay : ∀ k : ℕ, s.play t₀ c (k + 1) = (H k).1 := by
    intro k
    induction k with
    | zero => simp [Strategy.play, H]
    | succ k ih =>
        change Fin.snoc (s.play t₀ c (k + 1))
          ((s (s.play t₀ c (k + 1))).half (c k)) = (H (k + 1)).1
        rw [ih, hH k]
  refine ⟨c, fun k => ?_⟩
  rw [hplay k]
  exact (H k).2

open scoped Classical in
private theorem exists_avoiding_play_of_initial_triangle
    (S : AddSubgroup ℝ) (hpi : π ∉ S) (s : Strategy P)
    (t₀ : Triangle ℝ P)
    (ht₀ : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) ∉ S) :
    ∃ c : ℕ → Prop, ∀ (k : ℕ) (i : Fin 3),
      ∠ (((s.play t₀ c) (k + 1) (Fin.last k)).points i)
        (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 1))
        (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 2)) ∉ S := by
  let Q : Triangle ℝ P → Prop := fun t => ∀ i : Fin 3,
    ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ∉ S
  apply exists_strategy_play_preserving_invariant Q s t₀ ht₀
  intro k h hh
  exact cevian_move_preserves_angle_avoidance_branch S (h (Fin.last k))
    (s h).i (s h).p (s h).sbtw_p hh hpi

private theorem exists_coefficientRank (n : ℕ) (θ : ℝ) :
    ∃ rank : Triangle ℝ P → ℕ, ∀ t : Triangle ℝ P,
      (rank t = n - 1 ∨ ∃ r : ℕ,
        2 ≤ r ∧ r < n ∧ rank t = r - 1 ∧ WinsNow t ((r : ℝ) * θ)) ∧
      rank t ≤ n - 1 ∧
      ∀ r : ℕ, 2 ≤ r → r < n → WinsNow t ((r : ℝ) * θ) → rank t ≤ r - 1 := by
  classical
  let E : Triangle ℝ P → ℕ → Prop := fun t k =>
    k = n - 1 ∨ ∃ r : ℕ,
      2 ≤ r ∧ r < n ∧ k = r - 1 ∧ WinsNow t ((r : ℝ) * θ)
  have hE : ∀ t : Triangle ℝ P, ∃ k, E t k := fun t => ⟨n - 1, Or.inl rfl⟩
  let rank : Triangle ℝ P → ℕ := fun t => Nat.find (hE t)
  refine ⟨rank, fun t => ?_⟩
  have hspec : E t (rank t) := Nat.find_spec (hE t)
  have hdefault : rank t ≤ n - 1 := by
    exact Nat.find_min' (hE t) (Or.inl rfl)
  refine ⟨hspec, hdefault, ?_⟩
  intro r hr2 hrn hwin
  apply Nat.find_min' (hE t)
  exact Or.inr ⟨r, hr2, hrn, rfl, hwin⟩

private theorem mem_answer_iff_nat_mul_eq_pi (θ : ℝ) :
    θ ∈ answer ↔ ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) * θ = π := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n, hn, ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
  · rintro ⟨n, hn, hmul⟩
    refine ⟨n, hn, ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    exact (eq_div_iff hn0).2 (by simpa [mul_comm] using hmul)

private theorem parametric_increment_lt_denominator
    (n k : ℕ) (θ β : ℝ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hperiod : (n : ℝ) * θ = π)
    (hbudget : β + (k : ℝ) * θ < π) : k < n := by
  have hkR : (k : ℝ) < (n : ℝ) := by
    nlinarith
  exact_mod_cast hkR

private theorem parametric_increment_decreases_denominator_rank
    (n k : ℕ) (θ β : ℝ) (hθ : 0 < θ) (hβ : 0 ≤ β)
    (hperiod : (n : ℝ) * θ = π)
    (hbudget : β + (k : ℝ) * θ < π) :
    n - (k + 1) < n - k := by
  have hkR : (k : ℝ) < (n : ℝ) := by
    nlinarith
  have hk : k < n := by exact_mod_cast hkR
  omega

theorem cut_preserves_addSubgroup_avoidance
    {G : Type*} [AddCommGroup G] (S : AddSubgroup G)
    {α β γ δ ε φ ψ p : G}
    (hαeq : α = δ + ε) (hpeq : p = φ + ψ)
    (hleft : δ + β + φ = p) (hright : ε + γ + ψ = p)
    (hα : α ∉ S) (hβ : β ∉ S) (hγ : γ ∉ S) (hp : p ∉ S) :
    (δ ∉ S ∧ β ∉ S ∧ φ ∉ S) ∨
      (ε ∉ S ∧ γ ∉ S ∧ ψ ∉ S) := by
  classical
  by_contra h
  have h₁ : δ ∈ S ∨ β ∈ S ∨ φ ∈ S := by
    by_cases hδ : δ ∈ S
    · exact Or.inl hδ
    by_cases hβ' : β ∈ S
    · exact Or.inr (Or.inl hβ')
    · exact Or.inr (Or.inr (by
        by_contra hφ
        exact h (Or.inl ⟨hδ, hβ', hφ⟩)))
  have h₂ : ε ∈ S ∨ γ ∈ S ∨ ψ ∈ S := by
    by_cases hε : ε ∈ S
    · exact Or.inl hε
    by_cases hγ' : γ ∈ S
    · exact Or.inr (Or.inl hγ')
    · exact Or.inr (Or.inr (by
        by_contra hψ
        exact h (Or.inr ⟨hε, hγ', hψ⟩)))
  rcases cut_hits_addSubgroup S hαeq hpeq hleft hright h₁ h₂ with ha | hb | hg | hp'
  · exact hα ha
  · exact hβ hb
  · exact hγ hg
  · exact hp hp'

private lemma pi_div_three_not_mem_addSubgroup
    (S : AddSubgroup ℝ) (hpi : π ∉ S) : π / 3 ∉ S := by
  intro hthird
  apply hpi
  have hsum : π / 3 + π / 3 + π / 3 ∈ S :=
    S.add_mem (S.add_mem hthird hthird) hthird
  convert hsum using 1 <;> ring

private theorem mem_zmultiples_iff_mem_answer (θ : ℝ) (hθ : 0 < θ) (hθπ : θ < π) :
    π ∈ AddSubgroup.zmultiples θ ↔ θ ∈ answer := by
  constructor
  · rw [AddSubgroup.mem_zmultiples_iff]
    rintro ⟨z, hz⟩
    rw [zsmul_eq_mul] at hz
    have hzR : 0 < (z : ℝ) := by nlinarith [Real.pi_pos]
    have hzI : 0 < z := by exact_mod_cast hzR
    have hz_ne_one : z ≠ 1 := by
      intro heq
      subst z
      norm_num at hz
      linarith
    have hz2 : (2 : ℤ) ≤ z := by omega
    let n : ℕ := z.toNat
    have hnz : (n : ℤ) = z := by simp [n, Int.toNat_of_nonneg (le_of_lt hzI)]
    have hnR : (n : ℝ) = (z : ℝ) := by exact_mod_cast hnz
    have hn2 : 2 ≤ n := by exact_mod_cast (hnz.symm ▸ hz2)
    refine ⟨n, hn2, ?_⟩
    apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).2
    rw [hnR]
    nlinarith
  · rintro ⟨n, hn, rfl⟩
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(n : ℤ), ?_⟩
    rw [zsmul_eq_mul]
    push_cast
    field_simp
open scoped Classical in
private theorem winning_implies_mem_answer_of_pi_div_three_triangle
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < π)
    (t₀ : Triangle ℝ P)
    (ht₀ : ∀ i : Fin 3,
      ∠ (t₀.points i) (t₀.points (i + 1)) (t₀.points (i + 2)) = π / 3)
    (hwin : ∃ s : Strategy P, s.Winning θ) : θ ∈ answer := by
  by_contra hanswer
  let S : AddSubgroup ℝ := AddSubgroup.zmultiples θ
  have hpi : π ∉ S := by
    simpa [S] using pi_not_mem_zmultiples_of_not_mem_answer θ hθ0 hθπ hanswer
  have hθS : θ ∈ S := by
    change θ ∈ AddSubgroup.zmultiples θ
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨1, by simp⟩
  have havoid : ∀ s : Strategy P,
      ∃ t₀ : Triangle ℝ P, ∃ c : ℕ → Prop,
        ∀ (k : ℕ) (i : Fin 3),
          ∠ (((s.play t₀ c) (k + 1) (Fin.last k)).points i)
            (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 1))
            (((s.play t₀ c) (k + 1) (Fin.last k)).points (i + 2)) ∉ S := by
    intro s
    refine ⟨t₀, ?_⟩
    apply exists_avoiding_play_of_initial_triangle S hpi s t₀
    intro i
    rw [ht₀ i]
    exact pi_div_three_not_mem_addSubgroup S hpi
  exact (no_winning_strategy_of_universal_subgroup_avoidance S θ hθS havoid) hwin

theorem winning_of_wellFoundedRank_descent {α : Type*} (r : α → α → Prop)
    (wf : WellFounded r) (θ : ℝ) (rank : Triangle ℝ P → α)
    (hstep : ∀ t : Triangle ℝ P, ∃ m : Move t,
      (WinsNow t θ ∨ WinsNow (m.half True) θ ∨ r (rank (m.half True)) (rank t)) ∧
      (WinsNow t θ ∨ WinsNow (m.half False) θ ∨ r (rank (m.half False)) (rank t))) :
    ∃ s : Strategy P, s.Winning θ := by
  classical
  let s : Strategy P := fun {k} t => Classical.choose (hstep (t (Fin.last k)))
  refine ⟨s, ?_⟩
  intro t₀ c
  let T : ℕ → Triangle ℝ P := fun k => (s.play t₀ c (k + 1)) (Fin.last k)
  have hs : ∀ k, WinsNow (T k) θ ∨ WinsNow (T (k + 1)) θ ∨
      r (rank (T (k + 1))) (rank (T k)) := by
    intro k
    by_cases hc : c k
    · simpa only [T, play_last_succ_identity, s, Move.half, hc] using
        (Classical.choose_spec (hstep (T k))).1
    · simpa only [T, play_last_succ_identity, s, Move.half, hc] using
        (Classical.choose_spec (hstep (T k))).2
  let Q : α → Prop := fun a => ∀ U : ℕ → Triangle ℝ P, rank (U 0) = a →
      (∀ k, WinsNow (U k) θ ∨ WinsNow (U (k + 1)) θ ∨
        r (rank (U (k + 1))) (rank (U k))) → ∃ k, WinsNow (U k) θ
  have hQ (a : α) : Q a := wf.induction a (by
    intro a ih U ha hU
    rcases hU 0 with h0 | h1 | hlt
    · exact ⟨0, h0⟩
    · exact ⟨1, by simpa using h1⟩
    · have hlt' : r (rank (U 1)) a := by simpa [ha] using hlt
      obtain ⟨k, hk⟩ := ih (rank (U 1)) hlt' (fun j => U (j + 1)) rfl (by
        intro j
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hU (j + 1))
      exact ⟨k + 1, hk⟩)
  exact hQ (rank (T 0)) T rfl hs

private theorem move_angle_conservation (t : Triangle ℝ P) (m : Move t) :
    let A := t.points m.i
    let B := t.points (m.i + 1)
    let C := t.points (m.i + 2)
    let D := m.p
    ∠ B A C = ∠ B A D + ∠ D A C ∧
    π = ∠ A D B + ∠ A D C ∧
    ∠ B A D + ∠ A B C + ∠ A D B = π ∧
    ∠ D A C + ∠ A C B + ∠ A D C = π := by
  dsimp only
  have hsplit :
      ∠ (t.points (m.i + 1)) (t.points m.i) m.p +
        ∠ m.p (t.points m.i) (t.points (m.i + 2)) =
      ∠ (t.points (m.i + 1)) (t.points m.i) (t.points (m.i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw (p := t.points m.i) m.sbtw_p
  have hBD : ∠ (t.points m.i) (t.points (m.i + 1)) m.p =
      ∠ (t.points m.i) (t.points (m.i + 1)) (t.points (m.i + 2)) :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi _ m.sbtw_p.angle₁₂₃_eq_pi
  have hCD : ∠ (t.points m.i) (t.points (m.i + 2)) m.p =
      ∠ (t.points m.i) (t.points (m.i + 2)) (t.points (m.i + 1)) :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi _ m.sbtw_p.symm.angle₁₂₃_eq_pi
  have hsupp := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
    (t.points m.i) m.sbtw_p.angle₁₂₃_eq_pi
  have hi1 : m.i + 1 ≠ m.i := by omega
  have hi2 : m.i + 2 ≠ m.i := by omega
  have hAB : t.points (m.i + 1) ≠ t.points m.i := t.independent.injective.ne hi1
  have hAC : t.points (m.i + 2) ≠ t.points m.i := t.independent.injective.ne hi2
  have hleft := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := t.points m.i) (p₂ := t.points (m.i + 1)) m.p hAB
  have hright := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (p₁ := t.points m.i) (p₂ := t.points (m.i + 2)) m.p hAC
  have hcLB := EuclideanGeometry.angle_comm
    (t.points (m.i + 1)) m.p (t.points m.i)
  have hcLA := EuclideanGeometry.angle_comm
    m.p (t.points m.i) (t.points (m.i + 1))
  have hcRC := EuclideanGeometry.angle_comm
    (t.points (m.i + 2)) m.p (t.points m.i)
  constructor
  · linarith
  constructor
  · exact hsupp.symm
  constructor
  · linarith
  · linarith

private theorem exists_right_angle_forcing_move_of_crossing
    (t : Triangle ℝ P) (i : Fin 3)
    (hB : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < π / 2)
    (hAB : π / 2 <
      ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) +
        ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) :
    ∃ m : Move t,
      WinsNow (m.half True) (π / 2) ∧ WinsNow (m.half False) (π / 2) := by
  obtain ⟨m, hmT, hmF⟩ := exists_forcing_move_of_crossing
    t i (π / 2) (π / 2) (by positivity) hB hAB
  refine ⟨m, ?_, hmF⟩
  convert hmT using 1 <;> ring

private theorem exists_forcing_move_of_lattice_crossing
    (t : Triangle ℝ P) (i : Fin 3) (n k : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hk : k ≤ n) (hperiod : (n : ℝ) * θ = π)
    (hB : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < (k : ℝ) * θ)
    (hAB : (k : ℝ) * θ <
      ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) +
        ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) :
    ∃ m : Move t,
      WinsNow (m.half True) (((n - k : ℕ) : ℝ) * θ) ∧
      WinsNow (m.half False) ((k : ℝ) * θ) := by
  obtain ⟨m, hmT, hmF⟩ := exists_forcing_move_of_crossing
    t i θ ((k : ℝ) * θ) hθ hB hAB
  refine ⟨m, ?_, hmF⟩
  convert hmT using 1
  rw [Nat.cast_sub hk, ← hperiod]
  ring

theorem cevian_preserves_angle_avoidance
    (S : AddSubgroup ℝ) (A B C p : P)
    (hp : Sbtw ℝ B p C) (hBA : B ≠ A) (hCA : C ≠ A)
    (havoid : ∠ B A C ∉ S ∧ ∠ A B C ∉ S ∧ ∠ A C B ∉ S ∧ π ∉ S) :
    (∠ B A p ∉ S ∧ ∠ A B p ∉ S ∧ ∠ A p B ∉ S) ∨
    (∠ p A C ∉ S ∧ ∠ A C p ∉ S ∧ ∠ A p C ∉ S) := by
  have hα : ∠ B A C = ∠ B A p + ∠ p A C :=
    (EuclideanGeometry.angle_add_angle_eq_of_sbtw hp).symm
  have hpπ : π = ∠ A p B + ∠ A p C := by
    symm
    exact EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  have hBp : ∠ A B p = ∠ A B C :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.angle₁₂₃_eq_pi
  have hCp : ∠ A C p = ∠ A C B :=
    EuclideanGeometry.angle_eq_angle_of_angle_eq_pi A hp.angle₃₂₁_eq_pi
  have hleft : ∠ B A p + ∠ A B C + ∠ A p B = π := by
    have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := A) (p₂ := B) p hBA
    rw [hBp, EuclideanGeometry.angle_comm B p A,
      EuclideanGeometry.angle_comm p A B] at htri
    linarith
  have hright : ∠ p A C + ∠ A C B + ∠ A p C = π := by
    have htri := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := A) (p₂ := C) p hCA
    rw [hCp, EuclideanGeometry.angle_comm C p A] at htri
    linarith
  classical
  by_cases hl : ∠ B A p ∉ S ∧ ∠ A B C ∉ S ∧ ∠ A p B ∉ S
  · left
    exact ⟨hl.1, hBp ▸ hl.2.1, hl.2.2⟩
  · right
    have h₁ : ∠ B A p ∈ S ∨ ∠ A B C ∈ S ∨ ∠ A p B ∈ S := by
      simp only [not_and_or, not_not] at hl
      exact hl
    have h₂ : ¬ (∠ p A C ∈ S ∨ ∠ A C B ∈ S ∨ ∠ A p C ∈ S) := by
      intro h₂
      rcases cut_hits_addSubgroup S
        (α := ∠ B A C) (β := ∠ A B C) (γ := ∠ A C B)
        (δ := ∠ B A p) (ε := ∠ p A C)
        (φ := ∠ A p B) (ψ := ∠ A p C) (p := π)
        hα hpπ hleft hright h₁ h₂ with ha | hb | hc | hpi
      · exact havoid.1 ha
      · exact havoid.2.1 hb
      · exact havoid.2.2.1 hc
      · exact havoid.2.2.2 hpi
    simp only [not_or] at h₂
    exact ⟨h₂.1, hCp ▸ h₂.2.1, h₂.2.2⟩

private lemma scaled_integer_crossing
    {A B C θ : ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hθ : 0 < θ)
    (hpos : 0 < A ∧ 0 < B ∧ 0 < C)
    (hsum : A + B + C = (n : ℝ) * θ)
    (hnint : ∀ x ∈ ({A / θ, B / θ, C / θ} : Set ℝ),
      x ∉ Set.range ((↑) : ℤ → ℝ)) :
    (∃ k : ℤ, B < (k : ℝ) * θ ∧ (k : ℝ) * θ < A + B) ∨
    (∃ k : ℤ, C < (k : ℝ) * θ ∧ (k : ℝ) * θ < B + C) ∨
    (∃ k : ℤ, A < (k : ℝ) * θ ∧ (k : ℝ) * θ < C + A) := by
  have hsum' : A / θ + B / θ + C / θ = (n : ℝ) := by
    calc
      A / θ + B / θ + C / θ = (A + B + C) / θ := by ring
      _ = ((n : ℝ) * θ) / θ := by rw [hsum]
      _ = (n : ℝ) := by field_simp
  have hpos' : 0 < A / θ ∧ 0 < B / θ ∧ 0 < C / θ :=
    ⟨div_pos hpos.1 hθ, div_pos hpos.2.1 hθ, div_pos hpos.2.2 hθ⟩
  have scale_lt {x y : ℝ} (hxy : x < y) : x * θ < y * θ := by
    nlinarith [mul_pos (sub_pos.mpr hxy) hθ]
  rcases normalized_integer_crossing hn hpos' hsum' hnint with
      h | h | h
  · left
    rcases h with ⟨k, hk₁, hk₂⟩
    refine ⟨k, ?_, ?_⟩
    · convert scale_lt hk₁ using 1 <;> field_simp
    · convert scale_lt hk₂ using 1 <;> field_simp
  · right; left
    rcases h with ⟨k, hk₁, hk₂⟩
    refine ⟨k, ?_, ?_⟩
    · convert scale_lt hk₁ using 1 <;> field_simp
    · convert scale_lt hk₂ using 1 <;> field_simp
  · right; right
    rcases h with ⟨k, hk₁, hk₂⟩
    refine ⟨k, ?_, ?_⟩
    · convert scale_lt hk₁ using 1 <;> field_simp
    · convert scale_lt hk₂ using 1 <;> field_simp

private lemma div_not_integer_iff_not_mem_zmultiples
    {x θ : ℝ} (hθ : θ ≠ 0) :
    x / θ ∉ Set.range ((↑) : ℤ → ℝ) ↔
      x ∉ AddSubgroup.zmultiples θ := by
  constructor
  · intro hdiv hmem
    apply hdiv
    rw [AddSubgroup.mem_zmultiples_iff] at hmem
    rcases hmem with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk]
    simp [zsmul_eq_mul, hθ]
  · intro hmem hdiv
    apply hmem
    rw [AddSubgroup.mem_zmultiples_iff]
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul]
    exact ((div_eq_iff hθ).mp hk.symm).symm

private lemma exists_positive_angle_triple_avoiding_addSubgroup
    (S : AddSubgroup ℝ) (hpi : π ∉ S) :
    ∃ A B C : ℝ,
      0 < A ∧ 0 < B ∧ 0 < C ∧ A + B + C = π ∧
      A ∉ S ∧ B ∉ S ∧ C ∉ S := by
  have hthird : π / 3 ∉ S := by
    intro h
    apply hpi
    have hsum : (3 : ℕ) • (π / 3) ∈ S := S.nsmul_mem h 3
    rw [nsmul_eq_mul] at hsum
    convert hsum using 1 <;> ring
  refine ⟨π / 3, π / 3, π / 3, by positivity, by positivity, by positivity, ?_,
    hthird, hthird, hthird⟩
  ring

private theorem exists_forcing_move_of_angle_sum
    (t : Triangle ℝ P) (i : Fin 3) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (hA : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) = x + y) :
    ∃ m : Move t, WinsNow (m.half True) x ∧ WinsNow (m.half False) y := by
  have hxA : x < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) := by
    rw [hA]
    linarith
  obtain ⟨p, hp, hleft⟩ := exists_cevian_with_angle t i x hx hxA
  have hsum :
      ∠ (t.points (i + 1)) (t.points i) p +
        ∠ p (t.points i) (t.points (i + 2)) =
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hp
  have hright : ∠ p (t.points i) (t.points (i + 2)) = y := by
    rw [hleft, hA] at hsum
    linarith
  let m : Move t := ⟨i, p, hp⟩
  refine ⟨m, ?_, ?_⟩
  · refine ⟨2, ?_⟩
    simpa [m, Move.half, EuclideanGeometry.angle_comm] using hleft
  · refine ⟨2, ?_⟩
    simpa [m, Move.half] using hright

private lemma exists_pi_div_three_triangle_exists_equilateral :
    ∃ t : Triangle ℝ P, ∀ i : Fin 3,
      dist (t.points i) (t.points (i + 1)) =
        dist (t.points (i + 1)) (t.points (i + 2)) := by
  letI : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  let e : Fin (finrank ℝ V) ≃ Fin 2 := finCongr Fact.out
  let b : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex e
  let p : P := Classical.choice inferInstance
  let w : V := (1 / 2 : ℝ) • b 0 + (Real.sqrt 3 / 2) • b 1
  have hnorm : ‖b 0‖ = 1 ∧ ‖w‖ = 1 ∧ ‖w - b 0‖ = 1 := by
    have hn0 : ‖b 0‖ = 1 := b.orthonormal.1 0
    have hn1 : ‖b 1‖ = 1 := b.orthonormal.1 1
    have ho : inner ℝ (b 0) (b 1) = 0 := b.orthonormal.2 (by decide)
    have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    refine ⟨hn0, ?_, ?_⟩
    · rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
      simp only [pow_two]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ)]
      · simp [norm_smul, hn0, hn1, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg 3)]
        nlinarith [hsqrt]
      · simp [inner_smul_left, inner_smul_right, ho]
    · have heq : w - b 0 =
          (-1 / 2 : ℝ) • b 0 + (Real.sqrt 3 / 2) • b 1 := by
          dsimp [w]
          module
      rw [heq, ← sq_eq_sq₀ (norm_nonneg _) (by norm_num)]
      simp only [pow_two]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ)]
      · simp [norm_smul, hn0, hn1, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg 3)]
        nlinarith [hsqrt]
      · simp [inner_smul_left, inner_smul_right, ho]
  have haff : AffineIndependent ℝ ![p, b 0 +ᵥ p, w +ᵥ p] := by
    have hli : LinearIndependent ℝ ![b 0, w] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have h1 := congrArg (fun v : V => inner ℝ (b 1) v) hg
      have h0 := congrArg (fun v : V => inner ℝ (b 0) v) hg
      have hb := orthonormal_iff_ite.mp b.orthonormal
      simp [Fin.sum_univ_two, w, inner_add_right, inner_smul_right, hb] at h0 h1
      fin_cases i
      · simpa [h1] using h0
      · exact h1
    apply (affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)).2
    let f : Fin 2 → {j : Fin 3 // j ≠ 0} := fun i => ⟨i.succ, Fin.succ_ne_zero i⟩
    have hfi : Function.Injective f := by
      intro i j hij
      apply Fin.succ_inj.mp
      exact congrArg Subtype.val hij
    have hfs : Function.Surjective f := by
      rintro ⟨j, hj⟩
      fin_cases j
      · simp at hj
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    let q : Fin 2 ≃ {j : Fin 3 // j ≠ 0} := Equiv.ofBijective f ⟨hfi, hfs⟩
    have hli' := hli.comp q.symm q.symm.injective
    have heq :
        (fun j : {j : Fin 3 // j ≠ 0} =>
          ![p, b 0 +ᵥ p, w +ᵥ p] (j : Fin 3) -ᵥ
          ![p, b 0 +ᵥ p, w +ᵥ p] 0) =
        (![b 0, w] ∘ q.symm) := by
      funext j
      rcases j with ⟨j, hj⟩
      fin_cases j
      · simp at hj
      · have hq : q.symm ⟨1, hj⟩ = 0 := by
          apply q.injective
          simp [q, f]
        simp [hq]
      · have hq : q.symm ⟨2, hj⟩ = 1 := by
          apply q.injective
          simp [q, f]
        simp [hq]
    rw [heq]
    exact hli'
  have hd01 : dist p (b 0 +ᵥ p) = 1 := by
    rw [dist_comm, dist_eq_norm_vsub V]
    convert hnorm.1 using 1 <;> simp
  have hd12 : dist (b 0 +ᵥ p) (w +ᵥ p) = 1 := by
    rw [dist_eq_norm_vsub V]
    simpa [norm_sub_rev] using hnorm.2.2
  have hd20 : dist (w +ᵥ p) p = 1 := by
    rw [dist_eq_norm_vsub V]
    simpa using hnorm.2.1
  let t : Triangle ℝ P := ⟨![p, b 0 +ᵥ p, w +ᵥ p], haff⟩
  refine ⟨t, ?_⟩
  intro i
  fin_cases i <;> simp [t, hd01, hd12, hd20, dist_comm]

private lemma research_cos_half_angle_eq_pi_div_three
    {a b c : P} (hcos : Real.cos (∠ a b c) = (1 : ℝ) / 2) :
    ∠ a b c = π / 3 := by
  exact Real.injOn_cos
    ⟨angle_nonneg _ _ _, angle_le_pi _ _ _⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
    (by simpa only [Real.cos_pi_div_three] using hcos)

private lemma exists_pi_div_three_triangle_angle_eq_of_cos_eq_half
    {a b c : P} (hcos : Real.cos (∠ a b c) = (1 : ℝ) / 2) :
    ∠ a b c = π / 3 := by
  exact research_cos_half_angle_eq_pi_div_three hcos

omit [Fact (finrank ℝ V = 2)] in
private lemma exists_pi_div_three_triangle_vertex_cos_of_equilateral
    (t : Triangle ℝ P)
    (hside : ∀ i : Fin 3,
      dist (t.points i) (t.points (i + 1)) =
        dist (t.points (i + 1)) (t.points (i + 2)))
    (i : Fin 3) :
    Real.cos (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) =
      (1 : ℝ) / 2 := by
  have hcycle : i + 1 + 2 = i := by
    fin_cases i <;> rfl
  have hs₁ := hside i
  have hs₂ := hside (i + 1)
  have hBC_AC : dist (t.points (i + 1)) (t.points (i + 2)) =
      dist (t.points i) (t.points (i + 2)) := by
    rw [hcycle] at hs₂
    simpa [add_assoc, dist_comm] using hs₂
  have hne : t.points i ≠ t.points (i + 1) := by
    apply t.independent.injective.ne
    fin_cases i <;> decide
  have hpos : 0 < dist (t.points i) (t.points (i + 1)) := dist_pos.mpr hne
  have hlaw :=
    dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (t.points i) (t.points (i + 1)) (t.points (i + 2))
  rw [dist_comm (t.points (i + 2)) (t.points (i + 1)), ← hs₁, ← hBC_AC,
    ← hs₁] at hlaw
  have hfactor : dist (t.points i) (t.points (i + 1)) ^ 2 *
      (2 * Real.cos (∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hcos
  · exact ((pow_ne_zero 2 (ne_of_gt hpos)) hzero).elim
  · nlinarith

private lemma exists_pi_div_three_triangle_angles_of_equilateral
    (t : Triangle ℝ P)
    (hside : ∀ i : Fin 3,
      dist (t.points i) (t.points (i + 1)) =
        dist (t.points (i + 1)) (t.points (i + 2))) :
    ∀ i : Fin 3,
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) = π / 3 := by
  intro i
  apply exists_pi_div_three_triangle_angle_eq_of_cos_eq_half
  exact exists_pi_div_three_triangle_vertex_cos_of_equilateral t hside i

private lemma exists_pi_div_three_triangle :
    ∃ t : Triangle ℝ P, ∀ i : Fin 3,
      ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) = π / 3 := by
  obtain ⟨t, hside⟩ :=
    exists_pi_div_three_triangle_exists_equilateral (V := V) (P := P)
  exact ⟨t,
    exists_pi_div_three_triangle_angles_of_equilateral (V := V) (P := P) t hside⟩

private theorem cevian_move_parametric_split_identity
    (t : Triangle ℝ P) (i : Fin 3) (p : P)
    (hp : Sbtw ℝ (t.points (i + 1)) p (t.points (i + 2))) (x : ℝ)
    (hx : ∠ (t.points (i + 1)) (t.points i) p = x) :
    let m : Move t := ⟨i, p, hp⟩
    WinsNow (m.half True) x ∧
      WinsNow (m.half False)
        (∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) - x) := by
  let m : Move t := ⟨i, p, hp⟩
  change WinsNow (m.half True) x ∧
    WinsNow (m.half False)
      (∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) - x)
  have hsum :
      ∠ (t.points (i + 1)) (t.points i) p +
        ∠ p (t.points i) (t.points (i + 2)) =
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hp
  have hright :
      ∠ p (t.points i) (t.points (i + 2)) =
        ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) - x := by
    rw [hx] at hsum
    linarith
  constructor
  · refine ⟨2, ?_⟩
    simpa [Move.half, m, EuclideanGeometry.angle_comm] using hx
  · refine ⟨2, ?_⟩
    simpa [Move.half, m] using hright

private theorem exists_forcing_move_of_nat_multiple_decrement
    (t : Triangle ℝ P) (i : Fin 3) (θ : ℝ) (k : ℕ)
    (hθ : 0 < θ)
    (hA : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) =
      ((k + 2 : ℕ) : ℝ) * θ) :
    ∃ m : Move t,
      WinsNow (m.half True) θ ∧
      WinsNow (m.half False) (((k + 1 : ℕ) : ℝ) * θ) := by
  have hθA : θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) := by
    rw [hA]
    norm_num [Nat.cast_add]
    nlinarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  obtain ⟨p, hp, hleft⟩ := exists_cevian_with_angle t i θ hθ hθA
  let m : Move t := ⟨i, p, hp⟩
  have hsum :
      ∠ (t.points (i + 1)) (t.points i) p +
        ∠ p (t.points i) (t.points (i + 2)) =
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) :=
    EuclideanGeometry.angle_add_angle_eq_of_sbtw hp
  have hright :
      ∠ p (t.points i) (t.points (i + 2)) = (((k + 1 : ℕ) : ℝ) * θ) := by
    rw [hleft, hA] at hsum
    norm_num [Nat.cast_add] at hsum ⊢
    linarith
  refine ⟨m, ?_, ?_⟩
  · refine ⟨2, ?_⟩
    simpa [Move.half, m, EuclideanGeometry.angle_comm] using hleft
  · refine ⟨2, ?_⟩
    simpa [Move.half, m] using hright

private lemma crossing_int_to_nat_index
    {A B θ : ℝ} {n : ℕ} {k : ℤ}
    (hθ : 0 < θ) (hperiod : (n : ℝ) * θ = π)
    (hB : 0 < B) (hABπ : A + B < π)
    (hk : B < (k : ℝ) * θ ∧ (k : ℝ) * θ < A + B) :
    ∃ r : ℕ, 1 ≤ r ∧ r < n ∧ (r : ℝ) = (k : ℝ) := by
  have hkposR : 0 < (k : ℝ) := by
    have : 0 < (k : ℝ) * θ := lt_trans hB hk.1
    nlinarith
  have hkpos : 0 < k := by exact_mod_cast hkposR
  have hmul : (k : ℝ) * θ < (n : ℝ) * θ := by
    rw [hperiod]
    exact lt_trans hk.2 hABπ
  have hknR : (k : ℝ) < (n : ℝ) := by
    by_contra hnot
    have hle : (n : ℝ) ≤ (k : ℝ) := le_of_not_gt hnot
    have hprod : (n : ℝ) * θ ≤ (k : ℝ) * θ :=
      mul_le_mul_of_nonneg_right hle (le_of_lt hθ)
    linarith
  have hkn : k < (n : ℤ) := by exact_mod_cast hknR
  let r : ℕ := k.toNat
  have hrk : (r : ℤ) = k := by
    simp [r, Int.toNat_of_nonneg (le_of_lt hkpos)]
  have hrposZ : (0 : ℤ) < (r : ℤ) := by simpa [hrk] using hkpos
  have hrnZ : (r : ℤ) < (n : ℤ) := by simpa [hrk] using hkn
  refine ⟨r, ?_, ?_, ?_⟩
  · exact_mod_cast hrposZ
  · exact_mod_cast hrnZ
  · exact_mod_cast hrk

private theorem exists_right_angle_forcing_move_of_adjacent_acute
    (t : Triangle ℝ P) (i : Fin 3)
    (hx0 : 0 < π / 2 - ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)))
    (hxA : π / 2 - ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) <
      ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2))) :
    ∃ m : Move t, WinsNow (m.half True) (π / 2) ∧
      WinsNow (m.half False) (π / 2) := by
  let x := π / 2 - ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))
  obtain ⟨p, hp, hxp⟩ := exists_cevian_with_angle t i x hx0 hxA
  let m : Move t := ⟨i, p, hp⟩
  have hfalse : WinsNow (m.half False) (π / 2) := by
    have hout := (cevian_move_parametric_outcomes t i p hp x hxp).2
    simpa [m, x] using hout
  have hopp : ∠ (t.points i) p (t.points (i + 2)) = π / 2 := by
    have h := cevian_opposite_child_angle t i p hp
    rw [h, hxp]
    simp [x]
  have hsupp := EuclideanGeometry.angle_add_angle_eq_pi_of_angle_eq_pi
    (t.points i) hp.angle₁₂₃_eq_pi
  have hleftp : ∠ (t.points i) p (t.points (i + 1)) = π / 2 := by
    rw [hopp] at hsupp
    linarith
  refine ⟨m, ?_, hfalse⟩
  refine ⟨1, ?_⟩
  simpa [m, Move.half, EuclideanGeometry.angle_comm] using hleftp

private lemma right_angle_winning_of_cyclic_choice :
    ∃ s : Strategy P, s.Winning (π / 2) := by
  apply winning_of_natRank_descent (π / 2) (fun _ => 0)
  intro t
  let A := ∠ (t.points 1) (t.points 0) (t.points 2)
  let B := ∠ (t.points 0) (t.points 1) (t.points 2)
  let C := ∠ (t.points 1) (t.points 2) (t.points 0)
  have hA : 0 < A := by
    apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (k := ℝ)
      (p := t.points) (i₁ := 1) (i₂ := 0) (i₃ := 2)
      (by decide) (by decide) (by decide)).mp t.independent
  have hB : 0 < B := by
    apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (k := ℝ)
      (p := t.points) (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide)).mp t.independent
  have hC : 0 < C := by
    apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (k := ℝ)
      (p := t.points) (i₁ := 1) (i₂ := 2) (i₃ := 0)
      (by decide) (by decide) (by decide)).mp t.independent
  have hsum : A + B + C = π := by
    have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
      (p₁ := t.points 0) (p₂ := t.points 1) (p₃ := t.points 2)
      (t.independent.injective.ne (by decide))
    simpa [A, B, C, EuclideanGeometry.angle_comm, add_comm, add_left_comm,
      add_assoc] using h
  rcases cyclic_right_angle_choice A B C ⟨hA, hB, hC⟩ hsum with
      hAe | hBe | hCe | hacute
  · have hwin : WinsNow t (π / 2) := by
      refine ⟨2, ?_⟩
      change ∠ (t.points 2) (t.points 0) (t.points 1) = π / 2
      rw [EuclideanGeometry.angle_comm]
      exact hAe
    obtain ⟨m, _, _⟩ := exists_forcing_move_of_double_angle t 0 (π / 4) (by positivity)
      (by change A = 2 * (π / 4); rw [hAe]; ring)
    exact ⟨m, Or.inl hwin, Or.inl hwin⟩
  · have hwin : WinsNow t (π / 2) := ⟨0, by exact hBe⟩
    obtain ⟨m, _, _⟩ := exists_forcing_move_of_double_angle t 1 (π / 4) (by positivity)
      (by change ∠ (t.points 2) (t.points 1) (t.points 0) = 2 * (π / 4)
          rw [EuclideanGeometry.angle_comm]
          change B = 2 * (π / 4)
          rw [hBe]; ring)
    exact ⟨m, Or.inl hwin, Or.inl hwin⟩
  · have hwin : WinsNow t (π / 2) := ⟨1, by exact hCe⟩
    obtain ⟨m, _, _⟩ := exists_forcing_move_of_double_angle t 2 (π / 4) (by positivity)
      (by change ∠ (t.points 0) (t.points 2) (t.points 1) = 2 * (π / 4)
          rw [EuclideanGeometry.angle_comm]
          change C = 2 * (π / 4)
          rw [hCe]; ring)
    exact ⟨m, Or.inl hwin, Or.inl hwin⟩
  · rcases hacute with h0 | h1 | h2
    · obtain ⟨m, hmT, hmF⟩ := exists_right_angle_forcing_move_of_adjacent_acute
        t 0 (by simpa [B] using h0.2.2.1) (by simpa [A, B] using h0.2.2.2.1)
      exact ⟨m, Or.inr (Or.inl hmT), Or.inr (Or.inl hmF)⟩
    · obtain ⟨m, hmT, hmF⟩ := exists_right_angle_forcing_move_of_adjacent_acute
        t 1 (by simpa [C] using h1.2.2.1)
          (by simpa [B, C, EuclideanGeometry.angle_comm] using h1.2.2.2.1)
      exact ⟨m, Or.inr (Or.inl hmT), Or.inr (Or.inl hmF)⟩
    · obtain ⟨m, hmT, hmF⟩ := exists_right_angle_forcing_move_of_adjacent_acute
        t 2 (by simpa [A, EuclideanGeometry.angle_comm] using h2.2.2.1)
          (by simpa [A, C, EuclideanGeometry.angle_comm] using h2.2.2.2.1)
      exact ⟨m, Or.inr (Or.inl hmT), Or.inr (Or.inl hmF)⟩

private theorem move_half_preserves_universal_angle_avoidance
    (S : AddSubgroup ℝ) (t : Triangle ℝ P) (m : Move t)
    (havoid : ∀ j : Fin 3,
      ∠ (t.points j) (t.points (j + 1)) (t.points (j + 2)) ∉ S)
    (hpi : π ∉ S) :
    (∀ j : Fin 3,
      ∠ ((m.half True).points j) ((m.half True).points (j + 1))
        ((m.half True).points (j + 2)) ∉ S) ∨
    (∀ j : Fin 3,
      ∠ ((m.half False).points j) ((m.half False).points (j + 1))
        ((m.half False).points (j + 2)) ∉ S) := by
  rcases m with ⟨i, p, hp⟩
  have ha : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) ∉ S := by
    rw [EuclideanGeometry.angle_comm]
    convert havoid (i + 2) using 1 <;> fin_cases i <;> rfl
  have hb : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) ∉ S := havoid i
  have hc : ∠ (t.points i) (t.points (i + 2)) (t.points (i + 1)) ∉ S := by
    rw [EuclideanGeometry.angle_comm]
    convert havoid (i + 1) using 1 <;> fin_cases i <;> rfl
  have hi := cevian_cut_preserves_angle_avoidance S t i p hp ⟨ha, hb, hc, hpi⟩
  rcases hi with hleft | hright
  · left
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Move.half, EuclideanGeometry.angle_comm] at hleft ⊢ <;> tauto
  · right
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Move.half, EuclideanGeometry.angle_comm] at hright ⊢ <;> tauto

private theorem mem_answer_iff_pi_mem_zmultiples
    {θ : ℝ} (hθ0 : 0 < θ) (hθπ : θ < π) :
    θ ∈ answer ↔ π ∈ AddSubgroup.zmultiples θ := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨(n : ℤ), ?_⟩
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact mul_div_cancel₀ π (by positivity)
  · intro hπ
    rw [AddSubgroup.mem_zmultiples_iff] at hπ
    obtain ⟨z, hz⟩ := hπ
    rw [zsmul_eq_mul] at hz
    have hzR : 1 < (z : ℝ) := by
      nlinarith [Real.pi_pos]
    have hzI : (1 : ℤ) < z := by exact_mod_cast hzR
    have hz0 : 0 ≤ z := by omega
    have hzcast : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz0
    refine ⟨z.toNat, ?_, ?_⟩
    · omega
    · rw [hzcast]
      apply (eq_div_iff ?_).2
      nlinarith
      exact_mod_cast (show z ≠ 0 by omega)

private theorem winning_angle_mem_answer
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ < π)
    (hwin : ∃ s : Strategy P, s.Winning θ) :
    θ ∈ answer := by
  obtain ⟨t₀, ht₀⟩ := exists_pi_div_three_triangle (V := V) (P := P)
  exact winning_implies_mem_answer_of_pi_div_three_triangle θ hθ0 hθπ t₀ ht₀ hwin

private theorem research_lattice_crossing_reduces_default_coefficient_rank
    (n : ℕ) (θ : ℝ) (hn : 4 ≤ n) (hθ : 0 < θ)
    (hperiod : (n : ℝ) * θ = π) :
    ∃ rank : Triangle ℝ P → ℕ,
      (∀ t, rank t ≤ n - 1) ∧
      ∀ (t : Triangle ℝ P) (i : Fin 3) (k : ℕ),
        rank t = n - 1 → 2 ≤ k → k ≤ n - 2 →
        ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < (k : ℝ) * θ →
        (k : ℝ) * θ <
          ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) +
            ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) →
        ∃ m : Move t,
          rank (m.half True) < rank t ∧ rank (m.half False) < rank t := by
  obtain ⟨rank, hrank⟩ := exists_coefficientRank (P := P) n θ
  refine ⟨rank, (fun t => (hrank t).2.1), ?_⟩
  intro t i k hrt hk2 hkn hB hAB
  have hkle : k ≤ n := by omega
  obtain ⟨m, hmT, hmF⟩ := exists_forcing_move_of_lattice_crossing
    t i n k θ hθ hkle hperiod hB hAB
  refine ⟨m, ?_, ?_⟩
  · have hnk2 : 2 ≤ n - k := by omega
    have hnkn : n - k < n := by omega
    have hle := (hrank (m.half True)).2.2 (n - k) hnk2 hnkn hmT
    omega
  · have hkn' : k < n := by omega
    have hle := (hrank (m.half False)).2.2 k hk2 hkn' hmF
    omega

private theorem winning_pi_div_nat (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Strategy P, s.Winning (π / (n : ℝ)) := by
  by_cases hn2 : n = 2
  · subst n
    simpa using (right_angle_winning_of_cyclic_choice (V := V) (P := P))
  have hn3 : 3 ≤ n := by omega
  let θ : ℝ := π / (n : ℝ)
  have hn0 : (0 : ℝ) < n := by positivity
  have hθ : 0 < θ := div_pos Real.pi_pos hn0
  have hperiod : (n : ℝ) * θ = π := by dsimp [θ]; field_simp
  obtain ⟨rank, hrank⟩ := exists_coefficientRank (P := P) n θ
  apply winning_of_natRank_descent θ rank
  intro t
  let A := ∠ (t.points 1) (t.points 0) (t.points 2)
  let B := ∠ (t.points 0) (t.points 1) (t.points 2)
  let C := ∠ (t.points 1) (t.points 2) (t.points 0)
  have hA : 0 < A := by
    dsimp [A]; apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 1)
      (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)).mp t.independent
  have hB : 0 < B := by
    dsimp [B]; apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 0)
      (i₂ := 1) (i₃ := 2) (by decide) (by decide) (by decide)).mp t.independent
  have hC : 0 < C := by
    dsimp [C]; apply EuclideanGeometry.angle_pos_of_not_collinear
    exact (affineIndependent_iff_not_collinear_of_ne (p := t.points) (i₁ := 1)
      (i₂ := 2) (i₃ := 0) (by decide) (by decide) (by decide)).mp t.independent
  have hsum : A + B + C = (n : ℝ) * θ := by
    simpa [A, B, C, EuclideanGeometry.angle_comm, add_comm, add_left_comm, add_assoc]
      using triangle_angle_sum_as_nat_multiple t n θ (by omega) rfl
  have hsumπ : A + B + C = π := by rw [hsum, hperiod]
  have someMove : Nonempty (Move t) := by
    let p := AffineMap.lineMap (t.points 1) (t.points 2) (1 / 2 : ℝ)
    have h12 : t.points 1 ≠ t.points 2 := t.independent.injective.ne (by decide)
    have hp : Sbtw ℝ (t.points 1) p (t.points 2) := by
      apply sbtw_lineMap_iff.mpr
      exact ⟨h12, by norm_num, by norm_num⟩
    exact ⟨⟨0, p, by simpa [p] using hp⟩⟩
  by_cases ht : WinsNow t θ
  · obtain ⟨m⟩ := someMove
    exact ⟨m, Or.inl ht, Or.inl ht⟩
  rcases (hrank t).1 with hdefault | ⟨r, hr2, hrn, hrt, hrwin⟩
  · have hAw : WinsNow t A := by
      refine ⟨2, ?_⟩
      change ∠ (t.points 2) (t.points 0) (t.points 1) = A
      dsimp [A]
      exact EuclideanGeometry.angle_comm _ _ _
    have hBw : WinsNow t B := by refine ⟨0, ?_⟩; simp [B]
    have hCw : WinsNow t C := by refine ⟨1, ?_⟩; simp [C]
    have hAπ : A < π := by linarith
    have hBπ : B < π := by linarith
    have hCπ : C < π := by linarith
    have not_integer_of_angle (X : ℝ) (hX0 : 0 < X) (hXπ : X < π)
        (hXwin : WinsNow t X) : X / θ ∉ Set.range ((↑) : ℤ → ℝ) := by
      rintro ⟨z, hz⟩
      have hXz : X = (z : ℝ) * θ := (div_eq_iff hθ.ne').mp hz.symm
      have hz0R : 0 < (z : ℝ) := by nlinarith
      have hznR : (z : ℝ) < (n : ℝ) := by nlinarith [hperiod]
      have hz0 : 0 < z := by exact_mod_cast hz0R
      have hzn : z < (n : ℤ) := by exact_mod_cast hznR
      let u := z.toNat
      have huz : (u : ℤ) = z := by simp [u, Int.toNat_of_nonneg (le_of_lt hz0)]
      have hupos : 0 < u := by
        have : (0 : ℤ) < (u : ℤ) := by simpa [huz] using hz0
        exact_mod_cast this
      have hu1 : 1 ≤ u := by omega
      have hun : u < n := by
        exact_mod_cast (show (u : ℤ) < (n : ℤ) by simpa [huz] using hzn)
      have hucast : (u : ℝ) = (z : ℝ) := by exact_mod_cast huz
      have hwu : WinsNow t ((u : ℝ) * θ) := by rw [hucast, ← hXz]; exact hXwin
      by_cases hu : u = 1
      · exact ht (by simpa [hu] using hwu)
      · have hb := (hrank t).2.2 u (by omega) hun hwu
        rw [hdefault] at hb
        omega
    have hnint : ∀ x ∈ ({A / θ, B / θ, C / θ} : Set ℝ),
        x ∉ Set.range ((↑) : ℤ → ℝ) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact not_integer_of_angle A hA hAπ hAw
      · exact not_integer_of_angle B hB hBπ hBw
      · exact not_integer_of_angle C hC hCπ hCw
    have classify (u : ℕ) (hu1 : 1 ≤ u) (hun : u < n) (T : Triangle ℝ P)
        (hw : WinsNow T ((u : ℝ) * θ)) : WinsNow T θ ∨ rank T < rank t := by
      by_cases hu : u = 1
      · left; subst u; simpa using hw
      · right
        have hb := (hrank T).2.2 u (by omega) hun hw
        rw [hdefault]
        omega
    have finish (i : Fin 3) (u : ℕ) (hu1 : 1 ≤ u) (hun : u < n)
        (hlo : ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2)) < (u : ℝ) * θ)
        (hhi : (u : ℝ) * θ < ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) +
          ∠ (t.points i) (t.points (i + 1)) (t.points (i + 2))) :
        ∃ m : Move t,
          (WinsNow t θ ∨ WinsNow (m.half True) θ ∨ rank (m.half True) < rank t) ∧
          (WinsNow t θ ∨ WinsNow (m.half False) θ ∨ rank (m.half False) < rank t) := by
      obtain ⟨m, hmT, hmF⟩ := exists_forcing_move_of_lattice_crossing
        t i n u θ hθ (Nat.le_of_lt hun) hperiod hlo hhi
      refine ⟨m, ?_, ?_⟩
      · rcases classify (n - u) (by omega) (by omega) _ hmT with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rcases classify u hu1 hun _ hmF with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    rcases scaled_integer_crossing hn3 hθ ⟨hA, hB, hC⟩ hsum hnint with
        ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨u, hu1, hun, huk⟩ :=
        crossing_int_to_nat_index hθ hperiod hB (by linarith) hk
      exact finish 0 u hu1 hun (by simpa [B, ← huk] using hk.1)
        (by simpa [A, B, ← huk] using hk.2)
    · obtain ⟨u, hu1, hun, huk⟩ :=
        crossing_int_to_nat_index hθ hperiod hC (by linarith) hk
      exact finish 1 u hu1 hun (by simpa [C, ← huk] using hk.1)
        (by simpa [B, C, ← huk, EuclideanGeometry.angle_comm, add_comm] using hk.2)
    · obtain ⟨u, hu1, hun, huk⟩ :=
        crossing_int_to_nat_index hθ hperiod hA (by linarith) hk
      exact finish 2 u hu1 hun
        (by simpa [A, ← huk, EuclideanGeometry.angle_comm] using hk.1)
        (by simpa [A, C, ← huk, EuclideanGeometry.angle_comm, add_comm] using hk.2)
  · rcases hrwin with ⟨j, hj⟩
    let i : Fin 3 := j + 1
    have hAi : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) =
        (r : ℝ) * θ := by
      fin_cases j <;> simp_all [i, EuclideanGeometry.angle_comm] <;>
        rw [EuclideanGeometry.angle_comm] <;> assumption
    have hAi' : ∠ (t.points (i + 1)) (t.points i) (t.points (i + 2)) =
        (((r - 2 + 2 : ℕ) : ℝ) * θ) := by
      simpa [Nat.sub_add_cancel hr2] using hAi
    obtain ⟨m, hmT, hmF⟩ :=
      exists_forcing_move_of_nat_multiple_decrement t i θ (r - 2) hθ hAi'
    by_cases hrEq : r = 2
    · subst r
      have hmF' : WinsNow (m.half False) θ := by simpa using hmF
      exact ⟨m, Or.inr (Or.inl hmT), Or.inr (Or.inl hmF')⟩
    · have hmF' : WinsNow (m.half False) (((r - 1 : ℕ) : ℝ) * θ) := by
        simpa [show r - 2 + 1 = r - 1 by omega] using hmF
      have hbound := (hrank (m.half False)).2.2 (r - 1) (by omega) (by omega) hmF'
      have hdrop : rank (m.half False) < rank t := by rw [hrt]; omega
      exact ⟨m, Or.inr (Or.inl hmT), Or.inr (Or.inr hdrop)⟩

theorem result : {θ : ℝ | 0 < θ ∧ θ < π ∧ ∃ s : Strategy P, s.Winning θ} = answer := by
  rw [result_exact_obligations]
  exact ⟨fun θ hθ0 hθπ hwin => winning_angle_mem_answer θ hθ0 hθπ hwin,
    winning_pi_div_nat (V := V) (P := P)⟩

end IMO2026P4
