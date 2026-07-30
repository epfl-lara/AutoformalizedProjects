import Mathlib

/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/

open scoped Finset

namespace IMO2026P3

/-- A strategy for Liu Bang. -/
structure Strategy (n : ℕ) where
  /-- The points marked by Liu. -/
  points : Finset (Set.Ioo (0 : ℝ) 1)
  card_points_le : #points ≤ n
  /-- Given the points marked by Xiang, and the indices of starting points of pieces claimed so
  far, the index of the next starting point to claim.  The choice is ignored for previous indices
  that cannot arise (on Liu's turn) from this strategy. -/
  claims : ∀ xiangPoints : Finset (Set.Ioo (0 : ℝ) 1), #xiangPoints ≤ n →
    Disjoint points xiangPoints → ∀ m, m ≤ #points + #xiangPoints →
      ∀ priorClaims : Fin m → Fin (#points + #xiangPoints + 1),
      {i : Fin (#points + #xiangPoints + 1) // i ∉ Set.range priorClaims}

/-- Given the points marked by Xiang and the claims (not necessarily valid given this strategy)
made by Xiang (with arbitrary claims for after all pieces have been claimed), the first `k` claims
made (valid only if `k` does not exceed the number of pieces and Xiang does not claim
already-claimed pieces). -/
def Strategy.play {n : ℕ} (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    (k : ℕ) → Fin k → Fin (#s.points + #xiangPoints + 1)
| 0 => Fin.elim0
| k + 1 => Fin.snoc (s.play xiangPoints card_xiangPoints_le hd xiangClaims k)
    (if Even k then (if h : k ≤ #s.points + #xiangPoints then
      s.claims xiangPoints card_xiangPoints_le hd k h
        (s.play xiangPoints card_xiangPoints_le hd xiangClaims k) else 0) else xiangClaims (k / 2))

/-- Whether the claims made by Xiang when playing a strategy are valid. -/
def Strategy.PlayValid {n : ℕ} (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) : Prop :=
  Function.Injective (s.play xiangPoints card_xiangPoints_le hd xiangClaims
    (#s.points + #xiangPoints + 1))

/-- The sorted endpoints of the pieces from playing a strategy. -/
noncomputable def Strategy.playEnds {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) : List ℝ :=
  ((s.points ∪ xiangPoints).map (Function.Embedding.subtype _) ∪ {0, 1}).sort

/-- The length of a piece from playing a strategy. -/
noncomputable def Strategy.playPieceLength {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (i : Fin (#s.points + #xiangPoints + 1)) : ℝ :=
  (s.playEnds xiangPoints).getD ((i : ℕ) + 1) 0 - (s.playEnds xiangPoints).getD i 0

/-- The length achieved by Liu when playing a strategy against given claims by Xiang. -/
noncomputable def Strategy.playLength {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) : ℝ :=
  ∑ i : Fin (#s.points + #xiangPoints + 1) with Even ((i : Fin _) : ℕ),
    s.playPieceLength xiangPoints (s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1) i)

/-- The answer to be determined. -/
def answer : ℕ+ → ℝ := fun n =>
  (((2 : ℚ) ^ (n : ℕ) / ((2 : ℚ) ^ ((n : ℕ) + 1) - 1) : ℚ) : ℝ)

private lemma play_bijective_of_valid {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    Function.Bijective (s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1)) := by
  exact hvalid.bijective_of_finite

private lemma playEnds_length {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (s.playEnds xiangPoints).length = #s.points + #xiangPoints + 2 := by
  let e : (Set.Ioo (0 : ℝ) 1) ↪ ℝ := Function.Embedding.subtype _
  let u := s.points.map e ∪ xiangPoints.map e
  have hd' : Disjoint (s.points.map e) (xiangPoints.map e) := by
    rw [Finset.disjoint_left] at hd ⊢
    intro z hz₁ hz₂
    rw [Finset.mem_map] at hz₁ hz₂
    rcases hz₁ with ⟨x, hx, rfl⟩
    rcases hz₂ with ⟨y, hy, hxy⟩
    have : x = y := e.injective hxy.symm
    subst y
    exact hd hx hy
  have hcard : #u = #s.points + #xiangPoints := by
    dsimp [u]
    simpa using Finset.card_union_of_disjoint hd'
  have h0 : (0 : ℝ) ∉ u := by
    simp only [u, Finset.mem_union, Finset.mem_map, not_or]
    constructor <;> rintro ⟨x, hx, heq⟩ <;>
      exact (ne_of_gt x.2.1) heq
  have h1 : (1 : ℝ) ∉ u := by
    simp only [u, Finset.mem_union, Finset.mem_map, not_or]
    constructor <;> rintro ⟨x, hx, heq⟩ <;>
      exact (ne_of_lt x.2.2) heq
  rw [Strategy.playEnds, Finset.length_sort]
  change #((s.points ∪ xiangPoints).map e ∪ {0, 1}) = _
  rw [Finset.map_union]
  change #(u ∪ {0, 1}) = _
  have heq : u ∪ {0, 1} = insert 0 (insert 1 u) := by
    ext x
    simp [or_assoc, or_left_comm, or_comm]
  rw [heq]
  simp [h0, h1, hcard]

private lemma playEnds_getD_zero {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) :
    (s.playEnds xiangPoints).getD 0 0 = 0 := by
  let e : (Set.Ioo (0 : ℝ) 1) ↪ ℝ := Function.Embedding.subtype _
  let F : Finset ℝ := (s.points ∪ xiangPoints).map e ∪ {0, 1}
  have h0mem : (0 : ℝ) ∈ F := by simp [F]
  have hne : F.Nonempty := ⟨0, h0mem⟩
  have hmin : F.min' hne = 0 := by
    apply le_antisymm (Finset.min'_le F 0 h0mem)
    apply Finset.le_min' F hne 0
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · rw [Finset.mem_map] at hy
      rcases hy with ⟨x, hx, rfl⟩
      exact le_of_lt x.2.1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl <;> norm_num
  have hlen : 0 < (F.sort).length := by
    simpa [Finset.length_sort] using F.card_pos.mpr hne
  rw [Strategy.playEnds]
  change (F.sort).getD 0 0 = 0
  rw [List.getD_eq_getElem _ _ hlen, Finset.sorted_zero_eq_min']
  exact hmin

private lemma playEnds_getD_last {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (s.playEnds xiangPoints).getD (#s.points + #xiangPoints + 1) 0 = 1 := by
  let e : (Set.Ioo (0 : ℝ) 1) ↪ ℝ := Function.Embedding.subtype _
  let F : Finset ℝ := (s.points ∪ xiangPoints).map e ∪ {0, 1}
  have h1mem : (1 : ℝ) ∈ F := by simp [F]
  have hne : F.Nonempty := ⟨1, h1mem⟩
  have hmax : F.max' hne = 1 := by
    apply le_antisymm
    · apply Finset.max'_le F hne 1
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · rw [Finset.mem_map] at hy
        rcases hy with ⟨x, hx, rfl⟩
        exact le_of_lt x.2.2
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> norm_num
    · exact Finset.le_max' F 1 h1mem
  have hlenEq := playEnds_length s xiangPoints hd
  rw [Strategy.playEnds] at hlenEq
  change (F.sort).length = #s.points + #xiangPoints + 2 at hlenEq
  have hlt : #s.points + #xiangPoints + 1 < (F.sort).length := by omega
  have hidx : #s.points + #xiangPoints + 1 = (F.sort).length - 1 := by omega
  rw [Strategy.playEnds]
  change (F.sort).getD (#s.points + #xiangPoints + 1) 0 = 1
  rw [List.getD_eq_getElem _ _ hlt]
  have hlast := @Finset.sorted_last_eq_max' ℝ _ F (by omega)
  simpa only [hidx, hmax] using hlast

private lemma sum_playPieceLength_eq_one {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i = 1 := by
  let g : ℕ → ℝ := fun i => (s.playEnds xiangPoints).getD i 0
  let f : ℕ → ℝ := fun i => g (i + 1) - g i
  change ∑ i : Fin (#s.points + #xiangPoints + 1), f i = 1
  rw [Fin.sum_univ_eq_sum_range f]
  have htel := Finset.sum_range_sub g (#s.points + #xiangPoints + 1)
  change (∑ i ∈ Finset.range (#s.points + #xiangPoints + 1), f i) = 1
  rw [htel]
  dsimp only [g]
  rw [playEnds_getD_last s xiangPoints hd, playEnds_getD_zero]
  norm_num

private lemma sum_normalized_powers_two (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      (2 : ℚ) ^ i / ((2 : ℚ) ^ (n + 1) - 1) = 1 := by
  have hn : (1 : ℕ) < 2 ^ (n + 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hq : (1 : ℚ) < 2 ^ (n + 1) := by exact_mod_cast hn
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq)
  rw [← Finset.sum_div]
  rw [geom_sum_eq]
  · norm_num [hden]
  · norm_num

private lemma normalized_power_mem_Ioo {n i : ℕ} (hi : i < n) :
    ((2 : ℚ) ^ (i + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1) ∈ Set.Ioo 0 1 := by
  have hi1 : i + 1 < n + 1 := by omega
  have hnum : (1 : ℚ) < 2 ^ (i + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hden : (1 : ℚ) < 2 ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  have hpows : (2 : ℚ) ^ (i + 1) < 2 ^ (n + 1) :=
    pow_lt_pow_right₀ (by norm_num) hi1
  constructor
  · exact div_pos (sub_pos.mpr hnum) (sub_pos.mpr hden)
  · exact (div_lt_one (sub_pos.mpr hden)).mpr (by linarith)

private noncomputable def normalizedPowerPoint (n : ℕ) (i : Fin n) :
    Set.Ioo (0 : ℝ) 1 :=
  ⟨(((2 : ℚ) ^ ((i : ℕ) + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1) : ℚ), by
    have h := normalized_power_mem_Ioo i.isLt
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2⟩

private lemma normalizedPowerPoint_injective (n : ℕ) :
    Function.Injective (normalizedPowerPoint n) := by
  intro i j hij
  have hval := congrArg Subtype.val hij
  change (((((2 : ℚ) ^ ((i : ℕ) + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1) : ℚ) : ℝ)) =
    (((((2 : ℚ) ^ ((j : ℕ) + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1) : ℚ) : ℝ)) at hval
  have hq : ((2 : ℚ) ^ ((i : ℕ) + 1) - 1) / (2 ^ (n + 1) - 1) =
      (2 ^ ((j : ℕ) + 1) - 1) / (2 ^ (n + 1) - 1) := by exact_mod_cast hval
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))
  have hnum := congrArg (fun x : ℚ => x * (2 ^ (n + 1) - 1)) hq
  field_simp [hden] at hnum
  have hp : (2 : ℚ) ^ ((i : ℕ) + 1) = 2 ^ ((j : ℕ) + 1) := by linarith
  have hexp : (i : ℕ) + 1 = (j : ℕ) + 1 :=
    (pow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num : (2 : ℚ) ≠ 1)) hp
  exact Fin.ext (by omega)

private lemma result_of_game_bounds {n : ℕ+}
    (hlower : ∃ s : Strategy n,
      ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
        (card_xiangPoints_le : #xiangPoints ≤ n)
        (hd : Disjoint s.points xiangPoints)
        (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
          answer n ≤ s.playLength xiangPoints card_xiangPoints_le hd xiangClaims)
    (hupper : ∀ s : Strategy n,
      ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
        (card_xiangPoints_le : #xiangPoints ≤ n)
        (hd : Disjoint s.points xiangPoints)
        (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
          s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) :
    IsGreatest {c | ∃ s : Strategy n,
      ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
        (card_xiangPoints_le : #xiangPoints ≤ n)
        (hd : Disjoint s.points xiangPoints)
        (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
          c ≤ s.playLength xiangPoints card_xiangPoints_le hd xiangClaims} (answer n) := by
  constructor
  · exact hlower
  · rintro c ⟨s, hs⟩
    obtain ⟨xiangPoints, card_xiangPoints_le, hd, xiangClaims, hvalid, hlength⟩ := hupper s
    exact (hs xiangPoints card_xiangPoints_le hd xiangClaims hvalid).trans hlength

private lemma sum_playedPieceLength_eq_one {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    ∑ i : Fin (#s.points + #xiangPoints + 1),
      s.playPieceLength xiangPoints
        (s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (#s.points + #xiangPoints + 1) i) = 1 := by
  let p := s.play xiangPoints card_xiangPoints_le hd xiangClaims
    (#s.points + #xiangPoints + 1)
  let e : Equiv (Fin (#s.points + #xiangPoints + 1))
      (Fin (#s.points + #xiangPoints + 1)) :=
    Equiv.ofBijective p (play_bijective_of_valid s xiangPoints card_xiangPoints_le hd
      xiangClaims hvalid)
  change ∑ i, s.playPieceLength xiangPoints (p i) = 1
  change ∑ i, s.playPieceLength xiangPoints (e i) = 1
  rw [e.sum_comp]
  exact sum_playPieceLength_eq_one s xiangPoints hd

private lemma playLength_add_odd_sum_eq_one {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims +
      (∑ i : Fin (#s.points + #xiangPoints + 1) with
        ¬ Even ((i : Fin _) : ℕ),
        s.playPieceLength xiangPoints
          (s.play xiangPoints card_xiangPoints_le hd xiangClaims
            (#s.points + #xiangPoints + 1) i)) = 1 := by
  rw [Strategy.playLength]
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_playedPieceLength_eq_one s xiangPoints card_xiangPoints_le hd xiangClaims hvalid

private lemma playPieceLength_nonneg {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints)
    (i : Fin (#s.points + #xiangPoints + 1)) :
    0 ≤ s.playPieceLength xiangPoints i := by
  have hlen := playEnds_length s xiangPoints hd
  have hi : (i : ℕ) < (s.playEnds xiangPoints).length := by omega
  have hi1 : (i : ℕ) + 1 < (s.playEnds xiangPoints).length := by omega
  rw [Strategy.playPieceLength]
  rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi]
  apply sub_nonneg.mpr
  have hs : (s.playEnds xiangPoints).SortedLE := by
    rw [Strategy.playEnds]
    exact (Finset.sortedLT_sort _).sortedLE
  exact hs.getElem_le_getElem_of_le (Nat.le_add_right (i : ℕ) 1)

private lemma exists_max_fin_not_mem_range {m k : ℕ} (h : m < k) (f : Fin m → Fin k)
    (w : Fin k → ℝ) :
    ∃ i : Fin k, i ∉ Set.range f ∧ ∀ j : Fin k, j ∉ Set.range f → w j ≤ w i := by
  have hex : ∃ i : Fin k, i ∉ Set.range f := by
    by_contra hn
    push Not at hn
    have hf : Function.Surjective f := by
      intro i
      simpa only [Set.mem_range] using hn i
    exact (Nat.not_le_of_lt h) (Fin.le_of_surjective f hf)
  let R := Finset.univ.filter (fun i : Fin k => i ∉ Set.range f)
  have hR : R.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi⟩
  obtain ⟨i, hiR, hi⟩ := Finset.exists_max_image R w hR
  refine ⟨i, ?_, ?_⟩
  · simpa only [R, Finset.mem_filter, Finset.mem_univ, true_and] using hiR
  · intro j hj
    apply hi j
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj

private noncomputable def greedyNormalizedStrategy (n : ℕ) : Strategy n where
  points := Finset.univ.map ⟨normalizedPowerPoint n, normalizedPowerPoint_injective n⟩
  card_points_le := by simp
  claims := by
    intro xiangPoints card_xiangPoints_le hd m hm priorClaims
    let points : Finset (Set.Ioo (0 : ℝ) 1) :=
      Finset.univ.map ⟨normalizedPowerPoint n, normalizedPowerPoint_injective n⟩
    let ends : List ℝ :=
      ((points ∪ xiangPoints).map (Function.Embedding.subtype _) ∪ {0, 1}).sort
    let w : Fin (#points + #xiangPoints + 1) → ℝ := fun i =>
      ends.getD ((i : ℕ) + 1) 0 - ends.getD i 0
    change m ≤ #points + #xiangPoints at hm
    have hm' : m < #points + #xiangPoints + 1 := by omega
    let hex := exists_max_fin_not_mem_range hm' priorClaims w
    let i := Classical.choose hex
    exact ⟨i, (Classical.choose_spec hex).1⟩

private lemma greedyNormalizedStrategy_claims_max (n : ℕ)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint (greedyNormalizedStrategy n).points xiangPoints)
    (m : ℕ) (hm : m ≤ #(greedyNormalizedStrategy n).points + #xiangPoints)
    (priorClaims : Fin m → Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (j : Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (hj : j ∉ Set.range priorClaims) :
    (greedyNormalizedStrategy n).playPieceLength xiangPoints j ≤
      (greedyNormalizedStrategy n).playPieceLength xiangPoints
        ((greedyNormalizedStrategy n).claims xiangPoints card_xiangPoints_le hd m hm
          priorClaims).1 := by
  let points : Finset (Set.Ioo (0 : ℝ) 1) :=
    Finset.univ.map ⟨normalizedPowerPoint n, normalizedPowerPoint_injective n⟩
  let ends : List ℝ :=
    ((points ∪ xiangPoints).map (Function.Embedding.subtype _) ∪ {0, 1}).sort
  let w : Fin (#points + #xiangPoints + 1) → ℝ := fun i =>
    ends.getD ((i : ℕ) + 1) 0 - ends.getD i 0
  change m ≤ #points + #xiangPoints at hm
  have hm' : m < #points + #xiangPoints + 1 := by omega
  have hs := (Classical.choose_spec (exists_max_fin_not_mem_range hm' priorClaims w)).2 j hj
  simpa only [greedyNormalizedStrategy, Strategy.playPieceLength, Strategy.playEnds, points,
    ends, w, id_eq] using hs

private lemma greedyNormalizedStrategy_play_even_max (n : ℕ)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint (greedyNormalizedStrategy n).points xiangPoints)
    (xiangClaims : ℕ → Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (k : ℕ) (hk : k ≤ #(greedyNormalizedStrategy n).points + #xiangPoints)
    (he : Even k)
    (j : Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (hj : j ∉ Set.range ((greedyNormalizedStrategy n).play xiangPoints
      card_xiangPoints_le hd xiangClaims k)) :
    (greedyNormalizedStrategy n).playPieceLength xiangPoints j ≤
      (greedyNormalizedStrategy n).playPieceLength xiangPoints
        ((greedyNormalizedStrategy n).play xiangPoints card_xiangPoints_le hd xiangClaims
          (k + 1) (Fin.last k)) := by
  rw [Strategy.play]
  simp only [Fin.snoc_last, he, ↓reduceIte, dif_pos hk]
  exact greedyNormalizedStrategy_claims_max n xiangPoints card_xiangPoints_le hd k hk
    ((greedyNormalizedStrategy n).play xiangPoints card_xiangPoints_le hd xiangClaims k) j hj

private lemma Strategy.play_prefix {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    {k l : ℕ} (hkl : k ≤ l) (i : Fin k) :
    s.play xiangPoints card_xiangPoints_le hd xiangClaims l
        ⟨i, lt_of_lt_of_le i.isLt hkl⟩ =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims k i := by
  induction hkl with
  | refl => rfl
  | @step l hkl ih =>
      rw [Strategy.play]
      have hi : (⟨i, lt_of_lt_of_le i.isLt (Nat.le.step hkl)⟩ : Fin (l + 1)) =
          Fin.castSucc ⟨i, lt_of_lt_of_le i.isLt hkl⟩ := Fin.ext rfl
      rw [hi, Fin.snoc_castSucc]
      exact ih

private lemma Strategy.play_next_not_mem_range {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (k : ℕ) (hk : k < #s.points + #xiangPoints + 1) :
    s.play xiangPoints card_xiangPoints_le hd xiangClaims (k + 1) (Fin.last k) ∉
      Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims k) := by
  rintro ⟨i, hi⟩
  let M := #s.points + #xiangPoints + 1
  let a : Fin M := ⟨i, lt_of_lt_of_le i.isLt (Nat.le_of_lt hk)⟩
  let b : Fin M := ⟨k, hk⟩
  have ha := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
    (show k ≤ M from Nat.le_of_lt hk) i
  have hb := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
    (show k + 1 ≤ M from hk) (Fin.last k)
  have ha' : s.play xiangPoints card_xiangPoints_le hd xiangClaims M a =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims k i := by
    convert ha
  have hb' : s.play xiangPoints card_xiangPoints_le hd xiangClaims M b =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims (k + 1) (Fin.last k) := by
    dsimp [b]
    convert hb using 1 <;> simp
  have hab : s.play xiangPoints card_xiangPoints_le hd xiangClaims M a =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims M b :=
    ha'.trans (hi.trans hb'.symm)
  have heq : a = b := hvalid hab
  have hval := congrArg Fin.val heq
  change (i : ℕ) = k at hval
  omega

private lemma greedyNormalizedStrategy_consecutive_pair (n : ℕ)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint (greedyNormalizedStrategy n).points xiangPoints)
    (xiangClaims : ℕ → Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (hvalid : (greedyNormalizedStrategy n).PlayValid xiangPoints card_xiangPoints_le hd
      xiangClaims)
    (k : ℕ) (hk : k + 1 < #(greedyNormalizedStrategy n).points + #xiangPoints + 1)
    (he : Even k) :
    (greedyNormalizedStrategy n).playPieceLength xiangPoints
        ((greedyNormalizedStrategy n).play xiangPoints card_xiangPoints_le hd xiangClaims
          (k + 2) (Fin.last (k + 1))) ≤
      (greedyNormalizedStrategy n).playPieceLength xiangPoints
        ((greedyNormalizedStrategy n).play xiangPoints card_xiangPoints_le hd xiangClaims
          (k + 1) (Fin.last k)) := by
  let s := greedyNormalizedStrategy n
  let j := s.play xiangPoints card_xiangPoints_le hd xiangClaims (k + 2) (Fin.last (k + 1))
  have hjbig := s.play_next_not_mem_range xiangPoints card_xiangPoints_le hd xiangClaims
    hvalid (k + 1) hk
  have hj : j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims k) := by
    intro hr
    apply hjbig
    obtain ⟨i, hi⟩ := hr
    refine ⟨Fin.castSucc i, ?_⟩
    have hp := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
      (show k ≤ k + 1 by omega) i
    have hidx : Fin.castSucc i =
        (⟨i, lt_of_lt_of_le i.isLt (show k ≤ k + 1 by omega)⟩ : Fin (k + 1)) := Fin.ext rfl
    rw [hidx, hp]
    simpa only [j, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
  exact greedyNormalizedStrategy_play_even_max n xiangPoints card_xiangPoints_le hd xiangClaims
    k (by omega) he j hj

private lemma greedyNormalizedStrategy_card_points (n : ℕ) :
    #(greedyNormalizedStrategy n).points = n := by
  simp [greedyNormalizedStrategy]

private lemma normalized_power_gap (n i : ℕ) :
    (((2 : ℚ) ^ (i + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1)) -
      (((2 : ℚ) ^ i - 1) / ((2 : ℚ) ^ (n + 1) - 1)) =
        (2 : ℚ) ^ i / ((2 : ℚ) ^ (n + 1) - 1) := by
  rw [pow_succ]
  ring

private lemma normalized_power_final_gap (n : ℕ) :
    (1 : ℚ) - (((2 : ℚ) ^ n - 1) / ((2 : ℚ) ^ (n + 1) - 1)) =
      (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) := by
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))
  field_simp [hden]
  rw [pow_succ]
  ring

private def signedBinary : List ℤ → ℤ
  | [] => 0
  | a :: l => a + 2 * signedBinary l

private lemma signedBinary_ne_zero {l : List ℤ}
    (hcoeff : ∀ a ∈ l, a = -1 ∨ a = 0 ∨ a = 1)
    (hne : ∃ a ∈ l, a ≠ 0) : signedBinary l ≠ 0 := by
  induction l with
  | nil => simp at hne
  | cons a l ih =>
      have ha := hcoeff a (by simp)
      by_cases haz : a = 0
      · have htail : ∃ b ∈ l, b ≠ 0 := by
          obtain ⟨b, hb, hb0⟩ := hne
          simp only [List.mem_cons] at hb
          rcases hb with rfl | hb
          · exact False.elim (hb0 haz)
          · exact ⟨b, hb, hb0⟩
        have hi := ih (fun b hb => hcoeff b (by simp [hb])) htail
        simp [signedBinary, haz, hi]
      · rcases ha with ha | ha | ha
        · rw [ha]
          simp only [signedBinary]
          omega
        · exact False.elim (haz ha)
        · rw [ha]
          simp only [signedBinary]
          omega

private lemma one_le_abs_int_cast {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ |(z : ℝ)| := by
  exact_mod_cast Int.one_le_abs hz

private lemma one_div_le_abs_signedBinary_div {l : List ℤ} {D : ℝ}
    (hcoeff : ∀ a ∈ l, a = -1 ∨ a = 0 ∨ a = 1)
    (hne : ∃ a ∈ l, a ≠ 0) (hD : 0 < D) :
    1 / D ≤ |((signedBinary l : ℤ) : ℝ) / D| := by
  have hnz := signedBinary_ne_zero hcoeff hne
  have hone := one_le_abs_int_cast hnz
  rw [abs_div, abs_of_pos hD]
  exact div_le_div_of_nonneg_right hone hD.le

private def signedCombination : List ℤ → List ℝ → ℝ
  | a :: as, x :: xs => (a : ℝ) * x + signedCombination as xs
  | _, _ => 0

private def absDiffChain : List ℝ → ℝ
  | [] => 0
  | x :: xs => |x - absDiffChain xs|

private lemma signedCombination_map_neg (c : List ℤ) (xs : List ℝ) :
    signedCombination (c.map (- ·)) xs = -signedCombination c xs := by
  induction c generalizing xs with
  | nil => simp [signedCombination]
  | cons a c ih =>
      cases xs with
      | nil => simp [signedCombination]
      | cons x xs =>
          simp only [List.map_cons, signedCombination, Int.cast_neg]
          rw [ih]
          ring

private lemma absDiffChain_exists_signed (xs : List ℝ) :
    ∃ c : List ℤ, c.length = xs.length ∧
      (∀ a ∈ c, a = -1 ∨ a = 1) ∧
      absDiffChain xs = |signedCombination c xs| := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp, by simp [absDiffChain, signedCombination]⟩
  | cons x xs ih =>
      obtain ⟨c, hlen, hc, hchain⟩ := ih
      by_cases hz : 0 ≤ signedCombination c xs
      · refine ⟨1 :: c.map (- ·), by simp [hlen], ?_, ?_⟩
        · intro a ha
          simp only [List.mem_cons, List.mem_map] at ha
          rcases ha with rfl | ⟨b, hb, rfl⟩
          · exact Or.inr rfl
          · rcases hc b hb with rfl | rfl <;> simp
        · rw [absDiffChain, hchain, abs_of_nonneg hz]
          simp only [signedCombination, Int.cast_one, one_mul]
          rw [signedCombination_map_neg]
          ring_nf
      · refine ⟨1 :: c, by simp [hlen], ?_, ?_⟩
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact Or.inr rfl
          · exact hc a ha
        · rw [absDiffChain, hchain, abs_of_neg (lt_of_not_ge hz)]
          simp only [signedCombination, Int.cast_one, one_mul]
          ring_nf

private noncomputable def normalizedBinaryLengths (D : ℝ) : ℕ → List ℝ
  | 0 => []
  | n + 1 => 1 / D :: (normalizedBinaryLengths D n).map (2 * ·)

private lemma normalizedBinaryLengths_length (D : ℝ) (n : ℕ) :
    (normalizedBinaryLengths D n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [normalizedBinaryLengths, ih]

private lemma signedCombination_map_two (c : List ℤ) (xs : List ℝ) :
    signedCombination c (xs.map (2 * ·)) = 2 * signedCombination c xs := by
  induction c generalizing xs with
  | nil => simp [signedCombination]
  | cons a c ih =>
      cases xs with
      | nil => simp [signedCombination]
      | cons x xs =>
          simp only [List.map_cons, signedCombination]
          rw [ih]
          ring

private lemma signedCombination_normalizedBinaryLengths {D : ℝ} {n : ℕ} {c : List ℤ}
    (hlen : c.length = n) :
    signedCombination c (normalizedBinaryLengths D n) = ((signedBinary c : ℤ) : ℝ) / D := by
  induction n generalizing c with
  | zero =>
      have hc : c = [] := List.eq_nil_of_length_eq_zero hlen
      subst c
      simp [signedCombination, signedBinary]
  | succ n ih =>
      obtain ⟨a, c, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < c.length)
      have hlen' : c.length = n := by simpa using hlen
      rw [normalizedBinaryLengths, signedCombination, signedCombination_map_two, ih hlen']
      simp only [signedBinary, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
      ring

private lemma one_div_le_absDiffChain_normalizedBinaryLengths {D : ℝ} {n : ℕ}
    (hD : 0 < D) (hn : 0 < n) :
    1 / D ≤ absDiffChain (normalizedBinaryLengths D n) := by
  obtain ⟨c, hlen, hc, hchain⟩ :=
    absDiffChain_exists_signed (normalizedBinaryLengths D n)
  have hclen : c.length = n := hlen.trans (normalizedBinaryLengths_length D n)
  have hcoeff : ∀ a ∈ c, a = -1 ∨ a = 0 ∨ a = 1 := by
    intro a ha
    rcases hc a ha with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have hne : ∃ a ∈ c, a ≠ 0 := by
    have hcne : c ≠ [] := by
      intro h
      subst c
      simp at hclen
      omega
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil c hcne
    exact ⟨a, ha, by rcases hc a ha with rfl | rfl <;> norm_num⟩
  rw [hchain, signedCombination_normalizedBinaryLengths hclen]
  exact one_div_le_abs_signedBinary_div hcoeff hne hD

private lemma normalized_answer_identity (n : ℕ) :
    (2 : ℚ) ^ n / ((2 : ℚ) ^ (n + 1) - 1) =
      (1 + 1 / ((2 : ℚ) ^ (n + 1) - 1)) / 2 := by
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))
  field_simp [hden]
  rw [pow_succ]
  ring

private lemma answer_eq_half_one_add_inv {n : ℕ+} :
    answer n = (1 + 1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) / 2 := by
  rw [answer]
  exact_mod_cast normalized_answer_identity (n : ℕ)

private lemma answer_le_of_payoff_imbalance {n : ℕ+} {liu xiang : ℝ}
    (hsum : liu + xiang = 1)
    (himb : 1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) ≤ liu - xiang) :
    answer n ≤ liu := by
  rw [answer_eq_half_one_add_inv]
  linarith

private lemma payoff_le_answer_of_imbalance {n : ℕ+} {liu xiang : ℝ}
    (hsum : liu + xiang = 1)
    (himb : liu - xiang ≤ 1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    liu ≤ answer n := by
  rw [answer_eq_half_one_add_inv]
  linarith

private lemma sum_map_two (xs : List ℝ) :
    (xs.map (2 * ·)).sum = 2 * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private lemma sum_normalizedBinaryLengths (D : ℝ) (n : ℕ) :
    (normalizedBinaryLengths D n).sum = ((2 : ℝ) ^ n - 1) / D := by
  induction n with
  | zero => simp [normalizedBinaryLengths]
  | succ n ih =>
      rw [normalizedBinaryLengths]
      simp only [List.sum_cons, sum_map_two, ih]
      rw [pow_succ]
      ring

private lemma sum_normalizedBinaryLengths_denominator (n : ℕ) :
    (normalizedBinaryLengths ((2 : ℝ) ^ (n + 1) - 1) (n + 1)).sum = 1 := by
  rw [sum_normalizedBinaryLengths]
  have hden : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))
  exact div_self hden

private lemma absDiffChain_map_two (xs : List ℝ) :
    absDiffChain (xs.map (2 * ·)) = 2 * absDiffChain xs := by
  induction xs with
  | nil => simp [absDiffChain]
  | cons x xs ih =>
      simp only [List.map_cons, absDiffChain, ih]
      rw [show 2 * x - 2 * absDiffChain xs = 2 * (x - absDiffChain xs) by ring,
        abs_mul]
      norm_num

private lemma absDiffChain_normalizedBinaryLengths {D : ℝ} (hD : 0 < D) {n : ℕ}
    (hn : 0 < n) :
    absDiffChain (normalizedBinaryLengths D n) = 1 / D := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          simp only [normalizedBinaryLengths, List.map_nil, absDiffChain, sub_zero]
          rw [abs_of_pos (one_div_pos.mpr hD)]
      | succ n =>
          rw [normalizedBinaryLengths, absDiffChain, absDiffChain_map_two,
            ih (Nat.succ_pos n)]
          have hi : 0 < 1 / D := one_div_pos.mpr hD
          rw [show 1 / D - 2 * (1 / D) = -(1 / D) by ring, abs_neg, abs_of_pos hi]

private lemma playPieceLength_pos {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints)
    (i : Fin (#s.points + #xiangPoints + 1)) :
    0 < s.playPieceLength xiangPoints i := by
  have hlen := playEnds_length s xiangPoints hd
  have hi : (i : ℕ) < (s.playEnds xiangPoints).length := by omega
  have hi1 : (i : ℕ) + 1 < (s.playEnds xiangPoints).length := by omega
  rw [Strategy.playPieceLength]
  rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi]
  apply sub_pos.mpr
  have hs : (s.playEnds xiangPoints).SortedLT := by
    rw [Strategy.playEnds]
    exact Finset.sortedLT_sort _
  exact hs.getElem_lt_getElem_of_lt (Nat.lt_add_one (i : ℕ))

private noncomputable def physicalPieces {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) : List ℝ :=
  List.ofFn (fun i : Fin (#s.points + #xiangPoints + 1) =>
    s.playPieceLength xiangPoints i)

private lemma physicalPieces_length {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) :
    (physicalPieces s xiangPoints).length = #s.points + #xiangPoints + 1 := by
  simp [physicalPieces]

private lemma physicalPieces_sum {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (physicalPieces s xiangPoints).sum = 1 := by
  rw [physicalPieces, List.sum_ofFn]
  exact sum_playPieceLength_eq_one s xiangPoints hd

private lemma physicalPieces_pos {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    ∀ x ∈ physicalPieces s xiangPoints, 0 < x := by
  intro x hx
  rw [physicalPieces, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact playPieceLength_pos s xiangPoints hd i

private noncomputable def playedPieces {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) : List ℝ :=
  List.ofFn (fun turn : Fin (#s.points + #xiangPoints + 1) =>
    s.playPieceLength xiangPoints
      (s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) turn))

private lemma playedPieces_length {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length =
      #s.points + #xiangPoints + 1 := by
  simp [playedPieces]

private lemma playedPieces_sum_eq_one_of_valid {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).sum = 1 := by
  rw [playedPieces, List.sum_ofFn]
  exact sum_playedPieceLength_eq_one s xiangPoints card_xiangPoints_le hd xiangClaims hvalid

private lemma playedPieces_perm_physicalPieces {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).Perm
      (physicalPieces s xiangPoints) := by
  let p : Equiv.Perm (Fin (#s.points + #xiangPoints + 1)) :=
    Equiv.ofBijective
      (s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1))
      (play_bijective_of_valid s xiangPoints card_xiangPoints_le hd xiangClaims hvalid)
  change (List.ofFn (fun i => s.playPieceLength xiangPoints (p i))).Perm
    (List.ofFn (fun i => s.playPieceLength xiangPoints i))
  exact Equiv.Perm.ofFn_comp_perm p (fun i => s.playPieceLength xiangPoints i)

private noncomputable def Strategy.secondPlayLength {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) : ℝ :=
  ∑ i : Fin (#s.points + #xiangPoints + 1) with ¬Even ((i : Fin _) : ℕ),
    s.playPieceLength xiangPoints
      (s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) i)

private lemma playLength_add_secondPlayLength_eq_one {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims +
      s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims = 1 := by
  exact playLength_add_odd_sum_eq_one s xiangPoints card_xiangPoints_le hd xiangClaims hvalid

private lemma answer_le_playLength_of_imbalance {n : ℕ+}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (himb : 1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) ≤
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
        s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims) :
    answer n ≤ s.playLength xiangPoints card_xiangPoints_le hd xiangClaims := by
  exact answer_le_of_payoff_imbalance
    (playLength_add_secondPlayLength_eq_one s xiangPoints card_xiangPoints_le hd xiangClaims hvalid)
    himb

private lemma playLength_le_answer_of_imbalance {n : ℕ+}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (himb : s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
        s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
      1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  exact payoff_le_answer_of_imbalance
    (playLength_add_secondPlayLength_eq_one s xiangPoints card_xiangPoints_le hd xiangClaims hvalid)
    himb

private def RefinesByBlocks (fine coarse : List ℝ) : Prop :=
  ∃ blocks : List (List ℝ), blocks.length = coarse.length ∧
    blocks.flatten = fine ∧ blocks.map List.sum = coarse ∧
    ∀ b ∈ blocks, b ≠ []

private lemma refinesByBlocks_refl (xs : List ℝ) : RefinesByBlocks xs xs := by
  refine ⟨xs.map ([·]), by simp, ?_, ?_, ?_⟩
  · induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  · induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨x, _, rfl⟩ := hb
    simp

private lemma sum_eq_of_refinesByBlocks {fine coarse : List ℝ}
    (h : RefinesByBlocks fine coarse) : fine.sum = coarse.sum := by
  obtain ⟨blocks, _, rfl, rfl, _⟩ := h
  simp

private lemma length_le_flatten_length_of_ne_nil (blocks : List (List ℝ))
    (hne : ∀ b ∈ blocks, b ≠ []) : blocks.length ≤ blocks.flatten.length := by
  induction blocks with
  | nil => simp
  | cons b blocks ih =>
      have hb : b ≠ [] := hne b (by simp)
      have hbLen : 1 ≤ b.length := by
        cases b with
        | nil => exact False.elim (hb rfl)
        | cons x xs => simp
      have htail : ∀ c ∈ blocks, c ≠ [] := by
        intro c hc
        exact hne c (by simp [hc])
      have hi := ih htail
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

private lemma length_le_of_refinesByBlocks {fine coarse : List ℝ}
    (h : RefinesByBlocks fine coarse) : coarse.length ≤ fine.length := by
  obtain ⟨blocks, hlen, rfl, _, hne⟩ := h
  rw [← hlen]
  exact length_le_flatten_length_of_ne_nil blocks hne

private lemma flatten_length_sub_length_eq_sum (blocks : List (List ℝ))
    (hne : ∀ b ∈ blocks, b ≠ []) :
    blocks.flatten.length - blocks.length =
      (blocks.map (fun b => b.length - 1)).sum := by
  induction blocks with
  | nil => simp
  | cons b blocks ih =>
      have hb : b ≠ [] := hne b (by simp)
      have hbLen : 1 ≤ b.length := by
        cases b with
        | nil => exact False.elim (hb rfl)
        | cons x xs => simp
      have htail : ∀ c ∈ blocks, c ≠ [] := by
        intro c hc
        exact hne c (by simp [hc])
      have hi := ih htail
      have hblocks := length_le_flatten_length_of_ne_nil blocks htail
      simp only [List.flatten_cons, List.length_append, List.length_cons,
        List.map_cons, List.sum_cons]
      omega

private lemma refinement_excess_eq_sum {fine coarse : List ℝ}
    (h : RefinesByBlocks fine coarse) :
    ∃ blocks : List (List ℝ), blocks.length = coarse.length ∧
      blocks.flatten = fine ∧ blocks.map List.sum = coarse ∧
      fine.length - coarse.length =
        (blocks.map (fun b => b.length - 1)).sum := by
  obtain ⟨blocks, hlen, hflat, hsum, hne⟩ := h
  refine ⟨blocks, hlen, hflat, hsum, ?_⟩
  rw [← hflat, ← hlen]
  exact flatten_length_sub_length_eq_sum blocks hne

private def alternatingImbalance : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: xs => x - y + alternatingImbalance xs

private def PairDominates : List ℝ → Prop
  | [] => True
  | [x] => 0 ≤ x
  | x :: y :: xs => y ≤ x ∧ PairDominates xs

private lemma alternatingImbalance_nonneg_of_pairDominates {xs : List ℝ}
    (h : PairDominates xs) : 0 ≤ alternatingImbalance xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingImbalance]
  | singleton x => exact h
  | cons_cons x y xs ih =>
      exact add_nonneg (sub_nonneg.mpr h.1) (ih h.2)

private lemma pairDominates_of_indexed_pairs (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 ≤ x)
    (hpairs : ∀ k, 2 * k + 1 < xs.length →
      xs.getD (2 * k + 1) 0 ≤ xs.getD (2 * k) 0) : PairDominates xs := by
  induction xs using List.twoStepInduction with
  | nil => trivial
  | singleton x =>
      exact hpos x (by simp)
  | cons_cons x y xs ih =>
      constructor
      · simpa using hpairs 0 (by simp)
      · apply ih
        · intro z hz
          exact hpos z (by simp [hz])
        · intro k hk
          have hfull : 2 * (k + 1) + 1 < (x :: y :: xs).length := by
            simp only [List.length_cons]
            omega
          have h := hpairs (k + 1) hfull
          simpa [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
            show 2 * (k + 1) = 2 * k + 2 by omega] using h

private lemma playedPieces_getD {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (k : ℕ) (hk : k < #s.points + #xiangPoints + 1) :
    (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD k 0 =
      s.playPieceLength xiangPoints
        (s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (#s.points + #xiangPoints + 1) ⟨k, hk⟩) := by
  change (List.ofFn (fun turn : Fin (#s.points + #xiangPoints + 1) =>
    s.playPieceLength xiangPoints
      (s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) turn))).getD k 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn]

private lemma greedy_playedPieces_pairDominates (n : ℕ)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint (greedyNormalizedStrategy n).points xiangPoints)
    (xiangClaims : ℕ → Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1))
    (hvalid : (greedyNormalizedStrategy n).PlayValid xiangPoints card_xiangPoints_le hd
      xiangClaims) :
    PairDominates
      (playedPieces (greedyNormalizedStrategy n) xiangPoints card_xiangPoints_le hd
        xiangClaims) := by
  let s := greedyNormalizedStrategy n
  apply pairDominates_of_indexed_pairs
  · intro x hx
    rw [playedPieces, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact playPieceLength_nonneg s xiangPoints hd _
  · intro k hk
    have hk' : 2 * k + 1 < #s.points + #xiangPoints + 1 := by
      simpa [playedPieces_length] using hk
    rw [playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * k + 1) hk',
      playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims
        (2 * k) (by omega)]
    have hcon := greedyNormalizedStrategy_consecutive_pair n xiangPoints
      card_xiangPoints_le hd xiangClaims hvalid (2 * k) hk' (by simp)
    have hp1 := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
      (show 2 * k + 2 ≤ #s.points + #xiangPoints + 1 by omega) (Fin.last (2 * k + 1))
    have hp0 := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
      (show 2 * k + 1 ≤ #s.points + #xiangPoints + 1 by omega) (Fin.last (2 * k))
    rw [← hp1, ← hp0] at hcon
    exact hcon

private def firstPlayerSum : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: _ :: xs => x + firstPlayerSum xs

private def secondPlayerSum : List ℝ → ℝ
  | [] => 0
  | [_] => 0
  | _ :: y :: xs => y + secondPlayerSum xs

private lemma firstPlayerSum_add_secondPlayerSum (xs : List ℝ) :
    firstPlayerSum xs + secondPlayerSum xs = xs.sum := by
  induction xs using List.twoStepInduction with
  | nil => simp [firstPlayerSum, secondPlayerSum]
  | singleton x => simp [firstPlayerSum, secondPlayerSum]
  | cons_cons x y xs ih =>
      simp only [firstPlayerSum, secondPlayerSum, List.sum_cons]
      rw [← ih]
      ring

private lemma alternatingImbalance_eq_playerSums (xs : List ℝ) :
    alternatingImbalance xs = firstPlayerSum xs - secondPlayerSum xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingImbalance, firstPlayerSum, secondPlayerSum]
  | singleton x => simp [alternatingImbalance, firstPlayerSum, secondPlayerSum]
  | cons_cons x y xs ih =>
      simp only [alternatingImbalance, firstPlayerSum, secondPlayerSum]
      rw [ih]
      ring

private lemma alternatingImbalance_add_sum (xs : List ℝ) :
    alternatingImbalance xs + xs.sum = 2 * firstPlayerSum xs := by
  rw [alternatingImbalance_eq_playerSums, ← firstPlayerSum_add_secondPlayerSum]
  ring

private lemma alternatingImbalance_eq_listAlternatingSum (xs : List ℝ) :
    alternatingImbalance xs = xs.alternatingSum := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingImbalance]
  | singleton x => simp [alternatingImbalance]
  | cons_cons x y xs ih =>
      rw [alternatingImbalance, List.alternatingSum_cons_cons', ih]
      ring

private lemma fin_alternating_sum_eq_even_sub_not_even {m : ℕ} (f : Fin m → ℝ) :
    (∑ i : Fin m, (-1 : ℝ) ^ (i : ℕ) * f i) =
      (∑ i : Fin m with Even ((i : Fin _) : ℕ), f i) -
        ∑ i : Fin m with ¬Even ((i : Fin _) : ℕ), f i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin m => Even (i : ℕ))]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [hi.2.neg_one_pow]
    simp
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    have ho : Odd (i : ℕ) := (Nat.even_or_odd (i : ℕ)).resolve_left hi.2
    rw [ho.neg_one_pow]
    ring

private lemma playImbalance_eq_fin_alternating_sum {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
        s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims =
      ∑ i : Fin (#s.points + #xiangPoints + 1),
        (-1 : ℝ) ^ (i : ℕ) *
          s.playPieceLength xiangPoints
            (s.play xiangPoints card_xiangPoints_le hd xiangClaims
              (#s.points + #xiangPoints + 1) i) := by
  rw [fin_alternating_sum_eq_even_sub_not_even]
  rfl

private lemma one_div_le_abs_signedCombination_normalizedBinaryLengths
    {D : ℝ} {k : ℕ} {c : List ℤ}
    (hD : 0 < D) (hlen : c.length = k)
    (hcoeff : ∀ a ∈ c, a = -1 ∨ a = 0 ∨ a = 1)
    (hne : ∃ a ∈ c, a ≠ 0) :
    1 / D ≤ |signedCombination c (normalizedBinaryLengths D k)| := by
  rw [signedCombination_normalizedBinaryLengths hlen]
  exact one_div_le_abs_signedBinary_div hcoeff hne hD

private lemma exists_singleton_block_of_refinement_budget
    {fine coarse : List ℝ} (href : RefinesByBlocks fine coarse)
    (hcoarse : coarse ≠ []) (hbudget : fine.length < 2 * coarse.length) :
    ∃ blocks : List (List ℝ), blocks.length = coarse.length ∧
      blocks.flatten = fine ∧ blocks.map List.sum = coarse ∧
      (∀ b ∈ blocks, b ≠ []) ∧ ∃ b ∈ blocks, b.length = 1 := by
  obtain ⟨blocks, hlen, hflat, hsum, hne⟩ := href
  refine ⟨blocks, hlen, hflat, hsum, hne, ?_⟩
  by_contra h
  push Not at h
  have htwo : ∀ b ∈ blocks, 2 ≤ b.length := by
    intro b hb
    cases b with
    | nil => exact False.elim ((hne [] hb) rfl)
    | cons x xs =>
      cases xs with
      | nil => exact False.elim (h [x] hb (by simp))
      | cons y ys => simp
  have hsumlen : 2 * blocks.length ≤ (blocks.map List.length).sum := by
    calc
      2 * blocks.length = (blocks.map (fun _ => 2)).sum := by simp [Nat.mul_comm]
      _ ≤ (blocks.map List.length).sum := List.sum_le_sum htwo
  have hflatlen : fine.length = (blocks.map List.length).sum := by
    rw [← hflat, List.length_flatten]
  omega

private lemma exists_ternary_opposite_labeling {V E : ℕ} (hEV : E < V)
    (u v : Fin E → Fin V) :
    ∃ c : Fin V → ℤ, (∃ i, c i ≠ 0) ∧
      (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧
      ∀ e, c (u e) + c (v e) = 0 := by
  let L : (Fin V → ℝ) →ₗ[ℝ] (Fin E → ℝ) :=
    { toFun := fun x e => x (u e) + x (v e)
      map_add' := by
        intro x y
        funext e
        simp
        ring
      map_smul' := by
        intro a x
        funext e
        simp
        ring }
  have hdim : Module.finrank ℝ (Fin E → ℝ) <
      Module.finrank ℝ (Fin V → ℝ) := by
    simpa [Module.finrank_pi] using hEV
  have hker : L.ker ≠ ⊥ := L.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨x, hxne⟩ := L.ker.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hker)
  have hxmem : x.val ∈ L.ker := x.property
  have hxne' : x.val ≠ 0 := by
    intro hx
    apply hxne
    apply Subtype.ext
    exact hx
  let c : Fin V → ℤ := fun i =>
    if 0 < x.val i then 1 else if x.val i < 0 then -1 else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    apply hxne'
    funext i
    have hci := hn i
    simp only [c] at hci
    by_cases hp : 0 < x.val i
    · simp [hp] at hci
    · by_cases hm : x.val i < 0
      · simp [hp, hm] at hci
      · exact le_antisymm (not_lt.mp hp) (not_lt.mp hm)
  · intro i
    simp only [c]
    by_cases hp : 0 < x.val i
    · simp [hp]
    · by_cases hm : x.val i < 0
      · simp [hp, hm]
      · simp [hp, hm]
  · intro e
    have he : x.val (u e) + x.val (v e) = 0 := by
      have hzero : L x.val = 0 := hxmem
      exact congrFun hzero e
    simp only [c]
    rcases lt_trichotomy (x.val (u e)) 0 with hu | hu | hu
    · have hv : 0 < x.val (v e) := by linarith
      simp [hu, hv, not_lt_of_ge hu.le]
    · have hv : x.val (v e) = 0 := by linarith
      simp [hu, hv]
    · have hv : x.val (v e) < 0 := by linarith
      have hv' : ¬ 0 < x.val (v e) := not_lt_of_ge hv.le
      simp [hu, hv, hv']

lemma List.Perm.exists_zip_right {α β : Type*} {xs ys : List α}
    (hperm : xs.Perm ys) (labels : List β) (hlen : labels.length = xs.length) :
    ∃ labels' : List β, labels'.length = ys.length ∧
      (xs.zip labels).Perm (ys.zip labels') := by
  induction hperm generalizing labels with
  | nil =>
      have hl : labels = [] := List.eq_nil_of_length_eq_zero hlen
      subst labels
      exact ⟨[], rfl, .refl _⟩
  | cons x h ih =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        obtain ⟨labels', hlenLabels', hp⟩ := ih labels (by simpa using hlen)
        refine ⟨a :: labels', by simp [hlenLabels'], ?_⟩
        simpa using hp.cons (x, a)
  | swap x y l =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        cases labels with
        | nil => simp at hlen
        | cons b labels =>
          refine ⟨b :: a :: labels, by simpa using hlen, ?_⟩
          simpa using (List.Perm.swap (x, b) (y, a) (l.zip labels))
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨labels₁, hlen₁, hp₁⟩ := ih₁ labels hlen
      obtain ⟨labels₂, hlen₂, hp₂⟩ := ih₂ labels₁ hlen₁
      exact ⟨labels₂, hlen₂, hp₁.trans hp₂⟩

private def blockLabelsFrom (k : ℕ) : List (List ℝ) → List ℕ
  | [] => []
  | b :: bs => List.replicate b.length k ++ blockLabelsFrom (k + 1) bs

private lemma blockLabelsFrom_length (k : ℕ) (blocks : List (List ℝ)) :
    (blockLabelsFrom k blocks).length = blocks.flatten.length := by
  induction blocks generalizing k with
  | nil => rfl
  | cons b bs ih => simp [blockLabelsFrom, ih]

private lemma blockLabelsFrom_mem_bounds {k : ℕ} {blocks : List (List ℝ)} {i : ℕ}
    (hi : i ∈ blockLabelsFrom k blocks) : k ≤ i ∧ i < k + blocks.length := by
  induction blocks generalizing k with
  | nil => simp [blockLabelsFrom] at hi
  | cons b bs ih =>
      simp only [blockLabelsFrom, List.mem_append, List.mem_replicate] at hi
      rcases hi with hi | hi
      · rcases hi with ⟨_, rfl⟩
        simp
      · have h := ih hi
        simp only [List.length_cons]
        omega

private def taggedWeightedSum (c : ℕ → ℤ) (zs : List (ℝ × ℕ)) : ℝ :=
  (zs.map fun z => (c z.2 : ℝ) * z.1).sum

private def blockCoefficientsFrom (c : ℕ → ℤ) (k : ℕ) : List (List ℝ) → List ℤ
  | [] => []
  | _ :: bs => c k :: blockCoefficientsFrom c (k + 1) bs

private lemma blockCoefficientsFrom_length (c : ℕ → ℤ) (k : ℕ)
    (blocks : List (List ℝ)) :
    (blockCoefficientsFrom c k blocks).length = blocks.length := by
  induction blocks generalizing k with
  | nil => rfl
  | cons b bs ih => simp [blockCoefficientsFrom, ih]

private lemma taggedWeightedSum_zip_replicate (c : ℕ → ℤ) (k : ℕ) (b : List ℝ) :
    taggedWeightedSum c (b.zip (List.replicate b.length k)) = (c k : ℝ) * b.sum := by
  induction b with
  | nil => simp [taggedWeightedSum]
  | cons x xs ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons,
        taggedWeightedSum, List.map_cons, List.sum_cons]
      change (c k : ℝ) * x +
        taggedWeightedSum c (xs.zip (List.replicate xs.length k)) = _
      rw [ih]
      ring

private lemma taggedWeightedSum_flatten_zip_blockLabelsFrom
    (c : ℕ → ℤ) (k : ℕ) (blocks : List (List ℝ)) :
    taggedWeightedSum c (blocks.flatten.zip (blockLabelsFrom k blocks)) =
      signedCombination (blockCoefficientsFrom c k blocks) (blocks.map List.sum) := by
  induction blocks generalizing k with
  | nil => simp [taggedWeightedSum, blockLabelsFrom, blockCoefficientsFrom,
      signedCombination]
  | cons b bs ih =>
      rw [List.flatten_cons, blockLabelsFrom]
      rw [List.zip_append (by simp)]
      rw [show taggedWeightedSum c
        (b.zip (List.replicate b.length k) ++
          bs.flatten.zip (blockLabelsFrom (k + 1) bs)) =
        taggedWeightedSum c (b.zip (List.replicate b.length k)) +
          taggedWeightedSum c (bs.flatten.zip (blockLabelsFrom (k + 1) bs)) by
            simp [taggedWeightedSum]]
      rw [taggedWeightedSum_zip_replicate, ih]
      simp [blockCoefficientsFrom, signedCombination]

private lemma taggedWeightedSum_eq_of_perm (c : ℕ → ℤ)
    {zs ws : List (ℝ × ℕ)} (h : zs.Perm ws) :
    taggedWeightedSum c zs = taggedWeightedSum c ws := by
  unfold taggedWeightedSum
  exact (h.map fun z => (c z.2 : ℝ) * z.1).sum_eq

lemma List.map_snd_zip_eq_right {α β : Type*}
    (xs : List α) (ls : List β) (hlen : xs.length = ls.length) :
    (xs.zip ls).map Prod.snd = ls := by
  induction xs generalizing ls with
  | nil => simpa using List.eq_nil_of_length_eq_zero hlen.symm
  | cons x xs ih =>
      cases ls with
      | nil => simp at hlen
      | cons a ls =>
        have hlen' : xs.length = ls.length := by
          simp only [List.length_cons] at hlen
          omega
        simp [ih ls hlen']

lemma List.Perm.snd_of_zip {α β : Type*}
    {xs ys : List α} {ls rs : List β}
    (h : (xs.zip ls).Perm (ys.zip rs))
    (hxs : xs.length = ls.length) (hys : ys.length = rs.length) :
    ls.Perm rs := by
  have hm := h.map Prod.snd
  rw [List.map_snd_zip_eq_right xs ls hxs,
    List.map_snd_zip_eq_right ys rs hys] at hm
  exact hm

lemma List.Perm.forall_of_right {α : Type*} {xs ys : List α}
    (h : xs.Perm ys) {p : α → Prop} (hp : ∀ x ∈ xs, p x) :
    ∀ y ∈ ys, p y := by
  intro y hy
  exact hp y (h.mem_iff.mpr hy)

private def LabelPairOpposite (c : ℕ → ℤ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | a :: b :: ls => c a + c b = 0 ∧ LabelPairOpposite c ls

private lemma abs_taggedWeightedSum_le_alternatingImbalance
    (c : ℕ → ℤ) (xs : List ℝ) (labels : List ℕ)
    (hlen : labels.length = xs.length)
    (hc : ∀ i ∈ labels, c i = -1 ∨ c i = 0 ∨ c i = 1)
    (hpos : ∀ x ∈ xs, 0 ≤ x)
    (hdom : PairDominates xs) (hopp : LabelPairOpposite c labels) :
    |taggedWeightedSum c (xs.zip labels)| ≤ alternatingImbalance xs := by
  induction xs using List.twoStepInduction generalizing labels with
  | nil =>
      have hl : labels = [] := List.eq_nil_of_length_eq_zero hlen
      subst labels
      simp [taggedWeightedSum, alternatingImbalance]
  | singleton x =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        have hl : labels = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst labels
        simp only [List.zip_cons_cons, List.zip_nil_right, taggedWeightedSum,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          alternatingImbalance, add_zero]
        have hx : 0 ≤ x := hpos x (by simp)
        rcases hc a (by simp) with ha | ha | ha
        · rw [ha]; norm_num; exact le_of_eq (abs_of_nonneg hx)
        · rw [ha]; simp [hx]
        · rw [ha]; norm_num; exact le_of_eq (abs_of_nonneg hx)
  | cons_cons x y xs ih =>
      cases labels with
      | nil => simp at hlen
      | cons a labels =>
        cases labels with
        | nil => simp at hlen
        | cons b labels =>
          have hlen' : labels.length = xs.length := by
            simp only [List.length_cons] at hlen
            omega
          have hc' : ∀ i ∈ labels, c i = -1 ∨ c i = 0 ∨ c i = 1 := by
            intro i hi
            exact hc i (by simp [hi])
          have hpos' : ∀ z ∈ xs, 0 ≤ z := by
            intro z hz
            exact hpos z (by simp [hz])
          have hi := ih labels hlen' hc' hpos' hdom.2 hopp.2
          have hxy : 0 ≤ x - y := sub_nonneg.mpr hdom.1
          have hp : |(c a : ℝ) * x + (c b : ℝ) * y| ≤ x - y := by
            have hab : c b = -c a := by
              have := hopp.1
              omega
            rw [hab]
            rcases hc a (by simp) with ha | ha | ha
            · rw [ha]
              norm_num
              rw [abs_of_nonpos (by linarith : -x + y ≤ 0)]
              linarith
            · rw [ha]
              simp [hxy]
            · rw [ha]
              norm_num
              rw [abs_of_nonneg (by linarith : 0 ≤ x + -y)]
              linarith
          simp only [List.zip_cons_cons, taggedWeightedSum, List.map_cons,
            List.sum_cons, alternatingImbalance]
          calc
            |(c a : ℝ) * x + ((c b : ℝ) * y +
                taggedWeightedSum c (xs.zip labels))| =
                |((c a : ℝ) * x + (c b : ℝ) * y) +
                  taggedWeightedSum c (xs.zip labels)| := by ring_nf
            _ ≤ |(c a : ℝ) * x + (c b : ℝ) * y| +
                  |taggedWeightedSum c (xs.zip labels)| := abs_add_le _ _
            _ ≤ (x - y) + alternatingImbalance xs := add_le_add hp hi
            _ = x - y + alternatingImbalance xs := rfl

private lemma labelPairOpposite_of_indexed (c : ℕ → ℤ) (labels : List ℕ)
    (hpairs : ∀ k, 2 * k + 1 < labels.length →
      c (labels.getD (2 * k) 0) + c (labels.getD (2 * k + 1) 0) = 0) :
    LabelPairOpposite c labels := by
  induction labels using List.twoStepInduction with
  | nil => trivial
  | singleton a => trivial
  | cons_cons a b labels ih =>
      constructor
      · simpa using hpairs 0 (by simp)
      · apply ih
        intro k hk
        have hfull : 2 * (k + 1) + 1 < (a :: b :: labels).length := by
          simp only [List.length_cons]
          omega
        have h := hpairs (k + 1) hfull
        simpa [show 2 * (k + 1) = 2 * k + 2 by omega,
          show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega] using h

private lemma exists_ternary_pair_labeling {V : ℕ} (labels : List ℕ)
    (hbound : ∀ i ∈ labels, i < V) (hbudget : labels.length < 2 * V) :
    ∃ c : ℕ → ℤ, (∃ i < V, c i ≠ 0) ∧
      (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧
      LabelPairOpposite c labels := by
  let E := labels.length / 2
  have hEV : E < V := by
    dsimp [E]
    omega
  have hget : ∀ j, j < labels.length → labels.getD j 0 < V := by
    intro j hj
    rw [List.getD_eq_getElem labels 0 (by simpa using hj)]
    exact hbound _ (List.getElem_mem ..)
  let u : Fin E → Fin V := fun e =>
    ⟨labels.getD (2 * (e : ℕ)) 0, hget _ (by
      have he := e.isLt
      dsimp [E] at he
      omega)⟩
  let v : Fin E → Fin V := fun e =>
    ⟨labels.getD (2 * (e : ℕ) + 1) 0, hget _ (by
      have he := e.isLt
      dsimp [E] at he
      omega)⟩
  obtain ⟨cf, hnon, hcoeff, hopp⟩ := exists_ternary_opposite_labeling hEV u v
  let c : ℕ → ℤ := fun i => if hi : i < V then cf ⟨i, hi⟩ else 0
  refine ⟨c, ?_, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hnon
    exact ⟨i, i.isLt, by simpa [c, i.isLt] using hi⟩
  · intro i
    by_cases hi : i < V
    · simpa [c, hi] using hcoeff ⟨i, hi⟩
    · simp [c, hi]
  · apply labelPairOpposite_of_indexed
    intro k hk
    have hk0 : 2 * k < labels.length := by omega
    have hb0 := hget (2 * k) hk0
    have hb1 := hget (2 * k + 1) hk
    have hkE : k < E := by
      dsimp [E]
      omega
    have h := hopp ⟨k, hkE⟩
    dsimp only [c]
    rw [dif_pos hb0, dif_pos hb1]
    simpa [u, v] using h

private lemma blockCoefficientsFrom_mem_index (c : ℕ → ℤ) (k : ℕ)
    (blocks : List (List ℝ)) {i : ℕ} (hi : i < blocks.length) :
    c (k + i) ∈ blockCoefficientsFrom c k blocks := by
  induction blocks generalizing k i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => simp [blockCoefficientsFrom]
      | succ i =>
        simp only [List.length_cons] at hi
        have hm := ih (k + 1) (i := i) (by omega)
        simp only [blockCoefficientsFrom, List.mem_cons]
        right
        rw [show k + (i + 1) = k + 1 + i by omega]
        exact hm

private lemma blockCoefficientsFrom_forall (c : ℕ → ℤ) (k : ℕ)
    (blocks : List (List ℝ)) {p : ℤ → Prop} (hc : ∀ i, p (c i)) :
    ∀ a ∈ blockCoefficientsFrom c k blocks, p a := by
  induction blocks generalizing k with
  | nil => simp [blockCoefficientsFrom]
  | cons b bs ih =>
      intro a ha
      simp only [blockCoefficientsFrom, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hc k
      · exact ih (k + 1) a ha

private lemma normalized_refinement_imbalance_lower
    {D : ℝ} {k : ℕ} (blocks : List (List ℝ)) (fine played : List ℝ)
    (hD : 0 < D) (hblocks : blocks.length = k)
    (hflat : blocks.flatten = fine)
    (hsums : blocks.map List.sum = normalizedBinaryLengths D k)
    (hperm : fine.Perm played) (hbudget : played.length < 2 * blocks.length)
    (hpos : ∀ x ∈ played, 0 ≤ x) (hdom : PairDominates played) :
    1 / D ≤ alternatingImbalance played := by
  let sourceLabels := blockLabelsFrom 0 blocks
  have hsourceLen : sourceLabels.length = fine.length := by
    dsimp [sourceLabels]
    rw [blockLabelsFrom_length, hflat]
  obtain ⟨labels, hlabelsLen, hzip⟩ :=
    IMO2026P3.List.Perm.exists_zip_right hperm sourceLabels hsourceLen
  have hlabelPerm : sourceLabels.Perm labels :=
    IMO2026P3.List.Perm.snd_of_zip hzip hsourceLen.symm hlabelsLen.symm
  have hsourceBound : ∀ i ∈ sourceLabels, i < blocks.length := by
    intro i hi
    have hb := blockLabelsFrom_mem_bounds hi
    simpa [sourceLabels] using hb.2
  have hlabelBound : ∀ i ∈ labels, i < blocks.length :=
    IMO2026P3.List.Perm.forall_of_right hlabelPerm hsourceBound
  have hlabelBudget : labels.length < 2 * blocks.length := by
    rw [hlabelsLen]
    exact hbudget
  obtain ⟨c, hnon, hcoeff, hopp⟩ :=
    exists_ternary_pair_labeling labels hlabelBound hlabelBudget
  let coeffs := blockCoefficientsFrom c 0 blocks
  have hcoeffLen : coeffs.length = k := by
    dsimp [coeffs]
    rw [blockCoefficientsFrom_length, hblocks]
  have hcoeffTernary : ∀ a ∈ coeffs, a = -1 ∨ a = 0 ∨ a = 1 := by
    dsimp [coeffs]
    exact blockCoefficientsFrom_forall c 0 blocks hcoeff
  have hcoeffNonzero : ∃ a ∈ coeffs, a ≠ 0 := by
    obtain ⟨i, hi, hci⟩ := hnon
    refine ⟨c i, ?_, hci⟩
    dsimp [coeffs]
    simpa using blockCoefficientsFrom_mem_index c 0 blocks hi
  have hatom : 1 / D ≤ |signedCombination coeffs (normalizedBinaryLengths D k)| :=
    one_div_le_abs_signedCombination_normalizedBinaryLengths hD hcoeffLen
      hcoeffTernary hcoeffNonzero
  have hsourceWeighted :
      taggedWeightedSum c (fine.zip sourceLabels) =
        signedCombination coeffs (normalizedBinaryLengths D k) := by
    calc
      taggedWeightedSum c (fine.zip sourceLabels) =
          taggedWeightedSum c
            (blocks.flatten.zip (blockLabelsFrom 0 blocks)) := by
              simp only [sourceLabels]
              rw [hflat]
      _ = signedCombination (blockCoefficientsFrom c 0 blocks)
          (blocks.map List.sum) :=
            taggedWeightedSum_flatten_zip_blockLabelsFrom c 0 blocks
      _ = signedCombination coeffs (normalizedBinaryLengths D k) := by
            rw [hsums]
  have htargetWeighted :
      taggedWeightedSum c (fine.zip sourceLabels) =
        taggedWeightedSum c (played.zip labels) :=
    taggedWeightedSum_eq_of_perm c hzip
  have hanalytic : |taggedWeightedSum c (played.zip labels)| ≤
      alternatingImbalance played :=
    abs_taggedWeightedSum_le_alternatingImbalance c played labels hlabelsLen
      (by intro i hi; exact hcoeff i) hpos hdom hopp
  calc
    1 / D ≤ |signedCombination coeffs (normalizedBinaryLengths D k)| := hatom
    _ = |taggedWeightedSum c (played.zip labels)| := by
      rw [← hsourceWeighted, htargetWeighted]
    _ ≤ alternatingImbalance played := hanalytic

private lemma idxOf_lt_idxOf_of_sortedLT {xs : List ℝ} (hs : xs.SortedLT)
    {x y : ℝ} (hx : x ∈ xs) (hy : y ∈ xs) (hxy : x < y) :
    xs.idxOf x < xs.idxOf y := by
  have hix : xs.idxOf x < xs.length := List.idxOf_lt_length_iff.mpr hx
  have hiy : xs.idxOf y < xs.length := List.idxOf_lt_length_iff.mpr hy
  by_contra hnot
  have hle : xs.idxOf y ≤ xs.idxOf x := by omega
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hEq : y = x := (List.idxOf_inj hy).mp heq
    linarith
  · have hyxval : xs[xs.idxOf y] < xs[xs.idxOf x] :=
      hs.getElem_lt_getElem_of_lt hlt
    rw [List.getElem_idxOf hiy, List.getElem_idxOf hix] at hyxval
    linarith

private lemma normalized_missing_points_spec (n : ℕ) (s : Strategy n) :
    let grid : Finset (Set.Ioo (0 : ℝ) 1) :=
      Finset.univ.map ⟨normalizedPowerPoint n, normalizedPowerPoint_injective n⟩
    let xiangPoints := grid \ s.points
    xiangPoints.card ≤ n ∧ Disjoint s.points xiangPoints ∧
      ∀ i : Fin n, normalizedPowerPoint n i ∈ s.points ∪ xiangPoints := by
  dsimp only
  constructor
  · calc
      (Finset.univ.map ⟨normalizedPowerPoint n,
        normalizedPowerPoint_injective n⟩ \ s.points).card ≤
          (Finset.univ.map ⟨normalizedPowerPoint n,
            normalizedPowerPoint_injective n⟩).card :=
              Finset.card_le_card (by intro x hx; exact (Finset.mem_sdiff.mp hx).1)
      _ = n := by simp
  constructor
  · rw [Finset.disjoint_left]
    intro x hx hxdiff
    exact (Finset.mem_sdiff.mp hxdiff).2 hx
  · intro i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hi : normalizedPowerPoint n i ∈ s.points
    · exact Or.inl hi
    · exact Or.inr ⟨by simp, hi⟩

private lemma sum_take_adjacent_ofFn {N k : ℕ} (g : ℕ → ℝ) (hk : k ≤ N) :
    ((List.ofFn (fun i : Fin N => g ((i : ℕ) + 1) - g i)).take k).sum =
      g k - g 0 := by
  have hlist :
      (List.ofFn (fun i : Fin N => g ((i : ℕ) + 1) - g i)).take k =
        List.ofFn (fun i : Fin k => g ((i : ℕ) + 1) - g i) := by
    apply List.ext_get
    · simp [hk]
    · intro j hj1 hj2
      simp
  rw [hlist, List.sum_ofFn]
  calc
    (∑ i : Fin k, (g ((i : ℕ) + 1) - g i)) =
        Finset.sum (Finset.range k) (fun i => g (i + 1) - g i) :=
          Fin.sum_univ_eq_sum_range (fun j : ℕ => g (j + 1) - g j) k
    _ = g k - g 0 := by simpa using Finset.sum_range_sub g k

private lemma sum_take_drop_adjacent_ofFn {N a b : ℕ} (g : ℕ → ℝ)
    (hab : a ≤ b) (hb : b ≤ N) :
    (((List.ofFn (fun i : Fin N => g ((i : ℕ) + 1) - g i)).drop a).take
      (b - a)).sum = g b - g a := by
  let xs := List.ofFn (fun i : Fin N => g ((i : ℕ) + 1) - g i)
  have hpa : (xs.take a).sum = g a - g 0 := by
    dsimp only [xs]
    exact sum_take_adjacent_ofFn g (hab.trans hb)
  have hpb : (xs.take b).sum = g b - g 0 := by
    dsimp only [xs]
    exact sum_take_adjacent_ofFn g hb
  have hsplit := List.sum_take_add_sum_drop (xs.take b) a
  have htake : (xs.take b).take a = xs.take a := by
    rw [List.take_take, min_eq_left hab]
  have hdrop : (xs.take b).drop a = (xs.drop a).take (b - a) := by
    rw [List.drop_take]
  rw [htake, hdrop, hpa, hpb] at hsplit
  linarith

private lemma playEnds_sorted_normalized_mem {n k : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcover : ∀ i : Fin k, normalizedPowerPoint k i ∈ s.points ∪ xiangPoints) :
    (s.playEnds xiangPoints).SortedLT ∧
      ∀ i : Fin k, ((normalizedPowerPoint k i : Set.Ioo (0 : ℝ) 1) : ℝ) ∈
        s.playEnds xiangPoints := by
  constructor
  · exact Finset.sortedLT_sort _
  · intro i
    simp only [Strategy.playEnds, Finset.mem_sort, Finset.mem_union,
      Finset.mem_map, Finset.mem_insert, Finset.mem_singleton]
    left
    exact ⟨normalizedPowerPoint k i, Finset.mem_union.mp (hcover i), rfl⟩

private lemma physicalPieces_slice_sum {n a b : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hab : a ≤ b)
    (hb : b ≤ #s.points + #xiangPoints + 1) :
    (((physicalPieces s xiangPoints).drop a).take (b - a)).sum =
      (s.playEnds xiangPoints).getD b 0 -
        (s.playEnds xiangPoints).getD a 0 := by
  simp only [physicalPieces, Strategy.playPieceLength]
  exact sum_take_drop_adjacent_ofFn
    (fun j => (s.playEnds xiangPoints).getD j 0) hab hb

private lemma normalizedPowerPoint_strictMono (n : ℕ) :
    StrictMono (normalizedPowerPoint n) := by
  let f : ℕ → ℚ := fun i =>
    ((2 : ℚ) ^ (i + 1) - 1) / ((2 : ℚ) ^ (n + 1) - 1)
  have hden : 0 < (2 : ℚ) ^ (n + 1) - 1 := by
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hadj : ∀ i, f i < f (i + 1) := by
    intro i
    dsimp only [f]
    have hgap := normalized_power_gap n (i + 1)
    have hpos : 0 < (2 : ℚ) ^ (i + 1) /
        ((2 : ℚ) ^ (n + 1) - 1) := div_pos (by positivity) hden
    linarith
  have hmono : StrictMono f := strictMono_nat_of_lt_succ hadj
  intro i j hij
  have hq : f (i : ℕ) < f (j : ℕ) := hmono hij
  change (((f (i : ℕ) : ℚ) : ℝ)) < (((f (j : ℕ) : ℚ) : ℝ))
  exact_mod_cast hq

private lemma normalizedBoundaryRanks_strictMono {n k : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcover : ∀ i : Fin k, normalizedPowerPoint k i ∈ s.points ∪ xiangPoints) :
    ∀ i j : Fin k, i < j →
      (s.playEnds xiangPoints).idxOf (normalizedPowerPoint k i : ℝ) <
        (s.playEnds xiangPoints).idxOf (normalizedPowerPoint k j : ℝ) := by
  obtain ⟨hsorted, hmem⟩ := playEnds_sorted_normalized_mem s xiangPoints hcover
  intro i j hij
  exact idxOf_lt_idxOf_of_sortedLT hsorted (hmem i) (hmem j)
    (normalizedPowerPoint_strictMono k hij)

private lemma flatten_rankSlices {α : Type*} (xs : List α) (k : ℕ)
    (r : ℕ → ℕ) (hr : Monotone r) (h0 : r 0 = 0)
    (hk : r k = xs.length) :
    (List.ofFn (fun i : Fin k =>
      (xs.drop (r i)).take (r ((i : ℕ) + 1) - r i))).flatten = xs := by
  induction k generalizing xs r with
  | zero =>
      have hx : xs.length = 0 := by simpa [h0] using hk.symm
      have : xs = [] := List.eq_nil_of_length_eq_zero hx
      subst xs
      simp
  | succ k ih =>
      have hr1 : r 1 ≤ r (k + 1) := hr (by omega)
      let ys := xs.drop (r 1)
      let q : ℕ → ℕ := fun i => r (i + 1) - r 1
      have hq : Monotone q := by
        intro a b hab
        dsimp only [q]
        exact Nat.sub_le_sub_right (hr (by omega)) _
      have hq0 : q 0 = 0 := by simp [q]
      have hqk : q k = ys.length := by
        dsimp only [q, ys]
        rw [List.length_drop, ← hk]
      have hrec := ih ys q hq hq0 hqk
      rw [List.ofFn_succ, List.flatten_cons]
      simp only [Fin.val_zero, zero_add, h0, Nat.sub_zero, List.drop_zero]
      have htail :
          List.ofFn (fun i : Fin k =>
            (xs.drop (r (Fin.succ i))).take
              (r ((Fin.succ i : ℕ) + 1) - r (Fin.succ i))) =
          List.ofFn (fun i : Fin k =>
            (ys.drop (q i)).take (q ((i : ℕ) + 1) - q i)) := by
        apply List.ofFn_inj.mpr
        funext i
        dsimp only [ys, q]
        simp only [Fin.val_succ]
        have hri : r 1 ≤ r ((i : ℕ) + 1) := hr (by omega)
        have hadj : r ((i : ℕ) + 1) ≤ r ((i : ℕ) + 2) := hr (by omega)
        have htake :
            (r ((i : ℕ) + 2) - r 1) - (r ((i : ℕ) + 1) - r 1) =
              r ((i : ℕ) + 2) - r ((i : ℕ) + 1) := by omega
        rw [List.drop_drop, Nat.add_sub_of_le hri, htake]
      rw [htail, hrec]
      exact List.take_append_drop (r 1) xs

private lemma alternatingImbalance_ofFn {m : ℕ} (f : Fin m → ℝ) :
    alternatingImbalance (List.ofFn f) =
      ∑ i : Fin m, (-1 : ℝ) ^ (i : ℕ) * f i := by
  rw [alternatingImbalance_eq_listAlternatingSum]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.alternatingSum_cons, Fin.sum_univ_succ]
      rw [ih]
      simp only [Fin.val_succ, pow_succ]
      have hsum :
          (∑ x : Fin m, (-1 : ℝ) ^ (x : ℕ) * -1 * f x.succ) =
            -(∑ x : Fin m, (-1 : ℝ) ^ (x : ℕ) * f x.succ) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hsum]
      norm_num
      rw [sub_eq_add_neg]

private lemma playImbalance_eq_alternatingImbalance {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
        s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims =
      alternatingImbalance
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims) := by
  rw [playImbalance_eq_fin_alternating_sum]
  exact (alternatingImbalance_ofFn (fun i =>
    s.playPieceLength xiangPoints
      (s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) i))).symm

private lemma Strategy.play_congr_of_claims_prefix {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (x y : ℕ → Fin (#s.points + #xiangPoints + 1)) (k : ℕ)
    (hxy : ∀ i, i < k / 2 → x i = y i) :
    s.play xiangPoints card_xiangPoints_le hd x k =
      s.play xiangPoints card_xiangPoints_le hd y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Strategy.play, Strategy.play]
      have hp : s.play xiangPoints card_xiangPoints_le hd x k =
          s.play xiangPoints card_xiangPoints_le hd y k := by
        apply ih
        intro i hi
        exact hxy i (lt_of_lt_of_le hi (Nat.div_le_div_right (by omega)))
      rw [hp]
      congr 1
      split <;> rename_i he
      · split <;> rfl
      · obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.mp he
        have hlt : k / 2 < (k + 1) / 2 := by omega
        exact hxy (k / 2) (by simpa using hlt)

private lemma playEnds_getD_idxOf_normalizedPowerPoint {n k : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcover : ∀ i : Fin k, normalizedPowerPoint k i ∈ s.points ∪ xiangPoints)
    (i : Fin k) :
    (s.playEnds xiangPoints).getD
      ((s.playEnds xiangPoints).idxOf (normalizedPowerPoint k i : ℝ)) 0 =
      (normalizedPowerPoint k i : ℝ) := by
  have hm := (playEnds_sorted_normalized_mem s xiangPoints hcover).2 i
  have hlt : (s.playEnds xiangPoints).idxOf (normalizedPowerPoint k i : ℝ) <
      (s.playEnds xiangPoints).length := List.idxOf_lt_length_iff.mpr hm
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]

private lemma physicalPieces_refines_normalizedBinaryLengths_of_cover
    {n k : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints)
    (hcover : ∀ i : Fin k,
      normalizedPowerPoint k i ∈ s.points ∪ xiangPoints) :
    RefinesByBlocks (physicalPieces s xiangPoints)
      (normalizedBinaryLengths ((2 : ℝ) ^ (k + 1) - 1) (k + 1)) := by
  let D : ℝ := (2 : ℝ) ^ (k + 1) - 1
  let N : ℕ := #s.points + #xiangPoints + 1
  let r : ℕ → ℕ := fun j =>
    if h0 : j = 0 then 0
    else if hj : j ≤ k then
      (s.playEnds xiangPoints).idxOf
        (normalizedPowerPoint k (⟨j - 1, by omega⟩ : Fin k) : ℝ)
    else N
  have hD : 0 < D := by
    dsimp only [D]
    exact sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))
  have hmem := (playEnds_sorted_normalized_mem s xiangPoints hcover).2
  have hr_le_N : ∀ j, r j ≤ N := by
    intro j
    dsimp only [r]
    split
    · omega
    split
    · rename_i hj0 hj
      have hm := hmem (⟨j - 1, by omega⟩ : Fin k)
      have hlt := List.idxOf_lt_length_of_mem hm
      rw [playEnds_length s xiangPoints hd] at hlt
      dsimp only [N]
      omega
    · exact le_rfl
  have hr : Monotone r := by
    intro a b hab
    by_cases ha0 : a = 0
    · subst a
      simp [r]
    by_cases hak : a ≤ k
    · have hb0 : b ≠ 0 := by omega
      by_cases hbk : b ≤ k
      · simp only [r, ha0, hak, hb0, hbk, ↓reduceDIte]
        by_cases hab' : a = b
        · subst b
          rfl
        · exact Nat.le_of_lt
            (normalizedBoundaryRanks_strictMono s xiangPoints hcover
              (⟨a - 1, by omega⟩ : Fin k)
              (⟨b - 1, by omega⟩ : Fin k)
              (show a - 1 < b - 1 by omega))
      · have hbound := hr_le_N a
        simpa [r, ha0, hak, hb0, hbk] using hbound
    · have hb0 : b ≠ 0 := by omega
      have hbk : ¬b ≤ k := by omega
      simp [r, ha0, hak, hb0, hbk]
  have hr0 : r 0 = 0 := by
    simp [r]
  have hrend :
      r (k + 1) = (physicalPieces s xiangPoints).length := by
    rw [physicalPieces_length]
    simp [r, N]
  have hboundary : ∀ j, j ≤ k + 1 →
      (s.playEnds xiangPoints).getD (r j) 0 =
        ((2 : ℝ) ^ j - 1) / D := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      rw [hr0, playEnds_getD_zero]
      norm_num
    by_cases hjk : j ≤ k
    · let q : Fin k := ⟨j - 1, by omega⟩
      rw [show r j =
          (s.playEnds xiangPoints).idxOf
            (normalizedPowerPoint k q : ℝ) by
        simp [r, hj0, hjk, q]]
      rw [playEnds_getD_idxOf_normalizedPowerPoint s xiangPoints hcover q]
      dsimp only [q, normalizedPowerPoint, D]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]
      norm_cast
    · have hjeq : j = k + 1 := by omega
      subst j
      rw [hrend, physicalPieces_length,
        playEnds_getD_last s xiangPoints hd]
      exact (div_self (ne_of_gt hD)).symm
  have hnormalized : ∀ m : ℕ,
      normalizedBinaryLengths D m =
        List.ofFn (fun i : Fin m => (2 : ℝ) ^ (i : ℕ) / D) := by
    intro m
    induction m with
    | zero =>
        simp [normalizedBinaryLengths]
    | succ m ih =>
        rw [normalizedBinaryLengths, ih, List.ofFn_succ]
        congr 1
        rw [List.map_ofFn]
        apply List.ofFn_inj.mpr
        funext i
        simp only [Function.comp_apply, Fin.val_succ]
        rw [pow_succ]
        ring
  let blocks : List (List ℝ) :=
    List.ofFn (fun i : Fin (k + 1) =>
      (physicalPieces s xiangPoints).drop (r i) |>.take
        (r ((i : ℕ) + 1) - r i))
  refine ⟨blocks, ?_, ?_, ?_, ?_⟩
  · simp [blocks, normalizedBinaryLengths_length]
  · dsimp only [blocks]
    exact flatten_rankSlices
      (physicalPieces s xiangPoints) (k + 1) r hr hr0 hrend
  · rw [hnormalized]
    dsimp only [blocks]
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext i
    simp only [Function.comp_apply]
    rw [physicalPieces_slice_sum s xiangPoints
      (hr (Nat.le_add_right (i : ℕ) 1))
      (hr_le_N ((i : ℕ) + 1))]
    rw [hboundary i (by omega),
      hboundary ((i : ℕ) + 1) (by omega)]
    rw [pow_succ]
    ring
  · intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    intro hempty
    have hsumzero :
        ((physicalPieces s xiangPoints).drop (r i) |>.take
          (r ((i : ℕ) + 1) - r i)).sum = 0 := by
      simp [hempty]
    rw [physicalPieces_slice_sum s xiangPoints
      (hr (Nat.le_add_right (i : ℕ) 1))
      (hr_le_N ((i : ℕ) + 1)),
      hboundary i (by omega),
      hboundary ((i : ℕ) + 1) (by omega)] at hsumzero
    have hgap :
        ((2 : ℝ) ^ ((i : ℕ) + 1) - 1) / D -
            ((2 : ℝ) ^ (i : ℕ) - 1) / D =
          (2 : ℝ) ^ (i : ℕ) / D := by
      rw [pow_succ]
      ring
    rw [hgap] at hsumzero
    have hp : 0 < (2 : ℝ) ^ (i : ℕ) / D :=
      div_pos (by positivity) hD
    linarith

private lemma greedy_normalized_strategy_lower_bound_card_arith {n k : ℕ} (hk : k ≤ n) :
    n + k + 1 < 2 * (n + 1) := by
  omega

private lemma greedy_normalized_strategy_lower_bound {n : ℕ+} :
    ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint (greedyNormalizedStrategy n).points xiangPoints)
      (xiangClaims : ℕ → Fin (#(greedyNormalizedStrategy n).points + #xiangPoints + 1)),
      (greedyNormalizedStrategy n).PlayValid xiangPoints card_xiangPoints_le hd
          xiangClaims →
        answer n ≤ (greedyNormalizedStrategy n).playLength xiangPoints
          card_xiangPoints_le hd xiangClaims := by
  intro xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  have hcover : ∀ i : Fin (n : ℕ),
      normalizedPowerPoint (n : ℕ) i ∈
        (greedyNormalizedStrategy n).points ∪ xiangPoints := by
    intro i
    apply Finset.mem_union.mpr
    left
    simp [greedyNormalizedStrategy]
  obtain ⟨blocks, hblocks, hflat, hsums, _⟩ :=
    physicalPieces_refines_normalizedBinaryLengths_of_cover
      (greedyNormalizedStrategy n) xiangPoints hd hcover
  rw [normalizedBinaryLengths_length] at hblocks
  have hbudget :
      (playedPieces (greedyNormalizedStrategy n) xiangPoints
        card_xiangPoints_le hd xiangClaims).length < 2 * blocks.length := by
    rw [playedPieces_length, hblocks, greedyNormalizedStrategy_card_points]
    exact greedy_normalized_strategy_lower_bound_card_arith card_xiangPoints_le
  have hpos : ∀ x ∈ playedPieces (greedyNormalizedStrategy n) xiangPoints
      card_xiangPoints_le hd xiangClaims, 0 ≤ x := by
    intro x hx
    rw [playedPieces, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact playPieceLength_nonneg (greedyNormalizedStrategy n) xiangPoints hd _
  have halt :
      1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) ≤
        alternatingImbalance
          (playedPieces (greedyNormalizedStrategy n) xiangPoints
            card_xiangPoints_le hd xiangClaims) := by
    exact normalized_refinement_imbalance_lower blocks
      (physicalPieces (greedyNormalizedStrategy n) xiangPoints)
      (playedPieces (greedyNormalizedStrategy n) xiangPoints
        card_xiangPoints_le hd xiangClaims)
      (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega))) hblocks hflat hsums
      (playedPieces_perm_physicalPieces (greedyNormalizedStrategy n) xiangPoints
        card_xiangPoints_le hd xiangClaims hvalid).symm
      hbudget hpos
      (greedy_playedPieces_pairDominates n xiangPoints card_xiangPoints_le hd
        xiangClaims hvalid)
  apply answer_le_playLength_of_imbalance
    (greedyNormalizedStrategy n) xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  rw [playImbalance_eq_alternatingImbalance]
  exact halt

private lemma playedPieces_length_lt_twice_block_count {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length <
      2 * (n + 1) := by
  rw [playedPieces_length]
  have card_points_le := s.card_points_le
  omega

private lemma played_length_lt_twice_block_count {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n) :
    #s.points + #xiangPoints + 1 < 2 * (n + 1) := by
  have card_points_le := s.card_points_le
  omega

private noncomputable def counterexampleLiuPoints : Finset (Set.Ioo (0 : ℝ) 1) :=
  {⟨(1 / 5 : ℝ), by norm_num⟩}

private noncomputable def counterexampleRightmostStrategy : Strategy 1 where
  points := counterexampleLiuPoints
  card_points_le := by simp [counterexampleLiuPoints]
  claims := by
    intro xiangPoints card_xiangPoints_le hd m hm priorClaims
    let w : Fin (#counterexampleLiuPoints + #xiangPoints + 1) → ℝ := fun i => i
    have hlt : m < #counterexampleLiuPoints + #xiangPoints + 1 := by omega
    let hex := exists_max_fin_not_mem_range hlt priorClaims w
    exact ⟨Classical.choose hex, (Classical.choose_spec hex).1⟩

private noncomputable def counterexampleXiangPoints : Finset (Set.Ioo (0 : ℝ) 1) :=
  {⟨(1 / 3 : ℝ), by norm_num⟩}

private lemma counterexample_fixture :
    #counterexampleXiangPoints ≤ 1 ∧
    Disjoint counterexampleRightmostStrategy.points counterexampleXiangPoints ∧
    ∀ i : Fin 1, normalizedPowerPoint 1 i ∈
      counterexampleRightmostStrategy.points ∪ counterexampleXiangPoints := by
  constructor
  · simp [counterexampleXiangPoints]
  constructor
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp [counterexampleRightmostStrategy, counterexampleLiuPoints] at hx
    simp [counterexampleXiangPoints] at hy
    norm_num [hx] at hy
  · intro i
    fin_cases i
    rw [Finset.mem_union]
    right
    simp only [counterexampleXiangPoints, Finset.mem_singleton]
    apply Subtype.ext
    norm_num [normalizedPowerPoint]

private lemma counterexample_first_liu_claim_val
    (card_xiangPoints_le : #counterexampleXiangPoints ≤ (1 : ℕ))
    (hd : Disjoint counterexampleRightmostStrategy.points counterexampleXiangPoints)
    (xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points +
      #counterexampleXiangPoints + 1)) :
    ((counterexampleRightmostStrategy.play counterexampleXiangPoints
      card_xiangPoints_le hd xiangClaims 3 0 : ℕ)) = 2 := by
  simp only [Strategy.play, Fin.snoc_zero]
  change ((Classical.choose (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ))) : Fin 3) : ℕ) = 2
  have hmax := (Classical.choose_spec (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ)))).2 (2 : Fin 3) (by simp)
  norm_num at hmax ⊢
  omega

private lemma counterexample_first_liu_piece_length
    (card_xiangPoints_le : #counterexampleXiangPoints ≤ (1 : ℕ))
    (hd : Disjoint counterexampleRightmostStrategy.points counterexampleXiangPoints)
    (xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points +
      #counterexampleXiangPoints + 1)) :
    counterexampleRightmostStrategy.playPieceLength counterexampleXiangPoints
      (counterexampleRightmostStrategy.play counterexampleXiangPoints
        card_xiangPoints_le hd xiangClaims 3 0) = (2 / 3 : ℝ) := by
  have hval := counterexample_first_liu_claim_val card_xiangPoints_le hd xiangClaims
  have hclaim : counterexampleRightmostStrategy.play counterexampleXiangPoints
      card_xiangPoints_le hd xiangClaims 3 0 = (2 : Fin 3) := Fin.ext hval
  rw [hclaim]
  have hsort : ({(0 : ℝ), 1 / 5, 1 / 3, 1} : Finset ℝ).sort (· ≤ ·) =
      [0, 1 / 5, 1 / 3, 1] := by
    norm_num [Finset.sort_insert]
  norm_num [Strategy.playPieceLength, Strategy.playEnds,
    counterexampleRightmostStrategy, counterexampleLiuPoints, counterexampleXiangPoints,
    hsort]

private lemma counterexample_all_claims_exceed_answer
    (card_xiangPoints_le : #counterexampleXiangPoints ≤ (1 : ℕ))
    (hd : Disjoint counterexampleRightmostStrategy.points counterexampleXiangPoints)
    (xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points +
      #counterexampleXiangPoints + 1)) :
    answer 1 < counterexampleRightmostStrategy.playLength counterexampleXiangPoints
      card_xiangPoints_le hd xiangClaims := by
  have hfirst := counterexample_first_liu_piece_length
    card_xiangPoints_le hd xiangClaims
  have hlast : 0 < counterexampleRightmostStrategy.playPieceLength
      counterexampleXiangPoints
      (counterexampleRightmostStrategy.play counterexampleXiangPoints
        card_xiangPoints_le hd xiangClaims 3 (2 : Fin 3)) :=
    playPieceLength_pos counterexampleRightmostStrategy counterexampleXiangPoints hd _
  have hfilter : (Finset.univ.filter fun i : Fin 3 => Even (i : ℕ)) = {0, 2} := by
    decide
  rw [Strategy.playLength]
  change answer 1 < ∑ i : Fin 3 with Even ((i : Fin 3) : ℕ),
    counterexampleRightmostStrategy.playPieceLength counterexampleXiangPoints
      (counterexampleRightmostStrategy.play counterexampleXiangPoints
        card_xiangPoints_le hd xiangClaims 3 i)
  rw [hfilter, Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hfirst]
  norm_num [answer]
  exact hlast

private lemma counterexample_has_no_bounded_valid_claims :
    ¬ ∃ xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points +
        #counterexampleXiangPoints + 1),
      counterexampleRightmostStrategy.PlayValid counterexampleXiangPoints
          counterexample_fixture.1 counterexample_fixture.2.1 xiangClaims ∧
        counterexampleRightmostStrategy.playLength counterexampleXiangPoints
          counterexample_fixture.1 counterexample_fixture.2.1 xiangClaims ≤ answer 1 := by
  rintro ⟨xiangClaims, _, hle⟩
  exact (not_lt_of_ge hle)
    (counterexample_all_claims_exceed_answer
      counterexample_fixture.1 counterexample_fixture.2.1 xiangClaims)

private lemma not_covered_normalized_grid_claims_upper_bound :
    ¬ (∀ {n : ℕ+} (s : Strategy n)
        (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
        (card_xiangPoints_le : #xiangPoints ≤ n)
        (hd : Disjoint s.points xiangPoints),
      (∀ i : Fin n, normalizedPowerPoint n i ∈ s.points ∪ xiangPoints) →
        ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
          s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
            s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) := by
  intro h
  apply counterexample_has_no_bounded_valid_claims
  exact h (n := (1 : ℕ+)) counterexampleRightmostStrategy counterexampleXiangPoints
    counterexample_fixture.1 counterexample_fixture.2.1 counterexample_fixture.2.2



private lemma normalized_grid_residue_valid_claims {n : ℕ+} (s : Strategy n) :
    let grid : Finset (Set.Ioo (0 : ℝ) 1) :=
      Finset.univ.map
        ⟨normalizedPowerPoint n, normalizedPowerPoint_injective n⟩
    let xiangPoints := grid \ s.points
    ∀ (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims := by
  dsimp only
  intro card_xiangPoints_le hd
  let xiangPoints := (Finset.univ.map
    ⟨normalizedPowerPoint (n : ℕ), normalizedPowerPoint_injective (n : ℕ)⟩) \ s.points
  let M := #s.points + #xiangPoints + 1
  have hex : ∀ k, k ≤ M → ∃ x : ℕ → Fin M,
      Function.Injective (s.play xiangPoints card_xiangPoints_le hd x k) := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨fun _ => 0, ?_⟩
        intro i
        exact Fin.elim0 i
    | succ k ih =>
        intro hk
        obtain ⟨x, hx⟩ := ih (by omega)
        by_cases he : Even k
        · refine ⟨x, ?_⟩
          rw [Strategy.play]
          apply Fin.snoc_injective_of_injective hx
          simp only [he, ↓reduceIte]
          rw [dif_pos (by dsimp [M, xiangPoints] at hk ⊢; omega)]
          exact (s.claims xiangPoints card_xiangPoints_le hd k
            (by dsimp [M, xiangPoints] at hk ⊢; omega)
            (s.play xiangPoints card_xiangPoints_le hd x k)).property
        · have hkm : k < M := by omega
          let ey := exists_max_fin_not_mem_range hkm
            (s.play xiangPoints card_xiangPoints_le hd x k) (fun _ => (0 : ℝ))
          let y : Fin M := Classical.choose ey
          have hy : y ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd x k) :=
            (Classical.choose_spec ey).1
          let x' := Function.update x (k / 2) y
          have hprefix : s.play xiangPoints card_xiangPoints_le hd x' k =
              s.play xiangPoints card_xiangPoints_le hd x k := by
            apply s.play_congr_of_claims_prefix
            intro i hi
            dsimp [x']
            rw [Function.update_apply]
            split
            · omega
            · rfl
          refine ⟨x', ?_⟩
          rw [Strategy.play]
          simp only [he, ↓reduceIte]
          rw [hprefix]
          have hxval : x' (k / 2) = y := by simp [x']
          rw [hxval]
          exact Fin.snoc_injective_of_injective hx hy
  obtain ⟨x, hx⟩ := hex M le_rfl
  exact ⟨x, hx⟩

private lemma not_arbitrary_playLength_le_answer :
    ¬ (∀ {n : ℕ+} (s : Strategy n)
        (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
        (card_xiangPoints_le : #xiangPoints ≤ n)
        (hd : Disjoint s.points xiangPoints)
        (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) := by
  intro h
  have hle := h (n := (1 : ℕ+)) counterexampleRightmostStrategy
    counterexampleXiangPoints counterexample_fixture.1 counterexample_fixture.2.1
    (fun _ => 0)
  exact (not_lt_of_ge hle)
    (counterexample_all_claims_exceed_answer
      counterexample_fixture.1 counterexample_fixture.2.1 (fun _ => 0))



private lemma exists_valid_claims_for_points {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims := by
  let M := #s.points + #xiangPoints + 1
  have hex : ∀ k, k ≤ M → ∃ x : ℕ → Fin M,
      Function.Injective (s.play xiangPoints card_xiangPoints_le hd x k) := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨fun _ => 0, ?_⟩
        intro i
        exact Fin.elim0 i
    | succ k ih =>
        intro hk
        obtain ⟨x, hx⟩ := ih (by omega)
        by_cases he : Even k
        · refine ⟨x, ?_⟩
          rw [Strategy.play]
          apply Fin.snoc_injective_of_injective hx
          simp only [he, ↓reduceIte]
          rw [dif_pos (by dsimp [M] at hk ⊢; omega)]
          exact (s.claims xiangPoints card_xiangPoints_le hd k
            (by dsimp [M] at hk ⊢; omega)
            (s.play xiangPoints card_xiangPoints_le hd x k)).property
        · have hkm : k < M := by omega
          let ey := exists_max_fin_not_mem_range hkm
            (s.play xiangPoints card_xiangPoints_le hd x k) (fun _ => (0 : ℝ))
          let y : Fin M := Classical.choose ey
          have hy : y ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd x k) :=
            (Classical.choose_spec ey).1
          let x' := Function.update x (k / 2) y
          have hprefix : s.play xiangPoints card_xiangPoints_le hd x' k =
              s.play xiangPoints card_xiangPoints_le hd x k := by
            apply s.play_congr_of_claims_prefix
            intro i hi
            dsimp [x']
            rw [Function.update_apply]
            split
            · omega
            · rfl
          refine ⟨x', ?_⟩
          rw [Strategy.play]
          simp only [he, ↓reduceIte]
          rw [hprefix]
          have hxval : x' (k / 2) = y := by simp [x']
          rw [hxval]
          exact Fin.snoc_injective_of_injective hx hy
  obtain ⟨x, hx⟩ := hex M le_rfl
  exact ⟨x, hx⟩

private lemma exists_minimal_valid_claims {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        ∀ y : ℕ → Fin (#s.points + #xiangPoints + 1),
          s.PlayValid xiangPoints card_xiangPoints_le hd y →
            s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
              s.playLength xiangPoints card_xiangPoints_le hd y := by
  let M := #s.points + #xiangPoints + 1
  let q := M / 2
  let extend : (Fin q → Fin M) → (ℕ → Fin M) := fun f i =>
    if hi : i < q then f ⟨i, hi⟩ else 0
  have hplay (y : ℕ → Fin M) :
      s.play xiangPoints card_xiangPoints_le hd
          (extend (fun i : Fin q => y i)) M =
        s.play xiangPoints card_xiangPoints_le hd y M := by
    apply s.play_congr_of_claims_prefix
    intro i hi
    simp [extend, q, hi]
  classical
  let candidates : Finset (Fin q → Fin M) := Finset.univ.filter fun f =>
    s.PlayValid xiangPoints card_xiangPoints_le hd (extend f)
  obtain ⟨x, hx⟩ := exists_valid_claims_for_points s xiangPoints card_xiangPoints_le hd
  have hcx : (fun i : Fin q => x i) ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Strategy.PlayValid at hx ⊢
    rw [hplay x]
    exact hx
  obtain ⟨f, hf, hmin⟩ := candidates.exists_min_image
    (fun f => s.playLength xiangPoints card_xiangPoints_le hd (extend f)) ⟨_, hcx⟩
  have hfvalid : s.PlayValid xiangPoints card_xiangPoints_le hd (extend f) := by
    simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using hf
  refine ⟨extend f, hfvalid, ?_⟩
  intro y hy
  let fy : Fin q → Fin M := fun i => y i
  have hfy : fy ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Strategy.PlayValid at hy ⊢
    change Function.Injective
      (s.play xiangPoints card_xiangPoints_le hd
        (extend (fun i : Fin q => y i)) M)
    rw [hplay y]
    exact hy
  have hle := hmin fy hfy
  have hlength : s.playLength xiangPoints card_xiangPoints_le hd (extend fy) =
      s.playLength xiangPoints card_xiangPoints_le hd y := by
    simp only [Strategy.playLength]
    change (∑ i : Fin M with Even ((i : Fin M) : ℕ),
      s.playPieceLength xiangPoints
        (s.play xiangPoints card_xiangPoints_le hd (extend fy) M i)) = _
    change (∑ i : Fin M with Even ((i : Fin M) : ℕ),
      s.playPieceLength xiangPoints
        (s.play xiangPoints card_xiangPoints_le hd
          (extend (fun i : Fin q => y i)) M i)) = _
    rw [hplay y]
  rw [hlength] at hle
  exact hle

private lemma alternatingImbalance_le_of_second_pair_dominates
    {xs : List ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hpairs : ∀ q : ℕ, 2 * q + 1 < xs.length →
      xs.getD (2 * q) 0 ≤ xs.getD (2 * q + 1) 0)
    (hlast : Odd xs.length → xs.getD (xs.length - 1) 0 ≤ δ) :
    alternatingImbalance xs ≤ δ := by
  induction xs using List.twoStepInduction with
  | nil =>
      simpa [alternatingImbalance] using hδ
  | singleton x =>
      have h := hlast (by simp)
      simpa [alternatingImbalance] using h
  | cons_cons x y xs ih =>
      have hxy : x ≤ y := by
        simpa using hpairs 0 (by simp)
      have hpairs' : ∀ q : ℕ, 2 * q + 1 < xs.length →
          xs.getD (2 * q) 0 ≤ xs.getD (2 * q + 1) 0 := by
        intro q hq
        have h := hpairs (q + 1) (by simp only [List.length_cons]; omega)
        simpa [show 2 * (q + 1) = 2 * q + 2 by omega,
          show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega] using h
      have hlast' : Odd xs.length → xs.getD (xs.length - 1) 0 ≤ δ := by
        intro hodd
        have h := hlast (by simpa using hodd.add_even (by simp : Even 2))
        cases xs with
        | nil => simp at hodd
        | cons z zs => simpa using h
      have hi := ih hpairs' hlast'
      simp only [alternatingImbalance]
      linarith

private lemma arbitrary_strategy_upper_bound_iff_board_with_bounded_minimizer
    {n : ℕ+} (s : Strategy n) :
    (∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) ↔
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
      (∀ y : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd y →
          s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
            s.playLength xiangPoints card_xiangPoints_le hd y) ∧
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  constructor
  · rintro ⟨xiangPoints, hcard, hd, x, hxvalid, hxbound⟩
    obtain ⟨xmin, hminvalid, hmin⟩ :=
      exists_minimal_valid_claims s xiangPoints hcard hd
    refine ⟨xiangPoints, hcard, hd, xmin, hminvalid, hmin, ?_⟩
    exact le_trans (hmin x hxvalid) hxbound
  · rintro ⟨xiangPoints, hcard, hd, x, hxvalid, _hmin, hxbound⟩
    exact ⟨xiangPoints, hcard, hd, x, hxvalid, hxbound⟩

private lemma counterexample_rightmost_first_claim_for_four_fifths :
    let xiangPoints : Finset (Set.Ioo (0 : ℝ) 1) := {⟨(4 / 5 : ℝ), by norm_num⟩}
    ∀ (hcard : #xiangPoints ≤ (1 : ℕ))
      (hd : Disjoint counterexampleRightmostStrategy.points xiangPoints)
      (xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points + #xiangPoints + 1)),
    ((counterexampleRightmostStrategy.play xiangPoints hcard hd xiangClaims 3 0 : ℕ)) = 2 := by
  dsimp only
  intro hcard hd xiangClaims
  simp only [Strategy.play, Fin.snoc_zero]
  change ((Classical.choose (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ))) : Fin 3) : ℕ) = 2
  have hmax := (Classical.choose_spec (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ)))).2 (2 : Fin 3) (by simp)
  norm_num at hmax ⊢
  omega

private lemma playLength_le_answer_of_playedPieces_imbalance {n : ℕ+}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (himbalance : alternatingImbalance
      (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims) ≤
        1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  apply playLength_le_answer_of_imbalance s xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  rw [playImbalance_eq_alternatingImbalance]
  exact himbalance

private lemma exists_valid_second_greedy_claims {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
      ∀ q : ℕ, 2 * q + 1 < #s.points + #xiangPoints + 1 →
        ∀ j : Fin (#s.points + #xiangPoints + 1),
          j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims
            (2 * q + 1)) →
          s.playPieceLength xiangPoints j ≤
            s.playPieceLength xiangPoints (xiangClaims q) := by
  let M := #s.points + #xiangPoints + 1
  let Good (k : ℕ) (x : ℕ → Fin M) : Prop :=
    Function.Injective (s.play xiangPoints card_xiangPoints_le hd x k) ∧
    ∀ q : ℕ, 2 * q + 1 < k → ∀ j : Fin M,
      j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd x (2 * q + 1)) →
      s.playPieceLength xiangPoints j ≤ s.playPieceLength xiangPoints (x q)
  have hex : ∀ k, k ≤ M → ∃ x : ℕ → Fin M, Good k x := by
    intro k
    induction k with
    | zero =>
        intro hk
        refine ⟨fun _ => 0, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro q hq
          omega
    | succ k ih =>
        intro hk
        obtain ⟨x, hxinj, hxmax⟩ := ih (by omega)
        by_cases he : Even k
        · obtain ⟨r, hr⟩ := he
          subst k
          refine ⟨x, ?_, ?_⟩
          · rw [Strategy.play]
            apply Fin.snoc_injective_of_injective hxinj
            simp only [Even.add_self r, ↓reduceIte]
            rw [dif_pos (by dsimp [M] at hk ⊢; omega)]
            exact (s.claims xiangPoints card_xiangPoints_le hd (r + r)
              (by dsimp [M] at hk ⊢; omega)
              (s.play xiangPoints card_xiangPoints_le hd x (r + r))).property
          · intro q hq j hj
            apply hxmax q (by omega) j hj
        · have hkm : k < M := by omega
          let ey := exists_max_fin_not_mem_range hkm
            (s.play xiangPoints card_xiangPoints_le hd x k)
            (s.playPieceLength xiangPoints)
          let y : Fin M := Classical.choose ey
          have hyfresh : y ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd x k) :=
            (Classical.choose_spec ey).1
          have hymax : ∀ j : Fin M,
              j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd x k) →
              s.playPieceLength xiangPoints j ≤ s.playPieceLength xiangPoints y :=
            (Classical.choose_spec ey).2
          let x' := Function.update x (k / 2) y
          have hprefix : s.play xiangPoints card_xiangPoints_le hd x' k =
              s.play xiangPoints card_xiangPoints_le hd x k := by
            apply s.play_congr_of_claims_prefix
            intro i hi
            dsimp [x']
            rw [Function.update_apply]
            split
            · omega
            · rfl
          refine ⟨x', ?_, ?_⟩
          · rw [Strategy.play]
            simp only [he, ↓reduceIte]
            rw [hprefix]
            have hxval : x' (k / 2) = y := by simp [x']
            rw [hxval]
            exact Fin.snoc_injective_of_injective hxinj hyfresh
          · intro q hq j hj
            by_cases hqold : 2 * q + 1 < k
            · have hplayq : s.play xiangPoints card_xiangPoints_le hd x' (2 * q + 1) =
                  s.play xiangPoints card_xiangPoints_le hd x (2 * q + 1) := by
                apply s.play_congr_of_claims_prefix
                intro i hi
                dsimp [x']
                rw [Function.update_apply]
                split
                · omega
                · rfl
              have hxq : x' q = x q := by
                dsimp [x']
                rw [Function.update_apply]
                split
                · omega
                · rfl
              rw [hplayq] at hj
              rw [hxq]
              exact hxmax q hqold j hj
            · have hkq : 2 * q + 1 = k := by omega
              have hxq : x' q = y := by
                dsimp [x']
                rw [Function.update_apply]
                split
                · rfl
                · omega
              rw [hkq, hprefix] at hj
              rw [hxq]
              exact hymax j hj
  obtain ⟨x, hxinj, hxmax⟩ := hex M le_rfl
  exact ⟨x, hxinj, by simpa [M] using hxmax⟩

private lemma alternatingImbalance_cons (x : ℝ) (xs : List ℝ) :
    alternatingImbalance (x :: xs) = x - alternatingImbalance xs := by
  induction xs generalizing x with
  | nil => simp [alternatingImbalance]
  | cons y ys ih =>
      rw [show alternatingImbalance (x :: y :: ys) =
        x - y + alternatingImbalance ys by rfl, ih]
      ring

private lemma alternatingImbalance_le_head_of_tail_pairDominates
    {x : ℝ} {xs : List ℝ} (h : PairDominates xs) :
    alternatingImbalance (x :: xs) ≤ x := by
  rw [alternatingImbalance_cons]
  have hn := alternatingImbalance_nonneg_of_pairDominates h
  linarith

private lemma pairDominates_tail_of_indexed_shifted (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 ≤ x)
    (hpairs : ∀ k, 2 * k + 2 < xs.length →
      xs.getD (2 * k + 2) 0 ≤ xs.getD (2 * k + 1) 0) :
    PairDominates xs.tail := by
  cases xs with
  | nil => simp [PairDominates]
  | cons x ys =>
      apply pairDominates_of_indexed_pairs
      · intro y hy
        change y ∈ ys at hy
        apply hpos y
        simp only [List.mem_cons]
        exact Or.inr hy
      · intro k hk
        have h := hpairs k (by simp at hk ⊢; omega)
        simpa [List.getD] using h

private lemma playLength_le_half_one_add_of_second_pair_dominates
    {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hpairs : ∀ q : ℕ,
      2 * q + 1 < (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length →
      (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD (2 * q) 0 ≤
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD (2 * q + 1) 0)
    (hlast : Odd (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length →
      (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD
        ((playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length - 1) 0 ≤ δ) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ (1 + δ) / 2 := by
  have himb : s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
      s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ δ := by
    rw [playImbalance_eq_alternatingImbalance]
    exact alternatingImbalance_le_of_second_pair_dominates hδ hpairs hlast
  have hsum := playLength_add_secondPlayLength_eq_one
    s xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  linarith

private lemma counterexample_rightmost_third_claim_of_valid_middle_reply :
    let xiangPoints : Finset (Set.Ioo (0 : ℝ) 1) := {⟨(4 / 5 : ℝ), by norm_num⟩}
    ∀ (hcard : #xiangPoints ≤ (1 : ℕ))
      (hd : Disjoint counterexampleRightmostStrategy.points xiangPoints)
      (xiangClaims : ℕ → Fin (#counterexampleRightmostStrategy.points + #xiangPoints + 1))
      (hvalid : counterexampleRightmostStrategy.PlayValid xiangPoints hcard hd xiangClaims)
      (hmiddle : xiangClaims 0 = (1 : Fin 3)),
    ((counterexampleRightmostStrategy.play xiangPoints hcard hd xiangClaims 3
      (Fin.last 2) : Fin 3) : ℕ) = 0 := by
  dsimp only
  intro hcard hd xiangClaims hvalid hmiddle
  have htotal : #counterexampleRightmostStrategy.points +
      #({⟨(4 / 5 : ℝ), by norm_num⟩} : Finset (Set.Ioo (0 : ℝ) 1)) + 1 = 3 := by
    simp [counterexampleRightmostStrategy, counterexampleLiuPoints]
  have hfresh := counterexampleRightmostStrategy.play_next_not_mem_range
    (xiangPoints := {⟨(4 / 5 : ℝ), by norm_num⟩}) hcard hd xiangClaims hvalid 2 (by omega)
  have hp0 : ((counterexampleRightmostStrategy.play
      {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 2 0 : Fin 3) : ℕ) = 2 := by
    simp only [Strategy.play, Fin.snoc_zero]
    change ((Classical.choose (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ))) : Fin 3) : ℕ) = 2
    have hmax := (Classical.choose_spec (exists_max_fin_not_mem_range (by omega)
      (Fin.elim0) (fun i : Fin 3 => (i : ℝ)))).2 (2 : Fin 3) (by simp)
    norm_num at hmax ⊢
    omega
  have hp1 : counterexampleRightmostStrategy.play
      {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 2 1 = (1 : Fin 3) := by
    change counterexampleRightmostStrategy.play
      {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 2 (Fin.last 1) = (1 : Fin 3)
    rw [show counterexampleRightmostStrategy.play
      {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 2 =
      Fin.snoc (counterexampleRightmostStrategy.play
        {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 1) (xiangClaims 0) by
        simp [Strategy.play]]
    rw [Fin.snoc_last, hmiddle]
  let x := counterexampleRightmostStrategy.play
      {⟨(4 / 5 : ℝ), by norm_num⟩} hcard hd xiangClaims 3 (Fin.last 2)
  have hne2 : x ≠ (2 : Fin 3) := by
    intro heq
    apply hfresh
    refine ⟨0, ?_⟩
    apply Fin.eq_of_val_eq
    exact hp0.trans (congrArg Fin.val heq).symm
  have hne1 : x ≠ (1 : Fin 3) := by
    intro heq
    apply hfresh
    exact ⟨1, hp1.trans heq.symm⟩
  have hvne2 : (x : ℕ) ≠ 2 := fun h => hne2 (Fin.eq_of_val_eq h)
  have hvne1 : (x : ℕ) ≠ 1 := fun h => hne1 (Fin.eq_of_val_eq h)
  have hbound := x.isLt
  change (x : ℕ) = 0
  omega

private lemma second_greedy_shifted_piece_bounds {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (hmax : ∀ q : ℕ, 2 * q + 1 < #s.points + #xiangPoints + 1 →
      ∀ j : Fin (#s.points + #xiangPoints + 1),
        j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (2 * q + 1)) →
        s.playPieceLength xiangPoints j ≤
          s.playPieceLength xiangPoints (xiangClaims q)) :
    ∀ q : ℕ,
      2 * q + 2 < (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length →
      (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD (2 * q + 2) 0 ≤
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD (2 * q + 1) 0 := by
  intro q hq
  have hlen := playedPieces_length s xiangPoints card_xiangPoints_le hd xiangClaims
  have hq' : 2 * q + 2 < #s.points + #xiangPoints + 1 :=
    calc
      2 * q + 2 < (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length := hq
      _ = #s.points + #xiangPoints + 1 := hlen
  have hstep : 2 * q + 1 < 2 * q + 2 := by omega
  have hqodd : 2 * q + 1 < #s.points + #xiangPoints + 1 := lt_trans hstep hq'
  rw [playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 2) hq',
    playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 1) hqodd]
  have hoddPrefix : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 2) (Fin.last (2 * q + 1)) = xiangClaims q := by
    have hnotEven : ¬ Even (2 * q + 1) := by
      rintro ⟨r, hr⟩
      omega
    rw [Strategy.play]
    simp only [hnotEven, ↓reduceIte]
    rw [Fin.snoc_last]
    congr 1
    omega
  have hleOdd : 2 * q + 2 ≤ #s.points + #xiangPoints + 1 := Nat.le_of_lt hq'
  have hodd : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1) ⟨2 * q + 1, hqodd⟩ = xiangClaims q := by
    have hp := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
      hleOdd (Fin.last (2 * q + 1))
    have hp' : s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) ⟨2 * q + 1, hqodd⟩ =
        s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (2 * q + 2) (Fin.last (2 * q + 1)) := by
      convert hp using 1 <;> simp
    exact hp'.trans hoddPrefix
  rw [hodd]
  apply hmax q hqodd
  have hfresh := s.play_next_not_mem_range xiangPoints card_xiangPoints_le hd xiangClaims
    hvalid (2 * q + 2) hq'
  intro hrange
  apply hfresh
  rcases hrange with ⟨i, hi⟩
  have hilt : i.val < 2 * q + 2 := lt_trans i.isLt hstep
  let i' : Fin (2 * q + 2) := ⟨i.val, hilt⟩
  refine ⟨i', ?_⟩
  have hsmallLe : 2 * q + 1 ≤ 2 * q + 2 := Nat.le_of_lt hstep
  have hp_i := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims hsmallLe i
  have hp_i' : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 2) i' =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims (2 * q + 1) i := by
    exact hp_i
  have hleLast : 2 * q + 3 ≤ #s.points + #xiangPoints + 1 := by
    exact Nat.succ_le_of_lt hq'
  have hp_last := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
    hleLast (Fin.last (2 * q + 2))
  have hj : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1) ⟨2 * q + 2, hq'⟩ =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (2 * q + 3) (Fin.last (2 * q + 2)) := by
    convert hp_last using 1 <;> simp
  exact hp_i'.trans (hi.trans hj)

private lemma alternatingImbalance_le_getD_zero_of_shifted_pairs
    (xs : List ℝ)
    (hpos : ∀ x ∈ xs, 0 ≤ x)
    (hpairs : ∀ k, 2 * k + 2 < xs.length →
      xs.getD (2 * k + 2) 0 ≤ xs.getD (2 * k + 1) 0) :
    alternatingImbalance xs ≤ xs.getD 0 0 := by
  cases xs with
  | nil => simp [alternatingImbalance]
  | cons x ys =>
      have ht : PairDominates (x :: ys).tail :=
        pairDominates_tail_of_indexed_shifted (x :: ys) hpos hpairs
      have h := alternatingImbalance_le_head_of_tail_pairDominates
        (x := x) (xs := ys) (by simpa using ht)
      simpa using h

private lemma sorted_firstPlayerSum_eq_half_one_add
    {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) =
      (1 + alternatingImbalance
        ((physicalPieces s xiangPoints).mergeSort (· ≥ ·))) / 2 := by
  have hp := List.mergeSort_perm (physicalPieces s xiangPoints) (· ≥ ·)
  have hsum :
      ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)).sum = 1 := by
    rw [hp.sum_eq]
    exact physicalPieces_sum s xiangPoints hd
  have halt :=
    alternatingImbalance_add_sum
      ((physicalPieces s xiangPoints).mergeSort (· ≥ ·))
  rw [hsum] at halt
  linarith

private lemma threshold_transform
    {a : ℚ} (ha : 2 * a - 1 ≠ 0) (ha' : 4 * a - 1 ≠ 0) :
    (2 * a) / (4 * a - 1) =
      (2 * (a / (2 * a - 1))) / (2 * (a / (2 * a - 1)) + 1) := by
  field_simp
  ring

private lemma not_arbitrary_strategy_upper_bound_iff_all_valid_exceed
    {n : ℕ+} (s : Strategy n) :
    (¬ ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) ↔
    ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
        answer n < s.playLength xiangPoints card_xiangPoints_le hd xiangClaims := by
  simp only [not_exists, not_and, not_le]

private lemma exists_exceeding_minimal_valid_claims_of_all_valid_exceed
    {n : ℕ+} (s : Strategy n)
    (hall : ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
        answer n <
          s.playLength xiangPoints card_xiangPoints_le hd xiangClaims)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
      (∀ y : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd y →
          s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
            s.playLength xiangPoints card_xiangPoints_le hd y) ∧
      answer n <
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims := by
  obtain ⟨xmin, hvalid, hmin⟩ :=
    exists_minimal_valid_claims s xiangPoints card_xiangPoints_le hd
  exact ⟨xmin, hvalid, hmin,
    hall xiangPoints card_xiangPoints_le hd xmin hvalid⟩

private lemma arbitrary_strategy_upper_bound_of_static_sorted_board
    {n : ℕ+} (s : Strategy n)
    (hmajor : ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
      (∀ q : ℕ, 2 * q + 1 < #s.points + #xiangPoints + 1 →
        ∀ j : Fin (#s.points + #xiangPoints + 1),
          j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims
            (2 * q + 1)) →
          s.playPieceLength xiangPoints j ≤
            s.playPieceLength xiangPoints (xiangClaims q)) →
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
        firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)))
    (hboard : ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤ answer n) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  obtain ⟨xiangPoints, hcard, hd, hsorted⟩ := hboard
  obtain ⟨xiangClaims, hvalid, hmax⟩ :=
    exists_valid_second_greedy_claims s xiangPoints hcard hd
  refine ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, ?_⟩
  exact le_trans (hmajor xiangPoints hcard hd xiangClaims hvalid hmax) hsorted

private lemma firstPlayerSum_flatMap_duplicate (xs : List ℝ) :
    firstPlayerSum (xs.flatMap fun x => [x, x]) = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [firstPlayerSum, ih]

private lemma firstPlayerSum_cons_flatMap_duplicate (δ : ℝ) (xs : List ℝ) :
    firstPlayerSum (δ :: xs.flatMap fun x => [x, x]) = δ + xs.sum := by
  induction xs generalizing δ with
  | nil => simp [firstPlayerSum]
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.sum_cons]
      change δ + firstPlayerSum (x :: xs.flatMap fun y => [y, y]) = δ + (x + xs.sum)
      rw [ih]

private lemma sum_flatMap_duplicate (xs : List ℝ) :
    (xs.flatMap fun x => [x, x]).sum = 2 * xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

private lemma firstPlayerSum_cons_flatMap_duplicate_eq_half
    (δ : ℝ) (xs : List ℝ)
    (hsum : (δ :: xs.flatMap fun x => [x, x]).sum = 1) :
    firstPlayerSum (δ :: xs.flatMap fun x => [x, x]) = (1 + δ) / 2 := by
  rw [firstPlayerSum_cons_flatMap_duplicate]
  simp only [List.sum_cons] at hsum
  rw [sum_flatMap_duplicate] at hsum
  linarith

private lemma second_greedy_all_later_piece_bounds {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (hmax : ∀ q : ℕ, 2 * q + 1 < #s.points + #xiangPoints + 1 →
      ∀ j : Fin (#s.points + #xiangPoints + 1),
        j ∉ Set.range (s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (2 * q + 1)) →
        s.playPieceLength xiangPoints j ≤
          s.playPieceLength xiangPoints (xiangClaims q)) :
    ∀ q : ℕ, 2 * q + 1 <
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length →
      ∀ k : ℕ, 2 * q + 1 < k →
        k < (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).length →
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD k 0 ≤
          (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD
            (2 * q + 1) 0 := by
  intro q hq k hqk hk
  have hlen := playedPieces_length s xiangPoints card_xiangPoints_le hd xiangClaims
  have hq' : 2 * q + 1 < #s.points + #xiangPoints + 1 := by
    rw [← hlen]
    exact hq
  have hk' : k < #s.points + #xiangPoints + 1 := by
    rw [← hlen]
    exact hk
  rw [playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims k hk',
    playedPieces_getD s xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 1) hq']
  have hoddPrefix : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (2 * q + 2) (Fin.last (2 * q + 1)) = xiangClaims q := by
    have hnotEven : ¬ Even (2 * q + 1) := by
      rintro ⟨r, hr⟩
      omega
    rw [Strategy.play]
    simp only [hnotEven, ↓reduceIte]
    rw [Fin.snoc_last]
    congr 1
    omega
  have hodd : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1) ⟨2 * q + 1, hq'⟩ = xiangClaims q := by
    have hp := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
      (show 2 * q + 2 ≤ #s.points + #xiangPoints + 1 by omega)
      (Fin.last (2 * q + 1))
    have hp' : s.play xiangPoints card_xiangPoints_le hd xiangClaims
        (#s.points + #xiangPoints + 1) ⟨2 * q + 1, hq'⟩ =
        s.play xiangPoints card_xiangPoints_le hd xiangClaims
          (2 * q + 2) (Fin.last (2 * q + 1)) := by
      convert hp using 1 <;> simp
    exact hp'.trans hoddPrefix
  rw [hodd]
  apply hmax q hq'
  have hfresh := s.play_next_not_mem_range xiangPoints card_xiangPoints_le hd xiangClaims
    hvalid k hk'
  intro hrange
  apply hfresh
  rcases hrange with ⟨i, hi⟩
  let i' : Fin k := ⟨i.val, lt_trans i.isLt hqk⟩
  refine ⟨i', ?_⟩
  have hp_i := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
    (Nat.le_of_lt hqk) i
  have hp_i' : s.play xiangPoints card_xiangPoints_le hd xiangClaims k i' =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims (2 * q + 1) i := by
    exact hp_i
  have hp_last := s.play_prefix xiangPoints card_xiangPoints_le hd xiangClaims
    (show k + 1 ≤ #s.points + #xiangPoints + 1 by omega) (Fin.last k)
  have hj : s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1) ⟨k, hk'⟩ =
      s.play xiangPoints card_xiangPoints_le hd xiangClaims (k + 1) (Fin.last k) := by
    convert hp_last using 1 <;> simp
  exact hp_i'.trans (hi.trans hj)

private lemma static_sorted_board_bound_iff_imbalance
    {n : ℕ+} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤ answer n ↔
      alternatingImbalance ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
        1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) := by
  rw [sorted_firstPlayerSum_eq_half_one_add s xiangPoints hd,
    answer_eq_half_one_add_inv]
  constructor <;> intro h <;> linarith

private lemma not_arbitrary_strategy_upper_bound_iff_all_boards_minimum_exceeds
    {n : ℕ+} (s : Strategy n) :
    (¬ ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n) ↔
    ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        (∀ y : ℕ → Fin (#s.points + #xiangPoints + 1),
          s.PlayValid xiangPoints card_xiangPoints_le hd y →
            s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
              s.playLength xiangPoints card_xiangPoints_le hd y) ∧
        answer n <
          s.playLength xiangPoints card_xiangPoints_le hd xiangClaims := by
  constructor
  · intro h xiangPoints hcard hd
    have hall :=
      (not_arbitrary_strategy_upper_bound_iff_all_valid_exceed s).mp h
    exact exists_exceeding_minimal_valid_claims_of_all_valid_exceed
      s hall xiangPoints hcard hd
  · intro h
    rw [not_arbitrary_strategy_upper_bound_iff_all_valid_exceed]
    intro xiangPoints hcard hd y hy
    obtain ⟨xmin, hvalid, hmin, hgt⟩ := h xiangPoints hcard hd
    exact lt_of_lt_of_le hgt (hmin y hy)

private lemma arbitrary_strategy_upper_bound_of_bounded_first_piece
    {n : ℕ+} (s : Strategy n)
    (hboard : ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      ∀ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
        (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD 0 0 ≤
          1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  obtain ⟨xiangPoints, hcard, hd, hfirst⟩ := hboard
  obtain ⟨xiangClaims, hvalid, hmax⟩ :=
    exists_valid_second_greedy_claims s xiangPoints hcard hd
  refine ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, ?_⟩
  apply playLength_le_answer_of_playedPieces_imbalance
    s xiangPoints hcard hd xiangClaims hvalid
  let xs := playedPieces s xiangPoints hcard hd xiangClaims
  have hpos : ∀ x ∈ xs, 0 ≤ x := by
    intro x hx
    dsimp [xs, playedPieces] at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact playPieceLength_nonneg s xiangPoints hd _
  have hpairs : ∀ q, 2 * q + 2 < xs.length →
      xs.getD (2 * q + 2) 0 ≤ xs.getD (2 * q + 1) 0 := by
    intro q hq
    exact second_greedy_shifted_piece_bounds
      s xiangPoints hcard hd xiangClaims hvalid hmax q hq
  have ht : PairDominates xs.tail :=
    pairDominates_tail_of_indexed_shifted xs hpos hpairs
  cases hxs : xs with
  | nil =>
      have hlen := playedPieces_length s xiangPoints hcard hd xiangClaims
      dsimp [xs] at hxs
      rw [hxs] at hlen
      simp at hlen
  | cons x ys =>
      have himb := alternatingImbalance_le_head_of_tail_pairDominates
        (x := x) (xs := ys) (by simpa [hxs] using ht)
      have hb := hfirst xiangClaims hvalid
      dsimp [xs] at hxs
      rw [hxs] at hb ⊢
      simpa using le_trans himb hb

private lemma exists_second_greedy_playLength_le_half_one_add_first_piece
    {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
        (1 + (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims).getD 0 0) / 2 := by
  obtain ⟨xiangClaims, hvalid, hmax⟩ :=
    exists_valid_second_greedy_claims s xiangPoints card_xiangPoints_le hd
  refine ⟨xiangClaims, hvalid, ?_⟩
  let xs := playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims
  have hpos : ∀ x ∈ xs, 0 ≤ x := by
    intro x hx
    dsimp [xs, playedPieces] at hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact playPieceLength_nonneg s xiangPoints hd _
  have hpairs : ∀ q, 2 * q + 2 < xs.length →
      xs.getD (2 * q + 2) 0 ≤ xs.getD (2 * q + 1) 0 := by
    intro q hq
    exact second_greedy_shifted_piece_bounds
      s xiangPoints card_xiangPoints_le hd xiangClaims hvalid hmax q hq
  have htail : PairDominates xs.tail :=
    pairDominates_tail_of_indexed_shifted xs hpos hpairs
  have himbalance : alternatingImbalance xs ≤ xs.getD 0 0 := by
    cases hxs : xs with
    | nil => simp [hxs, alternatingImbalance]
    | cons x ys =>
        have h := alternatingImbalance_le_head_of_tail_pairDominates
          (x := x) (xs := ys) (by simpa [hxs] using htail)
        simpa [hxs] using h
  have hdifference :
      s.playLength xiangPoints card_xiangPoints_le hd xiangClaims -
        s.secondPlayLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ xs.getD 0 0 := by
    rw [playImbalance_eq_alternatingImbalance]
    exact himbalance
  have hsum := playLength_add_secondPlayLength_eq_one
    s xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  dsimp [xs] at hdifference ⊢
  linarith

private lemma exists_static_sorted_board_bound_of_alternating_bound
    {n : ℕ+} {s : Strategy n}
    {xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)}
    (hd : Disjoint s.points xiangPoints)
    (himb : alternatingImbalance
      ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
        2 * answer n - 1) :
    firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
      answer n := by
  rw [sorted_firstPlayerSum_eq_half_one_add s xiangPoints hd]
  linarith

private lemma binary_tolerance_recurrence (m : ℕ) (hm : 1 ≤ m) :
    (1 : ℝ) / ((2 : ℝ) ^ (m + 1) - 1) =
      ((1 : ℝ) / ((2 : ℝ) ^ m - 1)) /
        (2 + (1 : ℝ) / ((2 : ℝ) ^ m - 1)) := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ m := by
    exact one_lt_pow₀ (by norm_num) (by omega)
  have hne : (2 : ℝ) ^ m - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpow)
  rw [pow_succ]
  field_simp
  ring

private lemma alternatingImbalance_duplicate_prefix_identity
    (pairs residual : List ℝ) :
    alternatingImbalance
        ((pairs.flatMap fun x => [x, x]) ++ residual) =
      alternatingImbalance residual := by
  induction pairs with
  | nil => simp
  | cons x pairs ih =>
      simpa [alternatingImbalance] using ih

private lemma alternatingImbalance_append_zero (xs : List ℝ) :
    alternatingImbalance (xs ++ [0]) = alternatingImbalance xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingImbalance]
  | singleton x => simp [alternatingImbalance]
  | cons_cons x y xs ih => simp [alternatingImbalance, ih]

private lemma alternatingImbalance_insert_adjacent_equal
    (pre suffix : List ℝ) (x : ℝ) :
    alternatingImbalance (pre ++ x :: x :: suffix) =
      alternatingImbalance (pre ++ suffix) := by
  induction pre with
  | nil => simp [alternatingImbalance]
  | cons y pre ih =>
      simp only [List.cons_append]
      rw [alternatingImbalance_cons y, alternatingImbalance_cons y, ih]

private lemma signed_subset_difference_identity {m : ℕ}
    (x : Fin m → ℝ) (A B : Finset (Fin m)) :
    (∑ i, ((if i ∈ A then (1 : ℝ) else 0) -
      (if i ∈ B then (1 : ℝ) else 0)) * x i) =
      (∑ i ∈ A, x i) - ∑ i ∈ B, x i := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp

private lemma exists_ternary_signed_sum_eq_subset_sum_sub {m : ℕ}
    (x : Fin m → ℝ) (A B : Finset (Fin m)) (hAB : A ≠ B) :
    ∃ c : Fin m → ℤ,
      (∃ i, c i ≠ 0) ∧
      (∀ i, c i = -1 ∨ c i = 0 ∨ c i = 1) ∧
      (∑ i, (c i : ℝ) * x i) =
        (∑ i ∈ A, x i) - ∑ i ∈ B, x i := by
  let c : Fin m → ℤ := fun i =>
    (if i ∈ A then 1 else 0) - (if i ∈ B then 1 else 0)
  refine ⟨c, ?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hAB
    ext i
    have hi := h i
    simp only [c] at hi
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;>
      simp [ha, hb] at hi ⊢
  · intro i
    by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;>
      simp [c, ha, hb]
  · simp only [c, Int.cast_sub, Int.cast_ite, Int.cast_one,
      Int.cast_zero, sub_mul, Finset.sum_sub_distrib]
    simp

private lemma finite_real_finset_spacing
    (s : Finset ℝ) (hs_card : 2 ≤ s.card)
    (hs_range : ∀ y ∈ s, y ∈ Set.Icc (0 : ℝ) 1) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      |a - b| ≤ 1 / ((s.card : ℝ) - 1) := by
  let n := s.card - 1
  have hn : 0 < n := by omega
  have hcard : s.card = n + 1 := by omega
  let e : Fin (n + 1) ↪o ℝ := s.orderEmbOfFin hcard
  let f : ℕ → ℝ := fun i => if hi : i < n + 1 then e ⟨i, hi⟩ else 0
  have hf_mem (i : ℕ) (hi : i < n + 1) : f i ∈ s := by
    unfold f
    rw [dif_pos hi]
    exact Finset.orderEmbOfFin_mem s hcard ⟨i, hi⟩
  have hf_lt (i : ℕ) (hi : i < n) : f i < f (i + 1) := by
    unfold f
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact e.lt_iff_lt.mpr (by simp)
  have hex : ∃ i < n, f (i + 1) - f i ≤ 1 / (n : ℝ) := by
    by_contra h
    push Not at h
    have hsum : (∑ i ∈ Finset.range n, (1 / (n : ℝ))) <
        ∑ i ∈ Finset.range n, (f (i + 1) - f i) := by
      exact Finset.sum_lt_sum_of_nonempty
        ⟨0, Finset.mem_range.mpr hn⟩
        (fun i hi => h i (Finset.mem_range.mp hi))
    rw [Finset.sum_range_sub] at hsum
    have hends : f n - f 0 ≤ 1 := by
      have h0 := hs_range (f 0) (hf_mem 0 (by omega))
      have hn' := hs_range (f n) (hf_mem n (by omega))
      linarith [h0.1, hn'.2]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    simp [hnR] at hsum
    linarith
  obtain ⟨i, hi, hgap⟩ := hex
  refine ⟨f i, hf_mem i (by omega), f (i + 1), hf_mem (i + 1) (by omega), ?_, ?_⟩
  · exact ne_of_lt (hf_lt i hi)
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (hf_lt i hi)))]
    rw [hcard]
    norm_num
    simpa [n] using hgap

private lemma exists_distinct_subset_sums_close
    {m : ℕ} (x : Fin m → ℝ) (hm : 1 ≤ m)
    (hx0 : ∀ i, 0 ≤ x i)
    (hsum : ∑ i, x i = 1) :
    ∃ A B : Finset (Fin m), A ≠ B ∧
      |(∑ i ∈ A, x i) - ∑ i ∈ B, x i| ≤
        1 / ((2 : ℝ) ^ m - 1) := by
  let f : Finset (Fin m) → ℝ := fun A => ∑ i ∈ A, x i
  have hf_range (A : Finset (Fin m)) : f A ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact Finset.sum_nonneg fun i _ => hx0 i
    · rw [← hsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
        (fun i _ _ => hx0 i)
  have hcard : Fintype.card (Finset (Fin m)) = 2 ^ m := by simp
  have htwo : 2 ≤ Fintype.card (Finset (Fin m)) := by
    rw [hcard]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [pow_succ]
    have hp : 1 ≤ 2 ^ k := one_le_pow₀ (by omega)
    omega
  by_cases hinj : Function.Injective f
  · let s : Finset ℝ := Finset.univ.image f
    have hs_card : s.card = Fintype.card (Finset (Fin m)) := by
      exact Finset.card_image_of_injective _ hinj
    have hs_range : ∀ y ∈ s, y ∈ Set.Icc (0 : ℝ) 1 := by
      intro y hy
      simp only [s, Finset.mem_image] at hy
      obtain ⟨A, _, rfl⟩ := hy
      exact hf_range A
    obtain ⟨a, ha, b, hb, hab, hclose⟩ :=
      finite_real_finset_spacing s (by omega) hs_range
    simp only [s, Finset.mem_image] at ha hb
    obtain ⟨A, _, rfl⟩ := ha
    obtain ⟨B, _, rfl⟩ := hb
    refine ⟨A, B, fun h => hab (congrArg f h), ?_⟩
    simpa [f, hs_card, hcard] using hclose
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨A, B, heq, hne⟩ := hinj
    refine ⟨A, B, hne, ?_⟩
    have hp : (1 : ℝ) < (2 : ℝ) ^ m :=
      one_lt_pow₀ (by norm_num) (by omega)
    have heq' : (∑ i ∈ A, x i) = ∑ i ∈ B, x i := by
      simpa [f] using heq
    rw [heq', sub_self, abs_zero]
    positivity

private lemma pair_two_positive_blocks (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ as bs pairs residual : List ℝ,
      as.sum = a ∧ bs.sum = b ∧
      (∀ x ∈ as ++ bs, 0 < x) ∧
      (as ++ bs).Perm ((pairs.flatMap fun x => [x, x]) ++ residual) ∧
      (as.length - 1) + (bs.length - 1) ≤ 1 ∧
      (∀ x ∈ residual, 0 ≤ x) ∧ residual.sum = |a - b| := by
  rcases lt_trichotomy a b with hab | hab | hab
  · refine ⟨[a], [a, b - a], [a], [b - a], ?_⟩
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp [ha, sub_pos.mpr hab]
    constructor
    · simp
    constructor
    · norm_num
    constructor
    · simp [sub_nonneg.mpr hab.le]
    · simp [abs_of_nonpos (sub_nonpos.mpr hab.le)]
  · subst b
    refine ⟨[a], [a], [a], [], ?_⟩
    simp [ha]
  · refine ⟨[b, a - b], [b], [b], [a - b], ?_⟩
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp [hb, sub_pos.mpr hab]
    constructor
    · simpa using (List.Perm.swap b (a - b) [])
    constructor
    · norm_num
    constructor
    · simp [sub_nonneg.mpr hab.le]
    · simp [abs_of_nonneg (sub_nonneg.mpr hab.le)]

private lemma pair_two_positive_blocks_sided
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a < b ∧
      ∃ r, r = b - a ∧ 0 < r ∧
        [a].sum = a ∧ [a, r].sum = b) ∨
    (a = b) ∨
    (b < a ∧
      ∃ r, r = a - b ∧ 0 < r ∧
        [b, r].sum = a ∧ [b].sum = b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · left
    refine ⟨hab, b - a, rfl, sub_pos.mpr hab, by simp, ?_⟩
    simp
  · exact Or.inr (Or.inl hab)
  · right
    right
    refine ⟨hab, a - b, rfl, sub_pos.mpr hab, ?_, by simp⟩
    simp

private lemma flatten_map_singleton_real (R : List ℝ) :
    (R.map ([·])).flatten = R := by
  induction R with
  | nil => rfl
  | cons r R ih => simp only [List.map_cons, List.flatten_cons,
      List.singleton_append, ih]

private lemma singleton_blocks_excess_zero (R : List ℝ) :
    ((R.map ([·])).map (fun block => block.length - 1)).sum = 0 := by
  rw [List.map_map]
  have hfun : ((fun block : List ℝ => block.length - 1) ∘ fun x => [x]) =
      fun _ => 0 := by
    funext x
    simp
  rw [hfun]
  simp

private lemma paired_transport_single_left_lt
    (a b : ℝ) (R : List ℝ)
    (ha : 0 < a) (hRpos : ∀ x ∈ R, 0 < x) (hab : a < b) :
    ∃ (LB RB : List (List ℝ)) (pairs residual : List ℝ),
      LB.length = [a].length ∧
      RB.length = (b :: R).length ∧
      LB.map List.sum = [a] ∧
      RB.map List.sum = b :: R ∧
      (∀ block ∈ LB ++ RB, block ≠ [] ∧ ∀ y ∈ block, 0 < y) ∧
      (LB.flatten ++ RB.flatten).Perm
        ((pairs.flatMap fun y => [y, y]) ++ residual) ∧
      (∀ y ∈ residual, 0 ≤ y) ∧
      residual.sum = |[a].sum - (b :: R).sum| ∧
      (LB.map (fun block => block.length - 1)).sum +
          (RB.map (fun block => block.length - 1)).sum
        ≤ [a].length + (b :: R).length - 1 := by
  let singles : List (List ℝ) := R.map ([·])
  have hsums : singles.map List.sum = R := by
    simp [singles, Function.comp_def]
  have hflat : singles.flatten = R := by
    exact flatten_map_singleton_real R
  have hexcess : (singles.map (fun block => block.length - 1)).sum = 0 := by
    exact singleton_blocks_excess_zero R
  have hRnonneg : ∀ r ∈ R, 0 ≤ r := by
    intro r hr
    exact (hRpos r hr).le
  have hRsum : 0 ≤ R.sum := List.sum_nonneg hRnonneg
  refine ⟨[[a]], [a, b - a] :: singles, [a], (b - a) :: R, ?_⟩
  constructor
  · simp
  constructor
  · simp [singles]
  constructor
  · simp
  constructor
  · simp [hsums]
  constructor
  · intro block hblock
    simp only [List.mem_append, List.mem_cons] at hblock
    rcases hblock with (rfl | hfalse) | rfl | hsingles
    · exact ⟨by simp, by simp [ha]⟩
    · contradiction
    · exact ⟨by simp, by simp [ha, sub_pos.mpr hab]⟩
    · simp only [singles, List.mem_map] at hsingles
      obtain ⟨r, hr, rfl⟩ := hsingles
      exact ⟨by simp, by simp [hRpos r hr]⟩
  constructor
  · simp [hflat]
  constructor
  · intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact (sub_pos.mpr hab).le
    · exact hRnonneg r hr
  constructor
  · simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [abs_of_nonpos]
    · ring
    · linarith
  · simp [hexcess]

private lemma close_subset_partition_facts
    {m : ℕ} (A B : Finset (Fin m)) (hAB : A ≠ B) :
    let P := A \ B
    let N := B \ A
    let Z := Finset.univ \ (P ∪ N)
    Disjoint P N ∧
      Disjoint P Z ∧
      Disjoint N Z ∧
      P ∪ N ∪ Z = Finset.univ ∧
      (P ∪ N).Nonempty ∧
      P.card + N.card + Z.card = m := by
  dsimp
  have hPN : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp only [Finset.mem_sdiff] at hiP hiN
    exact hiP.2 hiN.1
  have hPZ : Disjoint (A \ B) (Finset.univ \ ((A \ B) ∪ (B \ A))) := by
    rw [Finset.disjoint_left]
    intro i hiP hiZ
    simp only [Finset.mem_sdiff] at hiP
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union] at hiZ
    exact hiZ (Or.inl hiP)
  have hNZ : Disjoint (B \ A) (Finset.univ \ ((A \ B) ∪ (B \ A))) := by
    rw [Finset.disjoint_left]
    intro i hiN hiZ
    simp only [Finset.mem_sdiff] at hiN
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union] at hiZ
    exact hiZ (Or.inr hiN)
  have hUZ : Disjoint ((A \ B) ∪ (B \ A))
      (Finset.univ \ ((A \ B) ∪ (B \ A))) := by
    rw [Finset.disjoint_left]
    intro i hiU hiZ
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hiZ
    exact hiZ hiU
  have hcover : (A \ B) ∪ (B \ A) ∪
      (Finset.univ \ ((A \ B) ∪ (B \ A))) = Finset.univ := by
    ext i
    simp
  refine ⟨hPN, hPZ, hNZ, hcover, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hAB
    ext i
    have hi : i ∉ (A \ B) ∪ (B \ A) := by simp [hempty]
    simp only [Finset.mem_union, Finset.mem_sdiff] at hi
    tauto
  · have hc := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hUZ,
      Finset.card_union_of_disjoint hPN] at hc
    simpa using hc

private lemma half_pair_refinement_exact (R : List ℝ)
    (hpos : ∀ x ∈ R, 0 < x) :
    ∃ fine pairs : List ℝ,
      RefinesByBlocks fine R ∧
      (∀ y ∈ fine, 0 < y) ∧
      fine = pairs.flatMap (fun y => [y, y]) ∧
      fine.length - R.length = R.length := by
  let blocks : List (List ℝ) := R.map (fun x => [x / 2, x / 2])
  let pairs : List ℝ := R.map (fun x => x / 2)
  refine ⟨blocks.flatten, pairs, ?_, ?_, ?_, ?_⟩
  · refine ⟨blocks, by simp [blocks], rfl, ?_, ?_⟩
    · simp [blocks, Function.comp_def]
    · intro b hb
      simp only [blocks, List.mem_map] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      simp
  · intro y hy
    simp only [blocks, List.mem_flatten, List.mem_map] at hy
    obtain ⟨b, ⟨x, hx, rfl⟩, hy⟩ := hy
    simp at hy
    subst y
    exact div_pos (hpos x hx) (by norm_num)
  · dsimp [blocks, pairs]
    clear hpos
    induction R with
    | nil => rfl
    | cons x R ih => simp [ih]
  · dsimp [blocks]
    clear hpos
    induction R with
    | nil => simp
    | cons x R ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        List.length_cons, List.length_nil, Nat.add_zero]
      omega

private lemma predicate_half_pair_refinement
    (R : List ℝ) (p : ℝ → Prop) [DecidablePred p]
    (hpos : ∀ x ∈ R, 0 < x) :
    ∃ fine pairs residual : List ℝ,
      RefinesByBlocks fine R ∧
      (∀ y ∈ fine, 0 < y) ∧
      fine.Perm ((pairs.flatMap fun y => [y, y]) ++ residual) ∧
      residual = R.filter (fun y => ¬ p y) ∧
      fine.length - R.length = (R.filter p).length := by
  induction R with
  | nil =>
      exact ⟨[], [], [], refinesByBlocks_refl [], by simp, by simp, by simp, by simp⟩
  | cons y R ih =>
      have hy : 0 < y := hpos y (by simp)
      have hR : ∀ z ∈ R, 0 < z := by
        intro z hz
        exact hpos z (by simp [hz])
      obtain ⟨fine, pairs, residual, href, hfine, hperm, hres, hlen⟩ := ih hR
      obtain ⟨blocks, hblen, hflat, hbsum, hbne⟩ := href
      have hcoarse : R.length ≤ fine.length :=
        length_le_of_refinesByBlocks ⟨blocks, hblen, hflat, hbsum, hbne⟩
      by_cases hp : p y
      · refine ⟨y / 2 :: y / 2 :: fine, y / 2 :: pairs, residual, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨[y / 2, y / 2] :: blocks, by simp [hblen], ?_, ?_, ?_⟩
          · simp [hflat]
          · simp [hbsum]
          · intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hb
            · simp
            · exact hbne b hb
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | rfl | hz
          · exact div_pos hy (by norm_num)
          · exact div_pos hy (by norm_num)
          · exact hfine z hz
        · simpa using (hperm.cons (y / 2)).cons (y / 2)
        · simp [hp, hres]
        · simp [hp]
          omega
      · refine ⟨y :: fine, pairs, y :: residual, ?_, ?_, ?_, ?_, ?_⟩
        · refine ⟨[y] :: blocks, by simp [hblen], ?_, ?_, ?_⟩
          · simp [hflat]
          · simp [hbsum]
          · intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with rfl | hb
            · simp
            · exact hbne b hb
        · intro z hz
          simp only [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hy
          · exact hfine z hz
        · have hmove (a : ℝ) (l₁ l₂ : List ℝ) :
              (a :: (l₁ ++ l₂)).Perm (l₁ ++ a :: l₂) := by
            induction l₁ with
            | nil => simp
            | cons b l₁ ih =>
              simpa only [List.cons_append] using
                (List.Perm.swap b a (l₁ ++ l₂)).trans (ih.cons b)
          exact (hperm.cons y).trans
            (hmove y (pairs.flatMap fun z => [z, z]) residual)
        · simp [hp, hres]
        · simp [hp]
          omega

private lemma subset_sum_difference_sdiff {m : ℕ} (x : Fin m → ℝ)
    (A B : Finset (Fin m)) :
    (∑ i ∈ A, x i) - ∑ i ∈ B, x i =
      (∑ i ∈ A \ B, x i) - ∑ i ∈ B \ A, x i := by
  simpa using (Finset.sum_sdiff_sub_sum_sdiff :
    (∑ i ∈ A \ B, x i) - ∑ i ∈ B \ A, x i =
      (∑ i ∈ A, x i) - ∑ i ∈ B, x i).symm

private lemma sdiff_nonempty_or_sdiff_nonempty {m : ℕ}
    {A B : Finset (Fin m)} (hAB : A ≠ B) :
    (A \ B).Nonempty ∨ (B \ A).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, Finset.nonempty_iff_ne_empty]
  by_contra h
  push Not at h
  apply hAB
  apply Finset.Subset.antisymm
  · exact Finset.sdiff_eq_empty_iff_subset.mp h.1
  · exact Finset.sdiff_eq_empty_iff_subset.mp h.2

private lemma append_half_pairs_perm
    (core pairs residual Z : List ℝ)
    (hcore : core.Perm ((pairs.flatMap fun y => [y, y]) ++ residual)) :
    (core ++ Z.flatMap fun z => [z / 2, z / 2]).Perm
      (((pairs ++ Z.map fun z => z / 2).flatMap fun y => [y, y]) ++ residual) := by
  let pf := pairs.flatMap fun y => [y, y]
  let zh := Z.flatMap fun z => [z / 2, z / 2]
  have hmove (a : ℝ) (ys : List ℝ) : (a :: ys).Perm (ys ++ [a]) := by
    induction ys with
    | nil => simp
    | cons b ys ih =>
      exact (List.Perm.swap _ _ _).trans (ih.cons b)
  have hcomm (xs ys : List ℝ) : (xs ++ ys).Perm (ys ++ xs) := by
    induction xs with
    | nil => simp
    | cons a xs ih =>
      apply (ih.cons a).trans
      simpa [List.append_assoc] using (hmove a ys).append_right xs
  have hz : (Z.map fun z => z / 2).flatMap (fun y => [y, y]) = zh := by
    simp [zh, List.flatMap_map]
  have h₁ : (core ++ zh).Perm ((pf ++ residual) ++ zh) := by
    exact hcore.append_right zh
  have h₂ : ((pf ++ residual) ++ zh).Perm ((pf ++ zh) ++ residual) := by
    simpa [List.append_assoc] using (hcomm residual zh).append_left pf
  dsimp [pf, zh] at h₁ h₂ ⊢
  rw [List.flatMap_append, hz]
  exact h₁.trans h₂

private lemma paired_transport_nil_right
    (L : List ℝ) (hLpos : ∀ x ∈ L, 0 < x) :
    ∃ LB : List (List ℝ),
      LB.length = L.length ∧
      LB.map List.sum = L ∧
      LB.flatten = L ∧
      (∀ block ∈ LB, block ≠ [] ∧ ∀ y ∈ block, 0 < y) ∧
      (LB.map (fun block => block.length - 1)).sum = 0 ∧
      (∀ y ∈ L, 0 ≤ y) ∧
      L.sum = |L.sum - ([] : List ℝ).sum| := by
  refine ⟨L.map ([·]), by simp, ?_, flatten_map_singleton_real L, ?_,
    singleton_blocks_excess_zero L, ?_, ?_⟩
  · simp [Function.comp_def]
  · intro block hblock
    simp only [List.mem_map] at hblock
    obtain ⟨x, hx, rfl⟩ := hblock
    exact ⟨by simp, by simp [hLpos x hx]⟩
  · intro y hy
    exact (hLpos y hy).le
  · simp only [List.sum_nil, sub_zero]
    rw [abs_of_nonneg]
    exact List.sum_nonneg (fun y hy => (hLpos y hy).le)

private lemma paired_transport_measure_steps
    (a b : ℝ) (L R : List ℝ) :
    L.length + ((b - a) :: R).length <
        (a :: L).length + (b :: R).length ∧
      ((a - b) :: L).length + R.length <
        (a :: L).length + (b :: R).length := by
  simp

private lemma paired_transport_residual_invariants (a b s t : ℝ) :
    |(a + s) - (b + t)| = |s - ((b - a) + t)| ∧
      |(a + s) - (b + t)| = |((a - b) + s) - t| := by
  constructor <;> congr 1 <;> ring

private lemma prepend_duplicate_transport_perm
    (a : ℝ) (left right pairs residual : List ℝ)
    (hperm : (left ++ right).Perm
      ((pairs.flatMap fun y => [y, y]) ++ residual)) :
    (a :: left ++ a :: right).Perm
      ((((a :: pairs).flatMap fun y => [y, y])) ++ residual) := by
  have hmove (x : ℝ) (l₁ l₂ : List ℝ) :
      (x :: (l₁ ++ l₂)).Perm (l₁ ++ x :: l₂) := by
    induction l₁ with
    | nil => simp
    | cons b l₁ ih =>
      simpa only [List.cons_append] using
        (List.Perm.swap b x (l₁ ++ l₂)).trans (ih.cons b)
  have hins :
      (a :: left ++ a :: right).Perm (a :: a :: (left ++ right)) := by
    exact (hmove a left right).symm.cons a
  exact hins.trans (by simpa using (hperm.cons a).cons a)

private lemma paired_transport
    (L R : List ℝ)
    (hLpos : ∀ x ∈ L, 0 < x)
    (hRpos : ∀ x ∈ R, 0 < x) :
    ∃ (LB RB : List (List ℝ)) (pairs residual : List ℝ),
      LB.length = L.length ∧
      RB.length = R.length ∧
      LB.map List.sum = L ∧
      RB.map List.sum = R ∧
      (∀ block ∈ LB ++ RB, block ≠ [] ∧ ∀ y ∈ block, 0 < y) ∧
      (LB.flatten ++ RB.flatten).Perm
        ((pairs.flatMap fun y => [y, y]) ++ residual) ∧
      (∀ y ∈ residual, 0 ≤ y) ∧
      residual.sum = |L.sum - R.sum| ∧
      (LB.map (fun block => block.length - 1)).sum +
          (RB.map (fun block => block.length - 1)).sum
        ≤ L.length + R.length - 1 := by
  let Good : List ℝ → List ℝ → Prop := fun L R =>
    ∃ (LB RB : List (List ℝ)) (pairs residual : List ℝ),
      LB.length = L.length ∧
      RB.length = R.length ∧
      LB.map List.sum = L ∧
      RB.map List.sum = R ∧
      (∀ block ∈ LB ++ RB, block ≠ [] ∧ ∀ y ∈ block, 0 < y) ∧
      (LB.flatten ++ RB.flatten).Perm
        ((pairs.flatMap fun y => [y, y]) ++ residual) ∧
      (∀ y ∈ residual, 0 ≤ y) ∧
      residual.sum = |L.sum - R.sum| ∧
      (LB.map (fun block => block.length - 1)).sum +
          (RB.map (fun block => block.length - 1)).sum
        ≤ L.length + R.length - 1
  change Good L R
  have hmain : ∀ n, ∀ (L R : List ℝ), L.length + R.length = n →
      (∀ x ∈ L, 0 < x) → (∀ x ∈ R, 0 < x) → Good L R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L R hmeasure hLpos hRpos
      cases L with
      | nil =>
        obtain ⟨RB, hRBlen, hRBsums, hflat, hblocks, hexcess,
            hnonneg, hsum⟩ := paired_transport_nil_right R hRpos
        refine ⟨[], RB, [], R, by simp, hRBlen, by simp, hRBsums,
          ?_, ?_, hnonneg, ?_, ?_⟩
        · simpa using hblocks
        · simp [hflat]
        · simpa [abs_sub_comm] using hsum
        · simp [hexcess]
      | cons a L =>
        have ha : 0 < a := hLpos a (by simp)
        have hLtail : ∀ x ∈ L, 0 < x := by
          intro x hx
          exact hLpos x (by simp [hx])
        cases R with
        | nil =>
          obtain ⟨LB, hLBlen, hLBsums, hflat, hblocks, hexcess,
              hnonneg, hsum⟩ := paired_transport_nil_right (a :: L) hLpos
          refine ⟨LB, [], [], a :: L, hLBlen, by simp, hLBsums, by simp,
            ?_, ?_, hnonneg, hsum, ?_⟩
          · simpa using hblocks
          · simp [hflat]
          · simp [hexcess]
        | cons b R =>
          have hb : 0 < b := hRpos b (by simp)
          have hRtail : ∀ x ∈ R, 0 < x := by
            intro x hx
            exact hRpos x (by simp [hx])
          have hmove (x : ℝ) (xs ys : List ℝ) :
              (xs ++ x :: ys).Perm (x :: xs ++ ys) := by
            induction xs with
            | nil => simp
            | cons z zs ih' =>
              exact (ih'.cons z).trans
                (List.Perm.swap z x (zs ++ ys)).symm
          rcases lt_trichotomy a b with hab | hab | hab
          · have hr : 0 < b - a := sub_pos.mpr hab
            have hsmall := (paired_transport_measure_steps a b L R).1
            have hrec := ih
              (L.length + ((b - a) :: R).length)
              (hsmall.trans_eq hmeasure) L ((b - a) :: R) rfl hLtail (by
                intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hr
                · exact hRtail x hx)
            obtain ⟨LB, RB, pairs, residual, hLBlen, hRBlen,
                hLBsums, hRBsums, hblocks, hperm, hresnonneg,
                hressum, hcut⟩ := hrec
            cases RB with
            | nil => simp at hRBlen
            | cons block RB =>
              have hblock : block ≠ [] ∧ ∀ y ∈ block, 0 < y :=
                hblocks block (by simp)
              have htails : ∀ c ∈ LB ++ RB,
                  c ≠ [] ∧ ∀ y ∈ c, 0 < y := by
                intro c hc
                apply hblocks c
                simp only [List.mem_append, List.mem_cons] at hc ⊢
                rcases hc with hc | hc
                · exact Or.inl hc
                · exact Or.inr (Or.inr hc)
              simp only [List.map_cons, List.cons.injEq] at hRBsums
              obtain ⟨hblocksum, hRBtailsums⟩ := hRBsums
              refine ⟨[a] :: LB, (a :: block) :: RB, a :: pairs, residual,
                ?_, ?_, ?_, ?_, ?_, ?_, hresnonneg, ?_, ?_⟩
              · simp [hLBlen]
              · simp only [List.length_cons] at hRBlen ⊢
                omega
              · simp [hLBsums]
              · simp [hRBtailsums, hblocksum]
              · intro c hc
                simp only [List.mem_append, List.mem_cons] at hc
                rcases hc with (rfl | hc) | rfl | hc
                · exact ⟨by simp, by simp [ha]⟩
                · exact htails c (by simp [hc])
                · refine ⟨by simp, ?_⟩
                  intro y hy
                  simp only [List.mem_cons] at hy
                  rcases hy with rfl | hy
                  · exact ha
                  · exact hblock.2 y hy
                · exact htails c (by simp [hc])
              · simp only [List.flatten_cons, List.singleton_append]
                change (a :: (LB.flatten ++ (a :: block ++ RB.flatten))).Perm _
                have hfront := (hmove a LB.flatten
                  (block ++ RB.flatten)).cons a
                apply hfront.trans
                convert (hperm.cons a).cons a using 1 <;>
                  simp only [List.flatten_cons, List.flatMap_cons,
                    List.cons_append, List.nil_append]
              · rw [hressum]
                congr 1
                simp only [List.sum_cons]
                ring
              · have hblocklen : 1 ≤ block.length := by
                  cases block with
                  | nil => exact False.elim (hblock.1 rfl)
                  | cons x xs => simp
                have hrecRhs : L.length + ((b - a) :: R).length - 1 =
                    L.length + R.length := by simp
                have htargetRhs : (a :: L).length + (b :: R).length - 1 =
                    L.length + R.length + 1 := by simp; omega
                rw [hrecRhs] at hcut
                rw [htargetRhs]
                simp only [List.map_cons, List.sum_cons, List.length_cons,
                  List.length_nil, Nat.add_sub_cancel] at hcut ⊢
                omega
          · subst b
            have htailMeasure : L.length + R.length < n := by
              simp only [List.length_cons] at hmeasure
              omega
            have hrec := ih (L.length + R.length) htailMeasure
              L R rfl hLtail hRtail
            obtain ⟨LB, RB, pairs, residual, hLBlen, hRBlen,
                hLBsums, hRBsums, hblocks, hperm, hresnonneg,
                hressum, hcut⟩ := hrec
            refine ⟨[a] :: LB, [a] :: RB, a :: pairs, residual,
              ?_, ?_, ?_, ?_, ?_, ?_, hresnonneg, ?_, ?_⟩
            · simp [hLBlen]
            · simp [hRBlen]
            · simp [hLBsums]
            · simp [hRBsums]
            · intro c hc
              simp only [List.mem_append, List.mem_cons] at hc
              rcases hc with (rfl | hc) | rfl | hc
              · exact ⟨by simp, by simp [ha]⟩
              · exact hblocks c (by simp [hc])
              · exact ⟨by simp, by simp [ha]⟩
              · exact hblocks c (by simp [hc])
            · simpa only [List.flatten_cons, List.singleton_append] using
                prepend_duplicate_transport_perm a LB.flatten RB.flatten
                  pairs residual hperm
            · rw [hressum]
              congr 1
              simp only [List.sum_cons]
              ring
            · have htargetRhs : (a :: L).length + (a :: R).length - 1 =
                  L.length + R.length + 1 := by simp; omega
              rw [htargetRhs]
              simp only [List.map_cons, List.sum_cons, List.length_cons,
                List.length_nil, Nat.add_sub_cancel]
              omega
          · have hr : 0 < a - b := sub_pos.mpr hab
            have hsmall := (paired_transport_measure_steps a b L R).2
            have hrec := ih
              (((a - b) :: L).length + R.length)
              (hsmall.trans_eq hmeasure) ((a - b) :: L) R rfl (by
                intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact hr
                · exact hLtail x hx) hRtail
            obtain ⟨LB, RB, pairs, residual, hLBlen, hRBlen,
                hLBsums, hRBsums, hblocks, hperm, hresnonneg,
                hressum, hcut⟩ := hrec
            cases LB with
            | nil => simp at hLBlen
            | cons block LB =>
              have hblock : block ≠ [] ∧ ∀ y ∈ block, 0 < y :=
                hblocks block (by simp)
              have htails : ∀ c ∈ LB ++ RB,
                  c ≠ [] ∧ ∀ y ∈ c, 0 < y := by
                intro c hc
                apply hblocks c
                simp only [List.mem_append, List.mem_cons] at hc ⊢
                rcases hc with hc | hc
                · exact Or.inl (Or.inr hc)
                · exact Or.inr hc
              simp only [List.map_cons, List.cons.injEq] at hLBsums
              obtain ⟨hblocksum, hLBtailsums⟩ := hLBsums
              refine ⟨(b :: block) :: LB, [b] :: RB, b :: pairs, residual,
                ?_, ?_, ?_, ?_, ?_, ?_, hresnonneg, ?_, ?_⟩
              · simp only [List.length_cons] at hLBlen ⊢
                omega
              · simp [hRBlen]
              · simp [hLBtailsums, hblocksum]
              · simp [hRBsums]
              · intro c hc
                simp only [List.mem_append, List.mem_cons] at hc
                rcases hc with (rfl | hc) | rfl | hc
                · refine ⟨by simp, ?_⟩
                  intro y hy
                  simp only [List.mem_cons] at hy
                  rcases hy with rfl | hy
                  · exact hb
                  · exact hblock.2 y hy
                · exact htails c (by simp [hc])
                · exact ⟨by simp, by simp [hb]⟩
                · exact htails c (by simp [hc])
              · simp only [List.flatten_cons, List.singleton_append]
                change (b :: (block ++ LB.flatten ++ b :: RB.flatten)).Perm _
                have hfront := (hmove b (block ++ LB.flatten) RB.flatten).cons b
                apply hfront.trans
                convert (hperm.cons b).cons b using 1 <;>
                  simp only [List.flatten_cons, List.flatMap_cons,
                    List.cons_append, List.nil_append, List.append_assoc]
              · rw [hressum]
                congr 1
                simp only [List.sum_cons]
                ring
              · have hblocklen : 1 ≤ block.length := by
                  cases block with
                  | nil => exact False.elim (hblock.1 rfl)
                  | cons x xs => simp
                have hrecRhs : ((a - b) :: L).length + R.length - 1 =
                    L.length + R.length := by simp
                have htargetRhs : (a :: L).length + (b :: R).length - 1 =
                    L.length + R.length + 1 := by simp; omega
                rw [hrecRhs] at hcut
                rw [htargetRhs]
                simp only [List.map_cons, List.sum_cons, List.length_cons,
                  List.length_nil, Nat.add_sub_cancel] at hcut ⊢
                omega
  exact hmain (L.length + R.length) L R rfl hLpos hRpos

private lemma perm_map_lift {α β : Type*} (f : α → β)
    (l₁ : List α) (l₂ : List β) (h : (l₁.map f).Perm l₂) :
    ∃ l₃ : List α, l₁.Perm l₃ ∧ l₃.map f = l₂ := by
  generalize heq : l₁.map f = u at h
  induction h generalizing l₁ with
  | nil =>
      simp only [List.map_eq_nil_iff] at heq
      subst l₁
      exact ⟨[], .refl [], rfl⟩
  | @cons a l₂ l₃ h ih =>
      cases l₁ with
      | nil => simp at heq
      | cons b bs =>
        simp only [List.map_cons, List.cons.injEq] at heq
        obtain ⟨hab, htail⟩ := heq
        subst a
        obtain ⟨cs, hperm, hmap⟩ := ih bs htail
        exact ⟨b :: cs, hperm.cons b, by simp [hmap]⟩
  | @swap a b l =>
      cases l₁ with
      | nil => simp at heq
      | cons x xs =>
        cases xs with
        | nil => simp at heq
        | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at heq
          obtain ⟨hxb, hya, htail⟩ := heq
          subst b
          subst a
          exact ⟨y :: x :: ys, (List.Perm.swap x y ys).symm, by simp [htail]⟩
  | @trans l₂ l₃ l₄ h₁ h₂ ih₁ ih₂ =>
      obtain ⟨cs, hperm₁, hmap₁⟩ := ih₁ l₁ heq
      obtain ⟨ds, hperm₂, hmap₂⟩ := ih₂ cs hmap₁
      exact ⟨ds, hperm₁.trans hperm₂, hmap₂⟩

private lemma partition_sort_perm_ofFn
    {m : ℕ} (P N Z : Finset (Fin m))
    (hPN : Disjoint P N) (hPZ : Disjoint P Z) (hNZ : Disjoint N Z)
    (hcover : P ∪ N ∪ Z = Finset.univ) :
    (P.sort (· ≤ ·) ++ N.sort (· ≤ ·) ++ Z.sort (· ≤ ·)).Perm
      (List.ofFn id) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, ?_⟩,
      Finset.sort_nodup _ _, ?_⟩
    · intro a ha b hb hab
      subst b
      apply Finset.disjoint_left.mp hPN
      · simpa using ha
      · simpa using hb
    · intro a ha b hb hab
      subst b
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · apply Finset.disjoint_left.mp hPZ
        · simpa using ha
        · simpa using hb
      · apply Finset.disjoint_left.mp hNZ
        · simpa using ha
        · simpa using hb
  · exact List.nodup_ofFn.mpr Function.injective_id
  · ext i
    simp only [List.mem_toFinset, List.mem_append, Finset.mem_sort,
      List.mem_ofFn]
    constructor
    · intro _
      simp
    · intro _
      have hi : i ∈ P ∪ N ∪ Z := by rw [hcover]; simp
      simpa only [Finset.mem_union] using hi

private lemma reassemble_partition_refinements
    {m : ℕ} (x : Fin m → ℝ)
    (P N Z : Finset (Fin m))
    (hPN : Disjoint P N)
    (hPZ : Disjoint P Z)
    (hNZ : Disjoint N Z)
    (hcover : P ∪ N ∪ Z = Finset.univ)
    (pFine nFine zFine : List ℝ)
    (hp : RefinesByBlocks pFine ((P.sort (· ≤ ·)).map x))
    (hn : RefinesByBlocks nFine ((N.sort (· ≤ ·)).map x))
    (hz : RefinesByBlocks zFine ((Z.sort (· ≤ ·)).map x)) :
    ∃ fine : List ℝ,
      RefinesByBlocks fine (List.ofFn x) ∧
      fine.Perm (pFine ++ nFine ++ zFine) ∧
      fine.length - m =
        (pFine.length - P.card) +
        (nFine.length - N.card) +
        (zFine.length - Z.card) := by
  obtain ⟨pBlocks, hpLen, hpFlat, hpSum, hpNe⟩ := hp
  obtain ⟨nBlocks, hnLen, hnFlat, hnSum, hnNe⟩ := hn
  obtain ⟨zBlocks, hzLen, hzFlat, hzSum, hzNe⟩ := hz
  let baseBlocks := pBlocks ++ nBlocks ++ zBlocks
  have hindex := partition_sort_perm_ofFn P N Z hPN hPZ hNZ hcover
  have hcoarsePerm : (baseBlocks.map List.sum).Perm (List.ofFn x) := by
    have hmapped := hindex.map x
    simpa [baseBlocks, hpSum, hnSum, hzSum] using hmapped
  obtain ⟨blocks, hblocksPerm, hblocksSum⟩ :=
    perm_map_lift List.sum baseBlocks (List.ofFn x) hcoarsePerm
  let fine := blocks.flatten
  have hblocksLen : blocks.length = m := by
    have h := congrArg List.length hblocksSum
    simpa using h
  have hblocksNe : ∀ b ∈ blocks, b ≠ [] := by
    intro b hb
    have hbbase : b ∈ baseBlocks := hblocksPerm.mem_iff.mpr hb
    simp only [baseBlocks, List.mem_append] at hbbase
    rcases hbbase with (hb | hb) | hb
    · exact hpNe b hb
    · exact hnNe b hb
    · exact hzNe b hb
  have hflatPerm : baseBlocks.flatten.Perm fine := by
    exact hblocksPerm.flatten
  have hFinePerm : fine.Perm (pFine ++ nFine ++ zFine) := by
    apply hflatPerm.symm.trans
    simp only [baseBlocks, List.flatten_append, hpFlat, hnFlat, hzFlat]
    exact .refl _
  have hFineLen : fine.length = pFine.length + nFine.length + zFine.length := by
    have h := hflatPerm.length_eq
    simpa only [baseBlocks, List.flatten_append, hpFlat, hnFlat, hzFlat,
      List.length_append] using h.symm
  have hcards : P.card + N.card + Z.card = m := by
    have h := hindex.length_eq
    simpa only [List.length_append, Finset.length_sort, List.length_ofFn,
      Nat.add_assoc] using h
  have hpLe : P.card ≤ pFine.length := by
    simpa only [List.length_map, Finset.length_sort] using
      (length_le_of_refinesByBlocks
        (fine := pFine) (coarse := (P.sort (· ≤ ·)).map x)
        ⟨pBlocks, hpLen, hpFlat, hpSum, hpNe⟩)
  have hnLe : N.card ≤ nFine.length := by
    simpa only [List.length_map, Finset.length_sort] using
      (length_le_of_refinesByBlocks
        (fine := nFine) (coarse := (N.sort (· ≤ ·)).map x)
        ⟨nBlocks, hnLen, hnFlat, hnSum, hnNe⟩)
  have hzLe : Z.card ≤ zFine.length := by
    simpa only [List.length_map, Finset.length_sort] using
      (length_le_of_refinesByBlocks
        (fine := zFine) (coarse := (Z.sort (· ≤ ·)).map x)
        ⟨zBlocks, hzLen, hzFlat, hzSum, hzNe⟩)
  refine ⟨fine, ⟨blocks, by simpa using hblocksLen, rfl, hblocksSum, hblocksNe⟩,
    hFinePerm, ?_⟩
  omega

private lemma add_sub_one_eq_sub_one_add
    (a z : ℕ)
    (ha : 1 ≤ a) :
    a + z - 1 = (a - 1) + z := by
  omega

private lemma add_le_total_sub_one_of_le_sub_one
    (a z x : ℕ)
    (ha : 1 ≤ a)
    (hx : x ≤ a - 1) :
    x + z ≤ a + z - 1 := by
  rw [add_sub_one_eq_sub_one_add a z ha]
  exact Nat.add_le_add_right hx z

private lemma partition_cut_budget
    (p n z transportExtra halfExtra m : ℕ)
    (hnonempty : 1 ≤ p + n)
    (hcard : p + n + z = m)
    (htransport : transportExtra ≤ p + n - 1)
    (hhalf : halfExtra = z) :
    transportExtra + halfExtra ≤ m - 1 := by
  subst halfExtra
  subst m
  exact add_le_total_sub_one_of_le_sub_one
    (p + n) z transportExtra hnonempty htransport

private lemma ternary_support_budget {m : ℕ} (c : Fin m → ℤ)
    (hc : ∃ i, c i ≠ 0) :
    (Finset.univ.filter fun i => c i = 0).card +
        ((Finset.univ.filter fun i => c i ≠ 0).card - 1) = m - 1 := by
  let z : Finset (Fin m) := Finset.univ.filter fun i => c i = 0
  let s : Finset (Fin m) := Finset.univ.filter fun i => c i ≠ 0
  have hdisj : Disjoint z s := by
    rw [Finset.disjoint_left]
    simp [z, s]
  have hunion : z ∪ s = Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hi : c i = 0
    · left
      simp [z, hi]
    · right
      simp [s, hi]
  have hpart : z.card + s.card = m := by
    calc
      z.card + s.card = (z ∪ s).card := (Finset.card_union_of_disjoint hdisj).symm
      _ = Finset.univ.card := congrArg Finset.card hunion
      _ = m := by simp
  have hsupp : 1 ≤ s.card := by
    obtain ⟨i, hi⟩ := hc
    exact Finset.card_pos.mpr ⟨i, by simp [s, hi]⟩
  simpa only [z, s] using (by omega : z.card + (s.card - 1) = m - 1)

private lemma sum_map_finset_sort {α : Type*} [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    ((s.sort (· ≤ ·)).map f).sum = ∑ i ∈ s, f i := by
  have hp : (s.sort (· ≤ ·)).Perm s.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup _ _
    · exact Finset.nodup_toList s
    · ext i
      simp
  rw [(hp.map f).sum_eq]
  exact Finset.sum_map_toList s f

private lemma exists_paired_refinement_of_close_subsets
    {m : ℕ} (x : Fin m → ℝ)
    (hx : ∀ i, 0 < x i)
    (A B : Finset (Fin m)) (hAB : A ≠ B) :
    ∃ fine pairs residual : List ℝ,
      RefinesByBlocks fine (List.ofFn x) ∧
      (∀ y ∈ fine, 0 < y) ∧
      fine.Perm ((pairs.flatMap fun y => [y, y]) ++ residual) ∧
      (∀ y ∈ residual, 0 ≤ y) ∧
      fine.length - m ≤ m - 1 ∧
      residual.sum =
        |(∑ i ∈ A, x i) - ∑ i ∈ B, x i| := by
  let P := A \ B
  let N := B \ A
  let Z := Finset.univ \ (P ∪ N)
  obtain ⟨hPN, hPZ, hNZ, hcover, hnonempty, hcard⟩ :=
    close_subset_partition_facts A B hAB
  let pList := (P.sort (· ≤ ·)).map x
  let nList := (N.sort (· ≤ ·)).map x
  let zList := (Z.sort (· ≤ ·)).map x
  have hpPos : ∀ y ∈ pList, 0 < y := by
    intro y hy
    simp only [pList, List.mem_map, Finset.mem_sort] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hx i
  have hnPos : ∀ y ∈ nList, 0 < y := by
    intro y hy
    simp only [nList, List.mem_map, Finset.mem_sort] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hx i
  have hzPos : ∀ y ∈ zList, 0 < y := by
    intro y hy
    simp only [zList, List.mem_map, Finset.mem_sort] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hx i
  obtain ⟨LB, RB, pairs, residual, hLBlen, hRBlen, hLBsum, hRBsum,
      hblocks, hperm, hresnonneg, hressum, htransport⟩ :=
    paired_transport pList nList hpPos hnPos
  let pFine := LB.flatten
  let nFine := RB.flatten
  let zBlocks := zList.map (fun z => [z / 2, z / 2])
  let zFine := zBlocks.flatten
  have hpRef : RefinesByBlocks pFine pList := by
    refine ⟨LB, hLBlen, rfl, hLBsum, ?_⟩
    intro b hb
    exact (hblocks b (by simp [hb])).1
  have hnRef : RefinesByBlocks nFine nList := by
    refine ⟨RB, hRBlen, rfl, hRBsum, ?_⟩
    intro b hb
    exact (hblocks b (by simp [hb])).1
  have hzRef : RefinesByBlocks zFine zList := by
    refine ⟨zBlocks, by simp [zBlocks], rfl, ?_, ?_⟩
    · simp [zBlocks, Function.comp_def]
    · intro b hb
      simp only [zBlocks, List.mem_map] at hb
      obtain ⟨z, -, rfl⟩ := hb
      simp
  obtain ⟨fine, hFineRef, hFinePerm, hFineLen⟩ :=
    reassemble_partition_refinements x P N Z hPN hPZ hNZ hcover
      pFine nFine zFine (by simpa [pList] using hpRef)
      (by simpa [nList] using hnRef) (by simpa [zList] using hzRef)
  have hcorePerm : (pFine ++ nFine).Perm
      ((pairs.flatMap fun y => [y, y]) ++ residual) := by
    simpa [pFine, nFine] using hperm
  have hzFineEq : zFine = zList.flatMap (fun z => [z / 2, z / 2]) := by
    dsimp [zFine, zBlocks]
    induction zList with
    | nil => rfl
    | cons z zs ih => simp [ih]
  have hpairPerm : (pFine ++ nFine ++ zFine).Perm
      (((pairs ++ zList.map fun z => z / 2).flatMap fun y => [y, y]) ++
        residual) := by
    rw [hzFineEq]
    exact append_half_pairs_perm (pFine ++ nFine) pairs residual zList hcorePerm
  have hpFinePos : ∀ y ∈ pFine, 0 < y := by
    intro y hy
    simp only [pFine, List.mem_flatten] at hy
    obtain ⟨b, hb, hy⟩ := hy
    exact (hblocks b (by simp [hb])).2 y hy
  have hnFinePos : ∀ y ∈ nFine, 0 < y := by
    intro y hy
    simp only [nFine, List.mem_flatten] at hy
    obtain ⟨b, hb, hy⟩ := hy
    exact (hblocks b (by simp [hb])).2 y hy
  have hzFinePos : ∀ y ∈ zFine, 0 < y := by
    intro y hy
    simp only [zFine, zBlocks, List.mem_flatten, List.mem_map] at hy
    obtain ⟨b, ⟨z, hz, rfl⟩, hy⟩ := hy
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
    rcases hy with rfl | rfl
    · exact div_pos (hzPos z hz) (by norm_num)
    · exact div_pos (hzPos z hz) (by norm_num)
  have hFinePos : ∀ y ∈ fine, 0 < y := by
    intro y hy
    have hy' := hFinePerm.mem_iff.mp hy
    simp only [List.mem_append] at hy'
    rcases hy' with (hy' | hy') | hy'
    · exact hpFinePos y hy'
    · exact hnFinePos y hy'
    · exact hzFinePos y hy'
  have hpExcess : pFine.length - P.card =
      (LB.map (fun b => b.length - 1)).sum := by
    rw [show P.card = LB.length by simpa [pList] using hLBlen.symm]
    exact flatten_length_sub_length_eq_sum LB (by
      intro b hb
      exact (hblocks b (by simp [hb])).1)
  have hnExcess : nFine.length - N.card =
      (RB.map (fun b => b.length - 1)).sum := by
    rw [show N.card = RB.length by simpa [nList] using hRBlen.symm]
    exact flatten_length_sub_length_eq_sum RB (by
      intro b hb
      exact (hblocks b (by simp [hb])).1)
  have hzListLen : zList.length = Z.card := by simp [zList]
  have hzFineLen : zFine.length = 2 * zList.length := by
    rw [hzFineEq]
    induction zList with
    | nil => simp
    | cons z zs ih => simp [ih]; omega
  have hzExcess : zFine.length - Z.card = Z.card := by omega
  have hsupportPos : 1 ≤ P.card + N.card := by
    have hu : (P ∪ N).card = P.card + N.card := by
      rw [Finset.card_union_of_disjoint hPN]
    have hp : 0 < (P ∪ N).card := by
      exact Finset.card_pos.mpr hnonempty
    omega
  have htransport' :
      (LB.map (fun b => b.length - 1)).sum +
          (RB.map (fun b => b.length - 1)).sum ≤ P.card + N.card - 1 := by
    simpa [pList, nList] using htransport
  have hbudget : fine.length - m ≤ m - 1 := by
    rw [hFineLen, hpExcess, hnExcess, hzExcess]
    exact partition_cut_budget P.card N.card Z.card
      ((LB.map (fun b => b.length - 1)).sum +
        (RB.map (fun b => b.length - 1)).sum) Z.card m
      hsupportPos hcard htransport' rfl
  have hsumIdentity : pList.sum - nList.sum =
      (∑ i ∈ A, x i) - ∑ i ∈ B, x i := by
    rw [show pList.sum = ∑ i ∈ P, x i by
      exact sum_map_finset_sort P x]
    rw [show nList.sum = ∑ i ∈ N, x i by
      exact sum_map_finset_sort N x]
    exact (subset_sum_difference_sdiff x A B).symm
  refine ⟨fine, pairs ++ zList.map (fun z => z / 2), residual,
    hFineRef, hFinePos, hFinePerm.trans hpairPerm, hresnonneg, hbudget, ?_⟩
  rw [hressum, hsumIdentity]

private lemma exists_budgeted_paired_refinement
    (N : ℕ) (hN : 1 ≤ N) (coarse : List ℝ)
    (hlen : coarse.length ≤ N + 1)
    (hpos : ∀ x ∈ coarse, 0 < x)
    (hsum : coarse.sum = 1) :
    ∃ fine pairs residual : List ℝ,
      RefinesByBlocks fine coarse ∧
      (∀ x ∈ fine, 0 < x) ∧
      fine.Perm ((pairs.flatMap fun x => [x, x]) ++ residual) ∧
      (∀ x ∈ residual, 0 ≤ x) ∧
      fine.length - coarse.length ≤ N ∧
      residual.sum ≤ 1 / ((2 : ℝ) ^ (N + 1) - 1) := by
  by_cases hsmall : coarse.length ≤ N
  · obtain ⟨fine, pairs, href, hfpos, hfine, hexcess⟩ :=
      half_pair_refinement_exact coarse hpos
    refine ⟨fine, pairs, [], href, hfpos, ?_, by simp, ?_, ?_⟩
    · simp [hfine]
    · omega
    · simp
      exact one_le_pow₀ (by norm_num)
  · have hm : coarse.length = N + 1 := by omega
    let x : Fin coarse.length → ℝ := fun i => coarse.get i
    have hx : ∀ i, 0 < x i := by
      intro i
      exact hpos (x i) (by simp [x])
    have hsumx : ∑ i, x i = 1 := by
      simpa [x] using hsum
    obtain ⟨A, B, hAB, hclose⟩ :=
      exists_distinct_subset_sums_close x (by omega) (fun i => (hx i).le) hsumx
    obtain ⟨fine, pairs, residual, href, hfpos, hperm, hrnonneg,
        hbudget, hrsum⟩ :=
      exists_paired_refinement_of_close_subsets x hx A B hAB
    refine ⟨fine, pairs, residual, ?_, hfpos, hperm, hrnonneg, ?_, ?_⟩
    · simpa [x] using href
    · simpa [hm] using hbudget
    · rw [hrsum]
      simpa [hm] using hclose

private lemma alternatingImbalance_flatMap_duplicate (xs : List ℝ) :
    alternatingImbalance (xs.flatMap fun x => [x, x]) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [alternatingImbalance, ih]

private lemma alternatingImbalance_duplicate_singleton_duplicate
    (before after : List ℝ) (δ : ℝ) :
    alternatingImbalance
      ((before.flatMap fun x => [x, x]) ++
        δ :: (after.flatMap fun x => [x, x])) = δ := by
  induction before with
  | nil =>
      simp only [List.flatMap_nil, List.nil_append]
      rw [alternatingImbalance_cons, alternatingImbalance_flatMap_duplicate]
      ring
  | cons x before ih => simp [alternatingImbalance, ih]

private lemma ordered_adjacent_pair_cost_le_arbitrary_pairing
    (a b c d : ℝ) (hab : b ≤ a) (hbc : c ≤ b) (hcd : d ≤ c) :
    |a - b| + |c - d| ≤ |a - c| + |b - d| ∧
      |a - b| + |c - d| ≤ |a - d| + |b - c| := by
  have hab' : 0 ≤ a - b := sub_nonneg.mpr hab
  have hcd' : 0 ≤ c - d := sub_nonneg.mpr hcd
  have hac' : 0 ≤ a - c := sub_nonneg.mpr (le_trans hbc hab)
  have hbd' : 0 ≤ b - d := sub_nonneg.mpr (le_trans hcd hbc)
  have had' : 0 ≤ a - d := sub_nonneg.mpr (le_trans hcd (le_trans hbc hab))
  have hbc' : 0 ≤ b - c := sub_nonneg.mpr hbc
  rw [abs_of_nonneg hab', abs_of_nonneg hcd', abs_of_nonneg hac',
    abs_of_nonneg hbd', abs_of_nonneg had', abs_of_nonneg hbc']
  constructor <;> linarith

private lemma alternatingImbalance_map_mul
    (a : ℝ) (xs : List ℝ) :
    alternatingImbalance (xs.map (fun x => a * x)) =
      a * alternatingImbalance xs := by
  induction xs using List.twoStepInduction with
  | nil => simp [alternatingImbalance]
  | singleton x => simp [alternatingImbalance]
  | cons_cons x y xs ih =>
      simp only [List.map_cons, alternatingImbalance]
      rw [ih]
      ring

private lemma alternatingImbalance_cons_flatMap_pairs
    (δ : ℝ) (ps : List (ℝ × ℝ)) :
    alternatingImbalance (δ :: ps.flatMap fun p => [p.1, p.2]) =
      δ + (ps.map fun p => p.2 - p.1).sum := by
  induction ps generalizing δ with
  | nil => simp [alternatingImbalance]
  | cons p ps ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      change δ - p.1 + alternatingImbalance
        (p.2 :: ps.flatMap fun q => [q.1, q.2]) =
          δ + (p.2 - p.1 + (ps.map fun q => q.2 - q.1).sum)
      rw [ih]
      ring

private lemma alternatingImbalance_duplicate_prefix_le_residual_sum
    (pairs residual : List ℝ) (hres : ∀ x ∈ residual, 0 ≤ x) :
    alternatingImbalance
        ((pairs.flatMap fun x => [x, x]) ++ residual) ≤ residual.sum := by
  have hle : ∀ ys : List ℝ, (∀ y ∈ ys, 0 ≤ y) →
      alternatingImbalance ys ≤ ys.sum := by
    intro ys hys
    induction ys using List.twoStepInduction with
    | nil => simp [alternatingImbalance]
    | singleton y => simp [alternatingImbalance]
    | cons_cons y z ys ih =>
        simp only [alternatingImbalance, List.sum_cons]
        have hz : 0 ≤ z := hys z (by simp)
        have hi := ih (by
          intro w hw
          exact hys w (by simp [hw]))
        linarith
  induction pairs with
  | nil => simpa using hle residual hres
  | cons x pairs ih =>
      simpa [alternatingImbalance] using ih

private lemma two_mul_answer_sub_one {n : ℕ+} :
    2 * answer n - 1 =
      1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) := by
  rw [answer_eq_half_one_add_inv]
  ring

private lemma mergeSort_flatMap_duplicate (xs : List ℝ) :
    (xs.flatMap fun x => [x, x]).mergeSort (· ≥ ·) =
      (xs.mergeSort (· ≥ ·)).flatMap fun x => [x, x] := by
  have hp :
      ((xs.flatMap fun x => [x, x]).mergeSort (· ≥ ·)).Perm
        ((xs.mergeSort (· ≥ ·)).flatMap fun x => [x, x]) :=
    (List.mergeSort_perm _ _).trans
      ((List.mergeSort_perm xs (· ≥ ·)).flatMap
        (fun x _ => List.Perm.refl [x, x])).symm
  have htrans : ∀ a b c : ℝ,
      decide (a ≥ b) = true → decide (b ≥ c) = true →
        decide (a ≥ c) = true := by
    simp only [decide_eq_true_eq]
    exact fun _ _ _ hab hbc => le_trans hbc hab
  have htotal : ∀ a b : ℝ,
      (decide (a ≥ b) || decide (b ≥ a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact le_total b a
  apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
  · intro a b _ _ hab hba
    exact le_antisymm hba hab
  · simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort htrans htotal (xs.flatMap fun x => [x, x])
  · rw [List.pairwise_flatMap]
    constructor
    · intro x hx
      simp
    · have hs : List.Pairwise (· ≥ ·) (xs.mergeSort (· ≥ ·)) := by
        simpa only [decide_eq_true_eq] using
          List.pairwise_mergeSort htrans htotal xs
      exact hs.imp (by
        intro a b hab x hx y hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
          or_false] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> exact hab)
  · exact hp

private lemma halfPair_refinesByBlocks (coarse : List ℝ) :
    RefinesByBlocks (coarse.flatMap fun x => [x / 2, x / 2]) coarse := by
  refine ⟨coarse.map (fun x => [x / 2, x / 2]), by simp, ?_, ?_, by simp⟩
  · induction coarse with
    | nil => rfl
    | cons x xs ih => simp [ih]
  · induction coarse with
    | nil => rfl
    | cons x xs ih =>
        simp only [List.map_cons, Function.comp_apply, List.sum_cons, List.sum_nil]
        rw [ih]
        congr 1
        ring

private lemma sorted_alternatingImbalance_le_residual_sum
    (xs pairs residual : List ℝ)
    (hsorted : List.Pairwise (· ≥ ·) xs)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x)
    (hperm : xs.Perm
      ((pairs.flatMap fun x => [x, x]) ++ residual))
    (hres : ∀ x ∈ residual, 0 ≤ x) :
    alternatingImbalance xs ≤ residual.sum := by
  have hbounds : ∀ (ys : List ℝ) (u : ℝ), 0 ≤ u →
      List.Pairwise (· ≥ ·) ys →
      (∀ y ∈ ys, 0 ≤ y) → (∀ y ∈ ys, y ≤ u) →
      0 ≤ alternatingImbalance ys ∧ alternatingImbalance ys ≤ u := by
    intro ys
    induction ys using List.twoStepInduction with
    | nil => intro u hu _ _ _; simpa [alternatingImbalance]
    | singleton y =>
        intro u _ _ hy hu
        simp only [alternatingImbalance]
        exact ⟨hy y (by simp), hu y (by simp)⟩
    | cons_cons y z ys ih =>
        intro u hu hs hp hub
        simp only [List.pairwise_cons] at hs
        have hyz : z ≤ y := hs.1 z (by simp)
        have hs' : List.Pairwise (· ≥ ·) ys := hs.2.2
        have hz0 := hp z (by simp)
        have hi := ih z hz0 hs'
          (fun w hw => hp w (by simp [hw]))
          (fun w hw => hs.2.1 w hw)
        have hyu := hub y (by simp)
        simp only [alternatingImbalance]
        constructor <;> linarith
  have herase : ∀ (ys : List ℝ) (a : ℝ),
      List.Pairwise (· ≥ ·) ys → (∀ y ∈ ys, 0 ≤ y) → a ∈ ys →
      |alternatingImbalance ys - alternatingImbalance (ys.erase a)| ≤ a := by
    intro ys
    induction ys with
    | nil => simp
    | cons x ys ih =>
        intro a hs hp ha
        simp only [List.pairwise_cons] at hs
        by_cases hxa : x = a
        · subst x
          have ha0 := hp a (by simp)
          have hb := hbounds ys a ha0 hs.2
            (fun w hw => hp w (by simp [hw])) hs.1
          rw [List.erase_cons_head]
          rw [alternatingImbalance_cons]
          apply (abs_le).2
          constructor <;> linarith
        · have hax : a ≠ x := Ne.symm hxa
          have ha' : a ∈ ys := by simpa [hax] using ha
          have hi := ih a hs.2 (fun w hw => hp w (by simp [hw])) ha'
          simp only [List.erase]
          rw [show (x == a) = false by simp [hxa]]
          simp only [alternatingImbalance_cons]
          have hid : x - alternatingImbalance ys -
              (x - alternatingImbalance (ys.erase a)) =
              -(alternatingImbalance ys -
                alternatingImbalance (ys.erase a)) := by ring
          rw [hid, abs_neg]
          exact hi
  induction residual generalizing xs with
  | nil =>
      simp only [List.append_nil, List.sum_nil] at hperm ⊢
      have htrans : ∀ a b c : ℝ,
          decide (a ≥ b) = true → decide (b ≥ c) = true →
            decide (a ≥ c) = true := by
        simp only [decide_eq_true_eq]
        exact fun _ _ _ hab hbc => le_trans hbc hab
      have htotal : ∀ a b : ℝ,
          (decide (a ≥ b) || decide (b ≥ a)) = true := by
        intro a b
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total b a
      let dup := pairs.flatMap fun x => [x, x]
      have hsdup : List.Pairwise (· ≥ ·) (dup.mergeSort (· ≥ ·)) := by
        simpa only [decide_eq_true_eq] using
          List.pairwise_mergeSort htrans htotal dup
      have heq : xs = dup.mergeSort (· ≥ ·) := by
        apply List.Perm.eq_of_pairwise (le := (· ≥ ·))
        · intro a b _ _ hab hba
          exact le_antisymm hba hab
        · exact hsorted
        · exact hsdup
        · exact hperm.trans (List.mergeSort_perm dup (· ≥ ·)).symm
      rw [heq]
      dsimp [dup]
      rw [mergeSort_flatMap_duplicate,
        alternatingImbalance_flatMap_duplicate]
  | cons r residual ih =>
      have hrmemR : r ∈ (pairs.flatMap fun x => [x, x]) ++ r :: residual := by
        simp
      have hrmem : r ∈ xs := hperm.mem_iff.mpr hrmemR
      let ys := xs.erase r
      have hysorted : List.Pairwise (· ≥ ·) ys := hsorted.erase _
      have hynonneg : ∀ y ∈ ys, 0 ≤ y := by
        intro y hy
        exact hnonneg y (List.mem_of_mem_erase hy)
      have hmove : ((pairs.flatMap fun x => [x, x]) ++ r :: residual).Perm
          (r :: (pairs.flatMap fun x => [x, x]) ++ residual) := by
        have h₁ : ((pairs.flatMap fun x => [x, x]) ++ r :: residual).Perm
            ((r :: residual) ++ (pairs.flatMap fun x => [x, x])) :=
          List.perm_append_comm
        have h₂ : (residual ++ (pairs.flatMap fun x => [x, x])).Perm
            ((pairs.flatMap fun x => [x, x]) ++ residual) :=
          List.perm_append_comm
        exact h₁.trans (h₂.cons r)
      have hyperm : ys.Perm
          ((pairs.flatMap fun x => [x, x]) ++ residual) := by
        exact List.Perm.cons_inv
          ((List.perm_cons_erase hrmem).symm.trans (hperm.trans hmove))
      have hi := ih ys hysorted hynonneg hyperm
        (fun y hy => hres y (by simp [hy]))
      have he := herase xs r hsorted hnonneg hrmem
      have he' := (abs_le.mp he).2
      simp only [List.sum_cons]
      dsimp [ys] at hi
      linarith

private lemma finset_card_sdiff_probe {α : Type} [DecidableEq α]
    (A B : Finset α) (hBA : B ⊆ A) : #(A \ B) = #A - #B := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBA]

private lemma prefix_sum_adjacent_sub (fine : List ℝ) (i : ℕ)
    (hi : i < fine.length) :
    (fine.take (i + 1)).sum - (fine.take i).sum = fine[i] := by
  rw [List.sum_take_succ _ _ hi]
  ring

private lemma card_internal_prefix_sdiff
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (e : Fin (fine.length - 1) ↪ Set.Ioo (0 : ℝ) 1)
    (hsub : s.points ⊆ Finset.univ.map e)
    (hlen : (physicalPieces s
      (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length ≤ fine.length) :
    #((Finset.univ.map e) \ s.points) =
      fine.length -
        (physicalPieces s
          (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length := by
  rw [finset_card_sdiff_probe _ _ hsub]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin,
    physicalPieces_length, Finset.card_empty, add_zero]
  omega

private lemma exists_internal_prefix_sum_embedding
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (href : RefinesByBlocks fine
      (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))))
    (hpos : ∀ x ∈ fine, 0 < x) :
    ∃ e : Fin (fine.length - 1) ↪ Set.Ioo (0 : ℝ) 1,
      ∀ i, ((e i : Set.Ioo (0 : ℝ) 1) : ℝ) =
        (fine.take ((i : ℕ) + 1)).sum := by
  have hsum : fine.sum = 1 := by
    rw [sum_eq_of_refinesByBlocks href]
    exact physicalPieces_sum s ∅ (by simp)
  have hmem : ∀ i, i + 1 < fine.length →
      (fine.take (i + 1)).sum ∈ Set.Ioo (0 : ℝ) fine.sum := by
    intro i hi
    have htpos : 0 < (fine.take (i + 1)).sum := by
      apply List.sum_pos (fine.take (i + 1))
      · intro x hx
        exact hpos x (List.mem_of_mem_take hx)
      · have hfine : fine ≠ [] := by
          intro he
          simp [he] at hi
        simp [hfine]
    have hdpos : 0 < (fine.drop (i + 1)).sum := by
      apply List.sum_pos (fine.drop (i + 1))
      · intro x hx
        exact hpos x (List.mem_of_mem_drop hx)
      · simpa using hi
    have hsplit := List.sum_take_add_sum_drop fine (i + 1)
    exact ⟨htpos, by linarith⟩
  have hstrict : ∀ {a b : ℕ}, a < b → b ≤ fine.length →
      (fine.take a).sum < (fine.take b).sum := by
    intro a b hab hb
    have hdpos : 0 < ((fine.take b).drop a).sum := by
      apply List.sum_pos ((fine.take b).drop a)
      · intro x hx
        exact hpos x (List.mem_of_mem_take (List.mem_of_mem_drop hx))
      · simpa [List.length_take, hb] using hab
    have hsplit := List.sum_take_add_sum_drop (fine.take b) a
    have htake : (fine.take b).take a = fine.take a := by
      rw [List.take_take, min_eq_left hab.le]
    rw [htake] at hsplit
    linarith
  let f : Fin (fine.length - 1) → Set.Ioo (0 : ℝ) 1 := fun i =>
    ⟨(fine.take ((i : ℕ) + 1)).sum, by
      have hm := hmem (i : ℕ) (by omega)
      rwa [hsum] at hm⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hijlt | hjilt
    · have hs := hstrict (a := (i : ℕ) + 1) (b := (j : ℕ) + 1)
          (by omega) (by omega)
      have heq := congrArg (fun z : Set.Ioo (0 : ℝ) 1 => (z : ℝ)) hij
      dsimp [f] at heq
      linarith
    · have hs := hstrict (a := (j : ℕ) + 1) (b := (i : ℕ) + 1)
          (by omega) (by omega)
      have heq := congrArg (fun z : Set.Ioo (0 : ℝ) 1 => (z : ℝ)) hij
      dsimp [f] at heq
      linarith
  · intro i
    rfl

private lemma exists_internal_boundary_of_refinesByBlocks
    {fine coarse : List ℝ} (href : RefinesByBlocks fine coarse)
    {k : ℕ} (hk0 : 0 < k) (hk : k < coarse.length) :
    ∃ j : ℕ, 0 < j ∧ j < fine.length ∧
      (fine.take j).sum = (coarse.take k).sum := by
  obtain ⟨blocks, hlen, hflat, hsum, hne⟩ := href
  let j := (blocks.take k).flatten.length
  have hkblocks : k < blocks.length := by omega
  have htake_len : (blocks.take k).length = k := by simp [hkblocks.le]
  have hp_le : (blocks.take k).length ≤ (blocks.take k).flatten.length :=
    length_le_flatten_length_of_ne_nil _
      (fun b hb => hne b (List.mem_of_mem_take hb))
  have hj0 : 0 < j := by
    dsimp [j]
    omega
  have hdrop_le : (blocks.drop k).length ≤ (blocks.drop k).flatten.length :=
    length_le_flatten_length_of_ne_nil _
      (fun b hb => hne b (List.mem_of_mem_drop hb))
  have hdrop_pos : 0 < (blocks.drop k).length := by simp [hkblocks]
  have hdecomp : blocks.flatten =
      (blocks.take k).flatten ++ (blocks.drop k).flatten := by
    rw [← List.flatten_append, List.take_append_drop]
  have hjlt : j < fine.length := by
    rw [← hflat, hdecomp]
    simp only [List.length_append]
    dsimp [j]
    omega
  refine ⟨j, hj0, hjlt, ?_⟩
  rw [← hflat, ← hsum]
  have htake : blocks.flatten.take j = (blocks.take k).flatten := by
    rw [hdecomp]
    dsimp [j]
    simp
  rw [htake, List.sum_flatten]
  simp

private lemma strategy_points_subset_internal_prefix_range
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (href : RefinesByBlocks fine
      (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))))
    (e : Fin (fine.length - 1) ↪ Set.Ioo (0 : ℝ) 1)
    (he : ∀ i, ((e i : Set.Ioo (0 : ℝ) 1) : ℝ) =
      (fine.take ((i : ℕ) + 1)).sum) :
    s.points ⊆ Finset.univ.map e := by
  intro x hx
  have hd : Disjoint s.points (∅ : Finset (Set.Ioo (0 : ℝ) 1)) := by simp
  have hxend : (x : ℝ) ∈ s.playEnds (∅ : Finset (Set.Ioo (0 : ℝ) 1)) := by
    simp only [Strategy.playEnds, Finset.mem_sort, Finset.mem_union,
      Finset.mem_map, Finset.mem_insert, Finset.mem_singleton]
    left
    exact ⟨x, Or.inl hx, rfl⟩
  let k := (s.playEnds (∅ : Finset (Set.Ioo (0 : ℝ) 1))).idxOf (x : ℝ)
  have hkEnds : k < (s.playEnds
      (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length :=
    List.idxOf_lt_length_iff.mpr hxend
  have hkget : (s.playEnds (∅ : Finset (Set.Ioo (0 : ℝ) 1))).getD k 0 =
      (x : ℝ) := by
    dsimp [k]
    rw [List.getD_eq_getElem _ _ hkEnds, List.getElem_idxOf hkEnds]
  have hlenEnds := playEnds_length s
    (∅ : Finset (Set.Ioo (0 : ℝ) 1)) hd
  simp only [Finset.card_empty, add_zero] at hlenEnds
  have hk0 : 0 < k := by
    by_contra h
    have hkz : k = 0 := by omega
    rw [hkz, playEnds_getD_zero] at hkget
    exact (ne_of_gt x.2.1) hkget.symm
  have hklast : k < #s.points + 1 := by
    have hkle : k ≤ #s.points + 1 := by omega
    apply lt_of_le_of_ne hkle
    intro hkeq
    have hlast : (s.playEnds (∅ : Finset (Set.Ioo (0 : ℝ) 1))).getD
        (#s.points + 1) 0 = 1 := by
      simpa using playEnds_getD_last s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1)) hd
    rw [← hkeq, hkget] at hlast
    exact (ne_of_lt x.2.2) hlast
  have hkcoarse : k < (physicalPieces s
      (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length := by
    rw [physicalPieces_length]
    simpa using hklast
  have hprefix : ((physicalPieces s
      (∅ : Finset (Set.Ioo (0 : ℝ) 1))).take k).sum = (x : ℝ) := by
    have hs := physicalPieces_slice_sum (a := 0) (b := k) s
      (∅ : Finset (Set.Ioo (0 : ℝ) 1)) (Nat.zero_le _) (by omega)
    simp only [List.drop_zero, Nat.sub_zero] at hs
    rw [playEnds_getD_zero, hkget] at hs
    linarith
  obtain ⟨j, hj0, hjlt, hj⟩ :=
    exists_internal_boundary_of_refinesByBlocks href hk0 hkcoarse
  have hsum : (fine.take j).sum = (x : ℝ) := hj.trans hprefix
  let i : Fin (fine.length - 1) := ⟨j - 1, by omega⟩
  have hij : (i : ℕ) + 1 = j := by
    dsimp [i]
    omega
  rw [Finset.mem_map]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  rw [he, hij, hsum]

private lemma prefix_cut_union_complement_restore
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (e : Fin (fine.length - 1) ↪ Set.Ioo (0 : ℝ) 1)
    (hsub : s.points ⊆ Finset.univ.map e) :
    s.points ∪ ((Finset.univ.map e) \ s.points) = Finset.univ.map e := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hx | ⟨hx, _⟩)
    · exact hsub hx
    · exact hx
  · intro hx
    by_cases hp : x ∈ s.points
    · exact Or.inl hp
    · exact Or.inr ⟨hx, hp⟩

private lemma playEnds_missing_prefix_cuts_eq_prefixSums
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (href : RefinesByBlocks fine
      (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))))
    (hpos : ∀ x ∈ fine, 0 < x)
    (e : Fin (fine.length - 1) ↪ Set.Ioo (0 : ℝ) 1)
    (he : ∀ i, ((e i : Set.Ioo (0 : ℝ) 1) : ℝ) =
      (fine.take ((i : ℕ) + 1)).sum)
    (hsub : s.points ⊆ Finset.univ.map e) :
    s.playEnds ((Finset.univ.map e) \ s.points) =
      List.ofFn (fun i : Fin (fine.length + 1) =>
        (fine.take (i : ℕ)).sum) := by
  rw [Strategy.playEnds, prefix_cut_union_complement_restore s fine e hsub]
  let L := List.ofFn (fun i : Fin (fine.length + 1) =>
    (fine.take (i : ℕ)).sum)
  have hsum : fine.sum = 1 := by
    rw [sum_eq_of_refinesByBlocks href]
    exact physicalPieces_sum s ∅ (by simp)
  have hstrict : ∀ {a b : ℕ}, a < b → b ≤ fine.length →
      (fine.take a).sum < (fine.take b).sum := by
    intro a b hab hb
    have hdpos : 0 < ((fine.take b).drop a).sum := by
      apply List.sum_pos ((fine.take b).drop a)
      · intro x hx
        exact hpos x (List.mem_of_mem_take (List.mem_of_mem_drop hx))
      · simpa [List.length_take, hb] using hab
    have hsplit := List.sum_take_add_sum_drop (fine.take b) a
    have htake : (fine.take b).take a = fine.take a := by
      rw [List.take_take, min_eq_left hab.le]
    rw [htake] at hsplit
    linarith
  have hpairLT : L.Pairwise (· < ·) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simpa only [L, List.get_ofFn, Fin.val_cast] using
      hstrict (show (i : ℕ) < (j : ℕ) from hij) (by
        have hj := j.isLt
        simpa [L] using hj)
  have hfin : L.toFinset =
      (Finset.univ.map e).map (Function.Embedding.subtype _) ∪ {0, 1} := by
    ext x
    simp only [List.mem_toFinset, L, List.mem_ofFn, Finset.mem_union,
      Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      by_cases hi0 : (i : ℕ) = 0
      · right; left; simp [hi0]
      by_cases hilast : (i : ℕ) = fine.length
      · right; right; simp [hilast, hsum]
      · left
        let j : Fin (fine.length - 1) := ⟨(i : ℕ) - 1, by omega⟩
        refine ⟨e j, ⟨j, rfl⟩, ?_⟩
        change ((e j : Set.Ioo (0 : ℝ) 1) : ℝ) = _
        rw [he]
        congr 2
        dsimp [j]
        omega
    · rintro (⟨y, ⟨i, rfl⟩, rfl⟩ | rfl | rfl)
      · refine ⟨⟨(i : ℕ) + 1, by omega⟩, ?_⟩
        change _ = ((e i : Set.Ioo (0 : ℝ) 1) : ℝ)
        rw [he]
      · exact ⟨⟨0, by omega⟩, by simp⟩
      · refine ⟨⟨fine.length, by omega⟩, ?_⟩
        simp [hsum]
  rw [← hfin]
  exact (List.toFinset_sort (· ≤ ·) hpairLT.nodup).mpr
    (hpairLT.imp (fun h : (_ < _) => le_of_lt h))

private lemma physicalPieces_eq_of_playEnds_eq_prefixSums
    {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (fine : List ℝ)
    (hd : Disjoint s.points xiangPoints)
    (hends : s.playEnds xiangPoints =
      List.ofFn (fun i : Fin (fine.length + 1) =>
        (fine.take (i : ℕ)).sum)) :
    physicalPieces s xiangPoints = fine := by
  have hadj :
      List.ofFn (fun i : Fin fine.length =>
        (List.ofFn (fun j : Fin (fine.length + 1) =>
          (fine.take (j : ℕ)).sum)).getD ((i : ℕ) + 1) 0 -
        (List.ofFn (fun j : Fin (fine.length + 1) =>
          (fine.take (j : ℕ)).sum)).getD (i : ℕ) 0) = fine := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp only [List.getElem_ofFn]
      rw [List.getD_eq_getElem, List.getD_eq_getElem]
      · rw [List.getElem_ofFn, List.getElem_ofFn]
        exact prefix_sum_adjacent_sub fine i hi₂
      · simp only [List.length_ofFn]
        omega
      · simp only [List.length_ofFn]
        omega
  have hcard : #s.points + #xiangPoints + 1 = fine.length := by
    have h := congrArg List.length hends
    rw [playEnds_length s xiangPoints hd] at h
    simp only [List.length_ofFn] at h
    omega
  simp only [physicalPieces, Strategy.playPieceLength]
  rw [hcard, hends]
  exact hadj

private lemma physicalPieces_prefix_sum_eq_playEnd {n k : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hk : k ≤ #s.points + #xiangPoints + 1) :
    ((physicalPieces s xiangPoints).take k).sum =
      (s.playEnds xiangPoints).getD k 0 := by
  have h := physicalPieces_slice_sum s xiangPoints (a := 0) (b := k)
    (Nat.zero_le k) hk
  rw [playEnds_getD_zero] at h
  simpa using h

private lemma exists_xiangPoints_realizing_positive_refinement
    {n : ℕ} (s : Strategy n) (fine : List ℝ)
    (href : RefinesByBlocks fine
      (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))))
    (hpos : ∀ x ∈ fine, 0 < x) :
    ∃ xiangPoints : Finset (Set.Ioo (0 : ℝ) 1),
      Disjoint s.points xiangPoints ∧
      #xiangPoints = fine.length -
        (physicalPieces s
          (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length ∧
      physicalPieces s xiangPoints = fine := by
  obtain ⟨e, he⟩ := exists_internal_prefix_sum_embedding s fine href hpos
  have hsub : s.points ⊆ Finset.univ.map e :=
    strategy_points_subset_internal_prefix_range s fine href e he
  let xiangPoints := (Finset.univ.map e) \ s.points
  have hd : Disjoint s.points xiangPoints := by
    rw [Finset.disjoint_left]
    intro x hxs hx
    exact (Finset.mem_sdiff.mp hx).2 hxs
  have hcard : #xiangPoints = fine.length -
      (physicalPieces s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length := by
    dsimp [xiangPoints]
    exact card_internal_prefix_sdiff s fine e hsub
      (length_le_of_refinesByBlocks href)
  have hends : s.playEnds xiangPoints =
      List.ofFn (fun i : Fin (fine.length + 1) =>
        (fine.take (i : ℕ)).sum) := by
    dsimp [xiangPoints]
    exact playEnds_missing_prefix_cuts_eq_prefixSums
      s fine href hpos e he hsub
  refine ⟨xiangPoints, hd, hcard, ?_⟩
  exact physicalPieces_eq_of_playEnds_eq_prefixSums
    s xiangPoints fine hd hends

private lemma residual_threshold_eq_two_mul_answer_sub_one
    {n : ℕ+} :
    1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) =
      2 * answer n - 1 := by
  rw [answer_eq_half_one_add_inv]
  ring

private lemma static_board_of_budgeted_paired_refinement
    {n : ℕ+} (s : Strategy n)
    (fine pairs residual : List ℝ)
    (href : RefinesByBlocks fine
      (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))))
    (hpos : ∀ x ∈ fine, 0 < x)
    (hperm : fine.Perm
      ((pairs.flatMap fun x => [x, x]) ++ residual))
    (hres0 : ∀ x ∈ residual, 0 ≤ x)
    (hbudget : fine.length -
      (physicalPieces s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length ≤ (n : ℕ))
    (hsmall : residual.sum ≤
      1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    ∃ xiangPoints : Finset (Set.Ioo (0 : ℝ) 1),
      #xiangPoints ≤ n ∧
      Disjoint s.points xiangPoints ∧
      alternatingImbalance
        ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
          2 * answer n - 1 := by
  obtain ⟨xiangPoints, hd, hcard, hpieces⟩ :=
    exists_xiangPoints_realizing_positive_refinement s fine href hpos
  refine ⟨xiangPoints, ?_, hd, ?_⟩
  · rw [hcard]
    exact hbudget
  · rw [hpieces]
    have htrans : ∀ a b c : ℝ,
        decide (a ≥ b) = true → decide (b ≥ c) = true →
          decide (a ≥ c) = true := by
      simp only [decide_eq_true_eq]
      exact fun _ _ _ hab hbc => le_trans hbc hab
    have htotal : ∀ a b : ℝ,
        (decide (a ≥ b) || decide (b ≥ a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total b a
    have hsorted : List.Pairwise (· ≥ ·)
        (fine.mergeSort (· ≥ ·)) := by
      simpa only [decide_eq_true_eq] using
        List.pairwise_mergeSort htrans htotal fine
    have hnonneg : ∀ x ∈ fine.mergeSort (· ≥ ·), 0 ≤ x := by
      intro x hx
      apply le_of_lt (hpos x ?_)
      exact (List.mergeSort_perm fine (· ≥ ·)).mem_iff.mp hx
    have hperm' : (fine.mergeSort (· ≥ ·)).Perm
        ((pairs.flatMap fun x => [x, x]) ++ residual) :=
      (List.mergeSort_perm fine (· ≥ ·)).trans hperm
    calc
      alternatingImbalance (fine.mergeSort (· ≥ ·)) ≤ residual.sum :=
        sorted_alternatingImbalance_le_residual_sum
          _ _ _ hsorted hnonneg hperm' hres0
      _ ≤ 1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) := hsmall
      _ = 2 * answer n - 1 :=
        residual_threshold_eq_two_mul_answer_sub_one

private lemma empty_board_physicalPieces_data
    {n : ℕ+} (s : Strategy n) :
    (physicalPieces s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length ≤ (n : ℕ) + 1 ∧
      (∀ x ∈ physicalPieces s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1)), 0 < x) ∧
      (physicalPieces s
        (∅ : Finset (Set.Ioo (0 : ℝ) 1))).sum = 1 := by
  simpa [physicalPieces_length] using
    And.intro (Nat.add_le_add_right s.card_points_le 1)
      (And.intro (physicalPieces_pos s ∅ (by simp))
        (physicalPieces_sum s ∅ (by simp)))

private lemma exists_strategy_budgeted_paired_refinement
    {n : ℕ+} (s : Strategy n) :
    ∃ fine pairs residual : List ℝ,
      RefinesByBlocks fine
        (physicalPieces s (∅ : Finset (Set.Ioo (0 : ℝ) 1))) ∧
      (∀ x ∈ fine, 0 < x) ∧
      fine.Perm ((pairs.flatMap fun x => [x, x]) ++ residual) ∧
      (∀ x ∈ residual, 0 ≤ x) ∧
      fine.length -
          (physicalPieces s
            (∅ : Finset (Set.Ioo (0 : ℝ) 1))).length ≤ (n : ℕ) ∧
      residual.sum ≤
        1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1) := by
  obtain ⟨hlen, hpos, hsum⟩ := empty_board_physicalPieces_data s
  exact exists_budgeted_paired_refinement (n : ℕ) n.pos _ hlen hpos hsum

private lemma sequential_reduction_family_residual_gt
    (u : ℝ) (hu_lower : -(1 : ℝ) / 6 < u)
    (hu_upper : u < (5 : ℝ) / 32) :
    (26 + u) / 31 < min (1 + u) (1 - u) := by
  rw [lt_min_iff]
  constructor <;> linarith

private lemma exists_static_sorted_board_alternating_bound
    {n : ℕ+} (s : Strategy n) :
    ∃ xiangPoints : Finset (Set.Ioo (0 : ℝ) 1),
      #xiangPoints ≤ n ∧
      Disjoint s.points xiangPoints ∧
      alternatingImbalance
        ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
          2 * answer n - 1 := by
  obtain ⟨fine, pairs, residual, href, hpos, hperm, hres0,
      hbudget, hsmall⟩ := exists_strategy_budgeted_paired_refinement s
  exact static_board_of_budgeted_paired_refinement s fine pairs residual
    href hpos hperm hres0 hbudget hsmall

private lemma physicalPieces_eq_of_points_eq
    {n : ℕ} (s t : Strategy n) (hpoints : s.points = t.points)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) :
    physicalPieces s xiangPoints = physicalPieces t xiangPoints := by
  simp [physicalPieces, Strategy.playPieceLength, Strategy.playEnds, hpoints]

private lemma nat_add_one_lt_two_pow_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    m + 1 < 2 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega, pow_succ]
      have h := ih (by omega)
      have hp : 0 < 2 ^ (2 + k) := by positivity
      omega

private lemma uniform_singleton_imbalance_exceeds_binary_bound
    (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / ((2 : ℝ) ^ m - 1) < 1 / m := by
  have hpowNat : m + 1 < 2 ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [show 2 + (k + 1) = (2 + k) + 1 by omega, pow_succ]
        have h := ih (by omega)
        have hp : 0 < 2 ^ (2 + k) := by positivity
        omega
  have hcast : ((m + 1 : ℕ) : ℝ) < ((2 ^ m : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  norm_num [Nat.cast_add, Nat.cast_pow] at hcast
  have hpow : (m : ℝ) < (2 : ℝ) ^ m - 1 := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have hden : (0 : ℝ) < (2 : ℝ) ^ m - 1 := lt_trans hmpos hpow
  rw [div_lt_div_iff₀ hden hmpos]
  simpa using hpow

private lemma firstPlayerSum_duplicate_all_but_one
    (m : ℕ) (before after : List ℝ)
    (hsum : ((before.flatMap fun x => [x, x]) ++
      (1 / (m : ℝ)) :: (after.flatMap fun x => [x, x])).sum = 1) :
    firstPlayerSum
      ((before.flatMap fun x => [x, x]) ++
        (1 / (m : ℝ)) :: (after.flatMap fun x => [x, x])) =
      (1 + 1 / (m : ℝ)) / 2 := by
  let xs := (before.flatMap fun x => [x, x]) ++
    (1 / (m : ℝ)) :: (after.flatMap fun x => [x, x])
  have himb : alternatingImbalance xs = 1 / (m : ℝ) := by
    dsimp [xs]
    rw [alternatingImbalance_duplicate_singleton_duplicate]
  have h := alternatingImbalance_add_sum xs
  rw [himb, hsum] at h
  linarith

private lemma exists_static_sorted_board_bound
    {n : ℕ+} (s : Strategy n) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      firstPlayerSum ((physicalPieces s xiangPoints).mergeSort (· ≥ ·)) ≤
        answer n := by
  obtain ⟨xiangPoints, hcard, hd, himb⟩ :=
    exists_static_sorted_board_alternating_bound s
  refine ⟨xiangPoints, hcard, hd, ?_⟩
  exact exists_static_sorted_board_bound_of_alternating_bound hd himb

private lemma firstPlayerSum_le_answer_of_sum_one_imbalance
    {n : ℕ+} (xs : List ℝ)
    (hsum : xs.sum = 1)
    (himbalance : alternatingImbalance xs ≤
      1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1)) :
    firstPlayerSum xs ≤ answer n := by
  have hid := alternatingImbalance_add_sum xs
  rw [answer_eq_half_one_add_inv]
  linarith

private lemma arbitrary_strategy_upper_bound_of_sorted_refinement
    {n : ℕ+} (s : Strategy n)
    (hrefine : ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      alternatingImbalance
        ((physicalPieces s xiangPoints).mergeSort
          (fun a b : ℝ => decide (b ≤ a))) ≤
        1 / ((2 : ℝ) ^ ((n : ℕ) + 1) - 1))
    (hmajorize : ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints),
      ∃ xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1),
        s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        alternatingImbalance
          (playedPieces s xiangPoints card_xiangPoints_le hd xiangClaims) ≤
        alternatingImbalance
          ((physicalPieces s xiangPoints).mergeSort
            (fun a b : ℝ => decide (b ≤ a)))) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  obtain ⟨xiangPoints, hcard, hd, hrefine⟩ := hrefine
  obtain ⟨xiangClaims, hvalid, hmajorize⟩ := hmajorize xiangPoints hcard hd
  refine ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, ?_⟩
  apply playLength_le_answer_of_playedPieces_imbalance s xiangPoints hcard hd xiangClaims hvalid
  exact hmajorize.trans hrefine

private lemma sorted_physicalPieces_sum {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    ((physicalPieces s xiangPoints).mergeSort
      (fun a b : ℝ => decide (b ≤ a))).sum = 1 := by
  rw [List.Perm.sum_eq (List.mergeSort_perm _ _)]
  exact physicalPieces_sum s xiangPoints hd

private lemma alternatingImbalance_orderedInsert_sandwich
    (a b : ℝ) (hab : a ≤ b) (xs : List ℝ)
    (hsorted : xs.Pairwise (· ≥ ·))
    (hbound : ∀ z ∈ xs, z ≤ b) :
    a ≤ alternatingImbalance xs +
        alternatingImbalance (xs.orderedInsert (· ≥ ·) a) ∧
      alternatingImbalance xs +
        alternatingImbalance (xs.orderedInsert (· ≥ ·) a) ≤
          2 * b - a := by
  induction xs generalizing b with
  | nil =>
      simp [alternatingImbalance]
      linarith
  | cons x xs ih =>
      rw [List.pairwise_cons] at hsorted
      by_cases hax : a ≥ x
      · simp [List.orderedInsert_cons, hax, alternatingImbalance_cons]
        linarith
      · have hax' : a ≤ x := le_of_lt (lt_of_not_ge hax)
        have hi := ih x hax' hsorted.2 hsorted.1
        rw [List.orderedInsert_cons, if_neg hax,
          alternatingImbalance_cons, alternatingImbalance_cons]
        constructor <;> linarith [hbound x (by simp)]

private def SecondGreedyDominates : List ℝ → Prop
  | [] => True
  | [_] => True
  | _ :: b :: xs => (∀ z ∈ xs, z ≤ b) ∧ SecondGreedyDominates xs

private lemma alternatingImbalance_le_insertionSort_of_secondGreedy
    {xs : List ℝ} (h : SecondGreedyDominates xs) :
    alternatingImbalance xs ≤
      alternatingImbalance (xs.insertionSort (· ≥ ·)) := by
  induction xs using List.twoStepInduction with
  | nil =>
      simp [alternatingImbalance]
  | singleton x =>
      simp [alternatingImbalance]
  | cons_cons a b xs ih =>
      rcases h with ⟨hb, htail⟩
      have hih := ih htail
      let t := xs.insertionSort (· ≥ ·)
      change alternatingImbalance xs ≤ alternatingImbalance t at hih
      have htSorted : t.Pairwise (· ≥ ·) :=
        List.pairwise_insertionSort _ _
      have hb_t : ∀ z ∈ t, z ≤ b := by
        intro z hz
        exact hb z ((List.mem_insertionSort (· ≥ ·)).mp hz)
      have hsort_b :
          (b :: xs).insertionSort (· ≥ ·) = b :: t := by
        exact List.insertionSort_cons_of_forall_rel
          (r := fun x y : ℝ => x ≥ y) hb
      by_cases hab : a ≥ b
      · rw [List.insertionSort_cons, hsort_b]
        rw [List.orderedInsert_cons_of_le
          (r := fun x y : ℝ => x ≥ y) t hab]
        simp only [alternatingImbalance]
        linarith
      · have hab' : a ≤ b := le_of_lt (lt_of_not_ge hab)
        have hsand :=
          alternatingImbalance_orderedInsert_sandwich
            a b hab' t htSorted hb_t
        rw [List.insertionSort_cons, hsort_b]
        rw [List.orderedInsert_of_not_le
          (r := fun x y : ℝ => x ≥ y) t hab]
        rw [alternatingImbalance_cons b
          (t.orderedInsert (· ≥ ·) a)]
        change
          a - b + alternatingImbalance xs ≤
            b - alternatingImbalance (t.orderedInsert (· ≥ ·) a)
        linarith

private lemma secondGreedyDominates_of_indexed
    (ys : List ℝ)
    (h : ∀ q : ℕ, 2 * q + 1 < ys.length →
      ∀ k : ℕ, 2 * q + 1 < k → k < ys.length →
        ys.getD k 0 ≤ ys.getD (2 * q + 1) 0) :
    SecondGreedyDominates ys := by
  induction ys using List.twoStepInduction with
  | nil =>
      trivial
  | singleton x =>
      trivial
  | cons_cons a b xs ih =>
      constructor
      · intro z hz
        obtain ⟨i, hi, hiz⟩ := List.getElem_of_mem hz
        have hh := h 0 (by simp) (i + 2) (by omega) (by simp; omega)
        rw [
          List.getD_eq_getElem _ _
            (show i + 2 < (a :: b :: xs).length by simp; omega),
          List.getD_eq_getElem _ _
            (show 1 < (a :: b :: xs).length by simp)
        ] at hh
        simpa using hiz ▸ hh
      · apply ih
        intro q hq k hqk hk
        have hh :=
          h (q + 1) (by simp; omega) (k + 2)
            (by omega) (by simp; omega)
        simpa [show 2 * (q + 1) + 1 = (2 * q + 1) + 2 by omega]
          using hh

private lemma firstPlayerSum_le_descending_mergeSort_of_secondGreedy
    (xs : List ℝ)
    (h : ∀ q : ℕ, 2 * q + 1 < xs.length →
      ∀ k : ℕ, 2 * q + 1 < k → k < xs.length →
        xs.getD k 0 ≤ xs.getD (2 * q + 1) 0) :
    firstPlayerSum xs ≤ firstPlayerSum (xs.mergeSort (· ≥ ·)) := by
  have hstruct := secondGreedyDominates_of_indexed xs h
  have himb :=
    alternatingImbalance_le_insertionSort_of_secondGreedy hstruct
  rw [← List.mergeSort_eq_insertionSort
    (r := fun x y : ℝ => x ≥ y) xs] at himb
  have hsum :
      (xs.mergeSort (· ≥ ·)).sum = xs.sum :=
    (List.mergeSort_perm xs (· ≥ ·)).sum_eq
  have hx := alternatingImbalance_add_sum xs
  have hs :=
    alternatingImbalance_add_sum (xs.mergeSort (· ≥ ·))
  linarith

private lemma descending_mergeSort_eq_of_perm
    {xs ys : List ℝ} (hp : xs.Perm ys) :
    xs.mergeSort (· ≥ ·) = ys.mergeSort (· ≥ ·) := by
  apply List.Perm.eq_of_pairwise'
    (r := fun x y : ℝ => x ≥ y)
    (List.pairwise_mergeSort' _ _)
    (List.pairwise_mergeSort' _ _)
  exact (List.mergeSort_perm xs (· ≥ ·)).trans
    (hp.trans (List.mergeSort_perm ys (· ≥ ·)).symm)

private lemma arbitrary_strategy_upper_bound {n : ℕ+} (s : Strategy n) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims ∧
        s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤ answer n := by
  apply arbitrary_strategy_upper_bound_of_static_sorted_board s
  · intro xiangPoints hcard hd xiangClaims hvalid hmax
    let xs := playedPieces s xiangPoints hcard hd xiangClaims
    have hindexed := second_greedy_all_later_piece_bounds
      s xiangPoints hcard hd xiangClaims hvalid hmax
    have hfp :
        firstPlayerSum xs ≤ firstPlayerSum (xs.mergeSort (· ≥ ·)) :=
      firstPlayerSum_le_descending_mergeSort_of_secondGreedy xs hindexed
    have hsorted :
        xs.mergeSort (· ≥ ·) =
          (physicalPieces s xiangPoints).mergeSort (· ≥ ·) :=
      descending_mergeSort_eq_of_perm
        (playedPieces_perm_physicalPieces
          s xiangPoints hcard hd xiangClaims hvalid)
    have htotal := playLength_add_secondPlayLength_eq_one
      s xiangPoints hcard hd xiangClaims hvalid
    have hdiff := playImbalance_eq_alternatingImbalance
      s xiangPoints hcard hd xiangClaims
    have hxsum := playedPieces_sum_eq_one_of_valid
      s xiangPoints hcard hd xiangClaims hvalid
    have hfps := alternatingImbalance_add_sum xs
    have hplay :
        s.playLength xiangPoints hcard hd xiangClaims =
          firstPlayerSum xs := by
      dsimp [xs] at hxsum hfps ⊢
      linarith
    rw [hplay]
    rw [hsorted] at hfp
    exact hfp
  · exact exists_static_sorted_board_bound s

theorem result {n : ℕ+} : IsGreatest {c | ∃ s : Strategy n,
    ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints) (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
      c ≤ s.playLength xiangPoints card_xiangPoints_le hd xiangClaims} (answer n) := by
  constructor
  · refine ⟨greedyNormalizedStrategy n, ?_⟩
    intro xiangPoints card_xiangPoints_le hd xiangClaims hvalid
    exact greedy_normalized_strategy_lower_bound
      xiangPoints card_xiangPoints_le hd xiangClaims hvalid
  · intro c hc
    obtain ⟨s, hs⟩ := hc
    obtain ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, hupper⟩ :=
      arbitrary_strategy_upper_bound s
    exact (hs xiangPoints hcard hd xiangClaims hvalid).trans hupper

end IMO2026P3
