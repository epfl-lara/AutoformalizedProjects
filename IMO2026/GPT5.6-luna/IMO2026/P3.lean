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
noncomputable def answer : ℕ+ → ℝ :=
  fun n => ((n : ℝ) + 1) / (2 * (n : ℝ) + 1)

private lemma fin_exists_not_mem_range (m : ℕ) (f : Fin m → Fin (m + 1)) :
    ∃ i : Fin (m + 1), i ∉ Set.range f := by
  classical
  by_contra h
  push_neg at h
  have hsurj : Function.Surjective f := by
    intro i
    exact h i
  have hcard : m + 1 ≤ m := by
    simpa using Fintype.card_le_of_surjective f hsurj
  exact Nat.not_succ_le_self m hcard

private lemma fin_exists_not_mem_range_of_le (m N : ℕ) (h : m ≤ N)
    (f : Fin m → Fin (N + 1)) : ∃ i : Fin (N + 1), i ∉ Set.range f := by
  classical
  by_contra hn
  push_neg at hn
  have hsurj : Function.Surjective f := by
    intro i
    exact hn i
  have hcard : N + 1 ≤ m := by
    simpa using Fintype.card_le_of_surjective f hsurj
  omega

private noncomputable def arbitraryStrategy (n : ℕ) : Strategy n :=
  { points := ∅
    card_points_le := by simp
    claims := by
      intro xiangPoints card_xiangPoints_le hd m hm priorClaims
      have hfree : ∃ i : Fin (#(∅ : Finset (Set.Ioo (0 : ℝ) 1)) + #xiangPoints + 1),
          i ∉ Set.range priorClaims := by
        apply fin_exists_not_mem_range_of_le m (#(∅ : Finset (Set.Ioo (0 : ℝ) 1)) + #xiangPoints)
        exact hm
      exact ⟨Classical.choose hfree, Classical.choose_spec hfree⟩ }

private noncomputable def strategyOfPoints (n : ℕ) (points : Finset (Set.Ioo (0 : ℝ) 1))
    (hpoints : #points ≤ n) : Strategy n :=
  { points := points
    card_points_le := hpoints
    claims := by
      intro xiangPoints hxiang hd m hm priorClaims
      have hfree : ∃ i : Fin (#points + #xiangPoints + 1), i ∉ Set.range priorClaims := by
        apply fin_exists_not_mem_range_of_le m (#points + #xiangPoints)
        exact hm
      exact ⟨Classical.choose hfree, Classical.choose_spec hfree⟩ }

private lemma injective_fin_surjective {N : ℕ} (f : Fin N → Fin N) (hf : Function.Injective f) :
    Function.Surjective f := by
  classical
  intro y
  by_contra hy
  have hnot : y ∉ Finset.univ.image f := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨x, hx, hxf⟩
    exact hy ⟨x, hxf⟩
  have hsub : (Finset.univ.image f) ⊆ Finset.univ.erase y := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨by
      intro hzy
      exact hnot (hzy ▸ hz), Finset.mem_univ z⟩
  have hlt : (Finset.univ.image f).card < (Finset.univ : Finset (Fin N)).card := by
    calc
      (Finset.univ.image f).card ≤ (Finset.univ.erase y).card := Finset.card_le_card hsub
      _ < (Finset.univ : Finset (Fin N)).card := Finset.card_erase_lt_of_mem (Finset.mem_univ y)
  have heq : (Finset.univ.image f).card = (Finset.univ : Finset (Fin N)).card := by
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb hab
      exact hf hab)]
  omega

private lemma play_valid_is_permutation {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    Function.Bijective (s.play xiangPoints card_xiangPoints_le hd xiangClaims
      (#s.points + #xiangPoints + 1)) := by
  refine ⟨hvalid, ?_⟩
  exact injective_fin_surjective _ hvalid

private lemma play_sum_reindex {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims) :
    (∑ i : Fin (#s.points + #xiangPoints + 1),
      s.playPieceLength xiangPoints
        (s.play xiangPoints card_xiangPoints_le hd xiangClaims (#s.points + #xiangPoints + 1) i)) =
      ∑ j : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints j := by
  let e : Fin (#s.points + #xiangPoints + 1) ≃ Fin (#s.points + #xiangPoints + 1) :=
    Equiv.ofBijective _ (play_valid_is_permutation s xiangPoints card_xiangPoints_le hd xiangClaims hvalid)
  simpa [e] using (Equiv.sum_comp e (fun j => s.playPieceLength xiangPoints j))

private lemma strategy_claim_fresh {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) (m : ℕ)
    (hm : m ≤ #s.points + #xiangPoints) (priorClaims : Fin m → Fin (#s.points + #xiangPoints + 1)) :
    (s.claims xiangPoints hcard hd m hm priorClaims : Fin (#s.points + #xiangPoints + 1)) ∉
      Set.range priorClaims := by
  exact (s.claims xiangPoints hcard hd m hm priorClaims).property

private lemma odd_grid_mem (n : ℕ) (i : Fin n) :
    ((2 : ℝ) * (i : ℝ) + 1) / ((2 : ℝ) * (n : ℝ) + 1) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : 0 < (2 : ℝ) * (n : ℝ) + 1 := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hn).2
    have hi : (i : ℝ) < (n : ℝ) := by exact_mod_cast i.isLt
    nlinarith

private noncomputable def oddGrid (n : ℕ) : Finset (Set.Ioo (0 : ℝ) 1) :=
  Finset.univ.image
    (fun i : Fin n =>
      (⟨((2 : ℝ) * (i : ℝ) + 1) / ((2 : ℝ) * (n : ℝ) + 1), odd_grid_mem n i⟩ : Set.Ioo (0 : ℝ) 1))

private lemma odd_grid_card (n : ℕ) : #(oddGrid n) = n := by
  classical
  calc
    #(oddGrid n) = #(Finset.univ : Finset (Fin n)) := by
      rw [oddGrid]
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Fin.ext
      have hv := congrArg Subtype.val hab
      have hn : (2 : ℝ) * (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn] at hv
      exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ))
    _ = n := by simp

private lemma even_grid_mem (n : ℕ) (i : Fin n) :
    ((2 : ℝ) * (i : ℝ) + 2) / ((2 : ℝ) * (n : ℝ) + 1) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hn : 0 < (2 : ℝ) * (n : ℝ) + 1 := by positivity
  constructor
  · positivity
  · apply (div_lt_iff₀ hn).2
    have hi' : (i : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt i.isLt)
    nlinarith

private noncomputable def evenGrid (n : ℕ) : Finset (Set.Ioo (0 : ℝ) 1) :=
  Finset.univ.image
    (fun i : Fin n =>
      (⟨((2 : ℝ) * (i : ℝ) + 2) / ((2 : ℝ) * (n : ℝ) + 1), even_grid_mem n i⟩ : Set.Ioo (0 : ℝ) 1))

private lemma even_grid_card (n : ℕ) : #(evenGrid n) = n := by
  classical
  calc
    #(evenGrid n) = #(Finset.univ : Finset (Fin n)) := by
      rw [evenGrid]
      apply Finset.card_image_iff.mpr
      intro a ha b hb hab
      apply Fin.ext
      have hv := congrArg Subtype.val hab
      have hn : (2 : ℝ) * (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hn] at hv
      exact_mod_cast (by linarith : (a : ℝ) = (b : ℝ))
    _ = n := by simp

private noncomputable def maxFreeIndex {N m : ℕ} (f : Fin N → ℝ)
    (prior : Fin m → Fin N) (hfree : ∃ i, i ∉ Set.range prior) :
    {i : Fin N // i ∉ Set.range prior} := by
  classical
  let U : Finset (Fin N) := Finset.univ.filter (fun i => i ∉ Set.range prior)
  have hU : U.Nonempty := by
    rcases hfree with ⟨i, hi⟩
    exact ⟨i, by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi⟩
  let H := Finset.exists_max_image U f hU
  let i : Fin N := Classical.choose H
  have hi : i ∈ U := (Classical.choose_spec H).1
  exact ⟨i, by
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi⟩

private lemma maxFreeIndex_max {N m : ℕ} (f : Fin N → ℝ)
    (prior : Fin m → Fin N) (hfree : ∃ i, i ∉ Set.range prior) :
    ∀ j : Fin N, j ∉ Set.range prior →
      f j ≤ f (maxFreeIndex f prior hfree) := by
  classical
  let U : Finset (Fin N) := Finset.univ.filter (fun i => i ∉ Set.range prior)
  have hU : U.Nonempty := by
    rcases hfree with ⟨i, hi⟩
    exact ⟨i, by
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi⟩
  let H := Finset.exists_max_image U f hU
  have hmax := (Classical.choose_spec H).2
  intro j hj
  apply hmax j
  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hj

private noncomputable def greedyStrategy (n : ℕ) : Strategy n :=
  { points := evenGrid n
    card_points_le := by rw [even_grid_card]
    claims := by
      intro xiangPoints hcard hd m hm priorClaims
      have hfree : ∃ i : Fin (#(evenGrid n) + #xiangPoints + 1),
          i ∉ Set.range priorClaims := by
        apply fin_exists_not_mem_range_of_le m (#(evenGrid n) + #xiangPoints)
        exact hm
      exact maxFreeIndex
        (fun i => (strategyOfPoints n (evenGrid n) (by rw [even_grid_card])).playPieceLength
          xiangPoints i) priorClaims hfree }

private lemma alternating_sum_bound {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (q : ℝ)
    (hpair : ∀ i : Fin n, a i.succ ≤ b i)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1)
    (hfirst : a 0 ≤ q) :
    (∑ i : Fin (n + 1), a i) ≤ (1 + q) / 2 := by
  have htail : (∑ i : Fin n, a i.succ) ≤ (∑ i : Fin n, b i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ] at htotal ⊢
  linarith

private lemma list_sum_getD_diff_eq_last_sub_first (l : List ℝ) :
    (∑ i : Fin l.length, (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) =
      l.getD l.length 0 - l.getD 0 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change (∑ i : Fin (l.length + 1), ((a :: l).getD ((i : ℕ) + 1) 0 -
      (a :: l).getD (i : ℕ) 0)) =
      (a :: l).getD l.length.succ 0 - (a :: l).getD 0 0
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.zero_add, Fin.val_succ,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [ih]
    ring

private lemma play_ends_sorted {n : ℕ} (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) :
    (s.playEnds xiangPoints).Pairwise (· ≤ ·) := by
  simp [Strategy.playEnds]

private lemma probe_playEnds_length {n : ℕ} (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (s.playEnds xiangPoints).length = #s.points + #xiangPoints + 2 := by
  rw [Strategy.playEnds, Finset.length_sort]
  simp [Finset.card_union_of_disjoint hd]

private lemma playLength_filter_expansion {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    s.playLength xiangPoints hcard hd xiangClaims =
      ∑ i : Fin (#s.points + #xiangPoints + 1),
        if Even ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0 := by
  simp [Strategy.playLength, Finset.sum_filter]

private lemma answer_le_of_odd_bound {n : ℕ+} {score odd : ℝ} (htotal : score + odd = 1)
    (hodd : odd ≤ (n : ℝ) / (2 * (n : ℝ) + 1)) : answer n ≤ score := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hidentity : ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) +
      (n : ℝ) / (2 * (n : ℝ) + 1) = 1 := by
    field_simp
    ring
  dsimp [answer]
  linarith

private lemma adjacent_getD_nonneg : ∀ (l : List ℝ), l.Pairwise (· ≤ ·) →
    ∀ (i : Fin l.length), i.val + 1 < l.length →
      0 ≤ l.getD (i.val + 1) 0 - l.getD i.val 0 := by
  intro l
  induction l with
  | nil =>
    intro hs i hi
    exact Fin.elim0 i
  | cons a l ih =>
    intro hs i hi
    cases i using Fin.cases with
    | zero =>
      cases l with
      | nil => simp at hi
      | cons b l =>
        have hs' := (List.pairwise_cons.mp hs)
        have hab : a ≤ b := hs'.1 b (by simp)
        simpa [List.getD] using (sub_nonneg.mpr hab)
    | succ j =>
      simp at hi
      have h' : j.val + 1 < l.length := by omega
      have hs' := (List.pairwise_cons.mp hs)
      have hj := ih hs'.2 j h'
      simpa [List.getD] using hj

private lemma list_sum_getD_diff_eq_last_sub_first_pred (l : List ℝ) (hl : 0 < l.length) :
    (∑ i : Fin (l.length - 1),
      (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) =
      l.getD (l.length - 1) 0 - l.getD 0 0 := by
  have hfull := list_sum_getD_diff_eq_last_sub_first l
  have hlen : l.length = (l.length - 1) + 1 := by omega
  rw [hlen] at hfull
  rw [Fin.sum_univ_castSucc] at hfull
  simp only [Fin.val_castSucc, Fin.val_last] at hfull
  rw [← hlen] at hfull
  have hres :
      (∑ i : Fin (l.length - 1),
        (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) +
        (l.getD l.length 0 - l.getD (l.length - 1) 0) =
      l.getD l.length 0 - l.getD 0 0 := by
    simpa only using hfull
  linarith [hres]

private lemma play_pieceLength_nonneg {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    ∀ i : Fin (#s.points + #xiangPoints + 1),
      0 ≤ s.playPieceLength xiangPoints i := by
  intro i
  unfold Strategy.playPieceLength
  have hlen := probe_playEnds_length s xiangPoints hd
  let j : Fin (s.playEnds xiangPoints).length :=
    ⟨i.val, by rw [hlen]; omega⟩
  have hj := adjacent_getD_nonneg (s.playEnds xiangPoints)
    (play_ends_sorted s xiangPoints) j (by
      dsimp [j]
      rw [hlen]
      omega)
  simpa [j] using hj

private lemma play_length_le_total_of_nonneg {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims)
    (hnonneg : ∀ i : Fin (#s.points + #xiangPoints + 1),
      0 ≤ s.playPieceLength xiangPoints i) :
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims ≤
      ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i := by
  calc
    s.playLength xiangPoints card_xiangPoints_le hd xiangClaims =
        ∑ i : Fin (#s.points + #xiangPoints + 1),
          if Even ((i : Fin _) : ℕ) then
            s.playPieceLength xiangPoints
              (s.play xiangPoints card_xiangPoints_le hd xiangClaims
                (#s.points + #xiangPoints + 1) i)
          else 0 := playLength_filter_expansion s xiangPoints card_xiangPoints_le hd xiangClaims
    _ ≤ ∑ i : Fin (#s.points + #xiangPoints + 1),
          s.playPieceLength xiangPoints
            (s.play xiangPoints card_xiangPoints_le hd xiangClaims
              (#s.points + #xiangPoints + 1) i) := by
      exact Finset.sum_le_sum (fun i hi => by
        split <;> simp_all [hnonneg])
    _ = ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i :=
      play_sum_reindex s xiangPoints card_xiangPoints_le hd xiangClaims hvalid

private lemma playLength_add_odd_play_sum_eq_total_new {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims +
      (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) =
      ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i := by
  rw [playLength_filter_expansion s xiangPoints hcard hd xiangClaims]
  rw [← play_sum_reindex s xiangPoints hcard hd xiangClaims hvalid]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases Nat.even_or_odd ((i : Fin _) : ℕ) with he | ho
  · have hno : ¬ Odd ((i : Fin _) : ℕ) := by
      intro hodd
      rcases he with ⟨k, hk⟩
      rcases hodd with ⟨l, hl⟩
      omega
    simp [he, hno]
  · have hno : ¬ Even ((i : Fin _) : ℕ) := by
      intro hev
      rcases ho with ⟨k, hk⟩
      rcases hev with ⟨l, hl⟩
      omega
    simp [ho, hno]

private lemma candidate_score_lower_of_odd_bound {n : ℕ+} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (htotal : (∑ i : Fin (#s.points + #xiangPoints + 1),
      s.playPieceLength xiangPoints i) = 1)
    (hodd : (∑ i : Fin (#s.points + #xiangPoints + 1),
      if Odd ((i : Fin _) : ℕ) then
        s.playPieceLength xiangPoints
          (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
      else 0) ≤ (n : ℝ) / (2 * (n : ℝ) + 1)) :
    answer n ≤ s.playLength xiangPoints hcard hd xiangClaims := by
  apply answer_le_of_odd_bound
  · calc
      s.playLength xiangPoints hcard hd xiangClaims +
          (∑ i : Fin (#s.points + #xiangPoints + 1),
            if Odd ((i : Fin _) : ℕ) then
              s.playPieceLength xiangPoints
                (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
            else 0) =
          ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i :=
        playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid
      _ = 1 := htotal
  · exact hodd

private lemma sorted_first_eq_zero (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (hm : (0 : ℝ) ∈ l) (hnon : ∀ x ∈ l, 0 ≤ x) : l.getD 0 0 = 0 := by
  cases l with
  | nil => simp at hm
  | cons a l =>
    have hcons := List.pairwise_cons.mp hs
    have ha_nonneg : 0 ≤ a := hnon a (by simp)
    have ha : a = 0 := by
      by_cases htail : (0 : ℝ) ∈ l
      · have ha_le : a ≤ 0 := hcons.1 0 htail
        linarith
      · have ha_eq : (0 : ℝ) = a := by simpa [htail] using hm
        exact ha_eq.symm
    simp [ha]

private lemma playEnds_first_zero {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) :
    (s.playEnds xiangPoints).getD 0 0 = 0 := by
  apply sorted_first_eq_zero
  · exact play_ends_sorted s xiangPoints
  · unfold Strategy.playEnds
    simp
  · intro x hx
    unfold Strategy.playEnds at hx
    have hx' : x ∈ Finset.map (Function.Embedding.subtype (p := fun x => x ∈ Set.Ioo (0 : ℝ) 1))
        (s.points ∪ xiangPoints) ∪ ({0, 1} : Finset ℝ) :=
      (Finset.mem_sort (r := fun a b : ℝ => a ≤ b)).mp hx
    rcases Finset.mem_union.1 hx' with hx' | hx'
    · rcases Finset.mem_map.1 hx' with ⟨p, hp, rfl⟩
      exact p.property.1.le
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
      rcases hx' with rfl | rfl
      · exact le_rfl
      · positivity

private lemma total_piece_sum_eq_one_of_endpoints_probe {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints)
    (hfirst : (s.playEnds xiangPoints).getD 0 0 = 0)
    (hlast : (s.playEnds xiangPoints).getD ((s.playEnds xiangPoints).length - 1) 0 = 1) :
    (∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i) = 1 := by
  have hlen := probe_playEnds_length s xiangPoints hd
  have hpos : 0 < (s.playEnds xiangPoints).length := by
    rw [hlen]
    omega
  have hsum := list_sum_getD_diff_eq_last_sub_first_pred (s.playEnds xiangPoints) hpos
  have hlast' : (s.playEnds xiangPoints).getD (#s.points + #xiangPoints + 2 - 1) 0 = 1 := by
    rw [← hlen]
    exact hlast
  rw [hlen] at hsum
  rw [hfirst, hlast'] at hsum
  norm_num at hsum
  rw [← Finset.sum_sub_distrib] at hsum
  change (∑ i : Fin (#s.points + #xiangPoints + 1),
      ((s.playEnds xiangPoints).getD ((i : ℕ) + 1) 0 -
        (s.playEnds xiangPoints).getD (i : ℕ) 0)) = 1 at hsum
  exact hsum

private lemma sorted_last_eq_one_test : ∀ (l : List ℝ), l.Pairwise (· ≤ ·) →
    (1 : ℝ) ∈ l → (∀ x ∈ l, x ≤ 1) → l.getD (l.length - 1) 0 = 1 := by
  intro l
  induction l with
  | nil =>
    intro hs hm hnon
    simp at hm
  | cons a l ih =>
    intro hs hm hnon
    have hcons := List.pairwise_cons.mp hs
    by_cases htail : (1 : ℝ) ∈ l
    · have hnon_tail : ∀ x ∈ l, x ≤ 1 := by
        intro x hx
        exact hnon x (by simp [hx])
      have hi := ih hcons.2 htail hnon_tail
      cases l with
      | nil => simp at htail
      | cons b l =>
        simpa [List.getD] using hi
    · have ha : a = 1 := by
        have : (1 : ℝ) = a := by simpa [htail] using hm
        exact this.symm
      cases l with
      | nil => simp [ha]
      | cons b l =>
        have hab : a ≤ b := hcons.1 b (by simp)
        have hb : b ≤ 1 := hnon b (by simp)
        have hb1 : b = 1 := by linarith [hab, hb, ha]
        exact False.elim (htail (by simp [hb1]))

private lemma even_odd_sum_partition {N : ℕ} (f : Fin N → ℝ) :
    (∑ i : Fin N with Even ((i : Fin N) : ℕ), f i) +
      ∑ i : Fin N with Odd ((i : Fin N) : ℕ), f i = ∑ i : Fin N, f i := by
  classical
  simpa [Nat.not_even_iff_odd] using
    (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun i : Fin N => Even ((i : Fin N) : ℕ)) f)

private lemma list_sum_getD_diff_eq_last_sub_first_drop (l : List ℝ) :
    (∑ i : Fin (l.length - 1), (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) =
      l.getD (l.length - 1) 0 - l.getD 0 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      change (∑ i : Fin (l.length + 1),
        ((a :: b :: l).getD ((i : ℕ) + 1) 0 - (a :: b :: l).getD (i : ℕ) 0)) =
        (a :: b :: l).getD (l.length + 1) 0 - (a :: b :: l).getD 0 0
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, Nat.zero_add, List.getD_cons_zero,
        Fin.val_succ, List.getD_cons_succ]
      have ih' : (∑ i : Fin l.length,
          (l.getD (i : ℕ) 0 - (b :: l).getD (i : ℕ) 0)) =
          (b :: l).getD l.length 0 - b := by
        convert ih using 1 <;> simp only [List.length_cons, Nat.succ_sub_one,
          List.getD_cons_zero, List.getD_cons_succ] <;> rfl
      rw [ih']
      simp

private lemma sorted_getD_zero_test {l : List ℝ}
    (hs : l.Pairwise (· ≤ ·)) (hmem : (0 : ℝ) ∈ l)
    (hnonneg : ∀ x ∈ l, 0 ≤ x) : l.getD 0 0 = 0 := by
  cases l with
  | nil => simp at hmem
  | cons a l =>
    simp only [List.getD_cons_zero]
    have ha0 : 0 ≤ a := hnonneg a (by simp)
    have hle : a ≤ 0 := by
      rcases List.mem_cons.mp hmem with h | h
      · exact le_of_eq h.symm
      · exact (List.pairwise_cons.mp hs).1 0 h
    linarith

private lemma total_piece_sum_eq_one_parametric {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i) = 1 := by
  apply total_piece_sum_eq_one_of_endpoints_probe s xiangPoints hd
  · exact playEnds_first_zero s xiangPoints
  · apply sorted_last_eq_one_test
    · exact play_ends_sorted s xiangPoints
    · unfold Strategy.playEnds
      simp
    · intro x hx
      unfold Strategy.playEnds at hx
      have hx' : x ∈ Finset.map (Function.Embedding.subtype (p := fun x => x ∈ Set.Ioo (0 : ℝ) 1))
          (s.points ∪ xiangPoints) ∪ ({0, 1} : Finset ℝ) :=
        (Finset.mem_sort (r := fun a b : ℝ => a ≤ b)).mp hx
      rcases Finset.mem_union.1 hx' with hx' | hx'
      · rcases Finset.mem_map.1 hx' with ⟨p, hp, rfl⟩
        exact p.property.2.le
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · positivity
        · exact le_rfl

private lemma play_piece_lengths_sum_eq_endpoint_gap {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (∑ i : Fin ((s.playEnds xiangPoints).length - 1),
      s.playPieceLength xiangPoints
        (Fin.cast (by
          rw [probe_playEnds_length s xiangPoints hd]
          omega : (s.playEnds xiangPoints).length - 1 =
          #s.points + #xiangPoints + 1) i)) =
      (s.playEnds xiangPoints).getD ((s.playEnds xiangPoints).length - 1) 0 -
        (s.playEnds xiangPoints).getD 0 0 := by
  unfold Strategy.playPieceLength
  have hsum := list_sum_getD_diff_eq_last_sub_first_pred
    (s.playEnds xiangPoints) (by rw [probe_playEnds_length s xiangPoints hd]; omega)
  simpa using hsum

private lemma sorted_last_eq_one_research :
    ∀ l : List ℝ, l.Pairwise (· ≤ ·) → 1 ∈ l →
      (∀ x ∈ l, x ≤ 1) → l.getD (l.length - 1) 0 = 1 := by
  intro l
  induction l with
  | nil =>
      intro hs hm hu
      simp at hm
  | cons a l ih =>
      intro hs hm hu
      cases l with
      | nil =>
          have ha' : (1 : ℝ) = a := by simpa using hm
          have ha : a = 1 := ha'.symm
          simp [ha]
      | cons b l =>
          have hs' := List.pairwise_cons.mp hs
          have hu' : ∀ x ∈ b :: l, x ≤ 1 := by
            intro x hx
            exact hu x (by simp [hx])
          have htail_sorted : (b :: l).Pairwise (· ≤ ·) := hs'.2
          by_cases hmemtail : (1 : ℝ) ∈ b :: l
          · have hlast := ih htail_sorted hmemtail hu'
            simpa [List.getD] using hlast
          · have hax : a = 1 := by
              have hm' : (1 : ℝ) = a ∨ (1 : ℝ) ∈ b :: l := by simpa using hm
              rcases hm' with ha | hfalse
              · exact ha.symm
              · exact False.elim (hmemtail hfalse)
            have hbx : b = 1 := by
              apply le_antisymm
              · exact hu' b (by simp)
              · rw [← hax]
                exact hs'.1 b (by simp)
            have hmemtail' : (1 : ℝ) ∈ b :: l := by simpa [hbx]
            have hlast := ih htail_sorted hmemtail' hu'
            simpa [List.getD] using hlast

private lemma playLength_le_one_of_endpoints_test {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (hfirst : (s.playEnds xiangPoints).getD 0 0 = 0)
    (hlast : (s.playEnds xiangPoints).getD ((s.playEnds xiangPoints).length - 1) 0 = 1) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ 1 := by
  have htotal := total_piece_sum_eq_one_of_endpoints_probe s xiangPoints hd hfirst hlast
  calc
    s.playLength xiangPoints hcard hd xiangClaims ≤
        ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i :=
      play_length_le_total_of_nonneg s xiangPoints hcard hd xiangClaims hvalid
        (play_pieceLength_nonneg s xiangPoints hd)
    _ = 1 := htotal

private lemma universal_playLength_le_one_probe {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ 1 := by
  apply playLength_le_one_of_endpoints_test s xiangPoints hcard hd xiangClaims hvalid
  · exact playEnds_first_zero s xiangPoints
  · apply sorted_last_eq_one_research
    · exact play_ends_sorted s xiangPoints
    · unfold Strategy.playEnds
      simp
    · intro x hx
      unfold Strategy.playEnds at hx
      have hx' : x ∈ Finset.map (Function.Embedding.subtype (p := fun x => x ∈ Set.Ioo (0 : ℝ) 1))
          (s.points ∪ xiangPoints) ∪ ({0, 1} : Finset ℝ) :=
        (Finset.mem_sort (r := fun a b : ℝ => a ≤ b)).mp hx
      rcases Finset.mem_union.1 hx' with hx' | hx'
      · rcases Finset.mem_map.1 hx' with ⟨p, hp, rfl⟩
        exact p.property.2.le
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl
        · norm_num
        · exact le_rfl

private lemma greedy_claim_is_max_probe {n : ℕ}
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint (evenGrid n) xiangPoints)
    (m : ℕ) (hm : m ≤ #(evenGrid n) + #xiangPoints)
    (priorClaims : Fin m → Fin (#(evenGrid n) + #xiangPoints + 1)) :
    ∀ j : Fin (#(evenGrid n) + #xiangPoints + 1), j ∉ Set.range priorClaims →
      (strategyOfPoints n (evenGrid n) (by rw [even_grid_card])).playPieceLength xiangPoints j ≤
        (greedyStrategy n).playPieceLength xiangPoints
          ((greedyStrategy n).claims xiangPoints hcard hd m hm priorClaims) := by
  have hfree : ∃ i : Fin (#(evenGrid n) + #xiangPoints + 1), i ∉ Set.range priorClaims :=
    fin_exists_not_mem_range_of_le m (#(evenGrid n) + #xiangPoints) hm priorClaims
  intro j hj
  simpa [greedyStrategy, strategyOfPoints, Strategy.playPieceLength, Strategy.playEnds] using
    (maxFreeIndex_max
      (fun i => (strategyOfPoints n (evenGrid n) (by rw [even_grid_card])).playPieceLength
        xiangPoints i) priorClaims hfree j hj)

private lemma playLength_add_odd_eq_one_of_endpoints_test {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (hfirst : (s.playEnds xiangPoints).getD 0 0 = 0)
    (hlast : (s.playEnds xiangPoints).getD ((s.playEnds xiangPoints).length - 1) 0 = 1) :
    s.playLength xiangPoints hcard hd xiangClaims +
      (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) = 1 := by
  rw [playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid]
  exact total_piece_sum_eq_one_of_endpoints_probe s xiangPoints hd hfirst hlast

private lemma sorted_last_eq_one (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (hm : (1 : ℝ) ∈ l) (hupper : ∀ x ∈ l, x ≤ 1) :
    l.getD (l.length - 1) 0 = 1 := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    cases l with
    | nil =>
      have hm' : (1 : ℝ) = a := by simpa using hm
      simpa [hm']
    | cons b l =>
      have hs' := List.pairwise_cons.mp hs
      have hm' : (1 : ℝ) = a ∨ (1 : ℝ) = b ∨ (1 : ℝ) ∈ l := by
        simpa only [List.mem_cons] using hm
      have htail : (1 : ℝ) ∈ b :: l := by
        rcases hm' with hma | hmb | hm_tail
        · have hab : a ≤ b := hs'.1 b (by simp)
          have hb : b ≤ 1 := hupper b (by simp)
          have : b = 1 := by linarith [hma, hab, hb]
          simp [this]
        · simp [hmb]
        · simp only [List.mem_cons]
          exact Or.inr hm_tail
      have hupper' : ∀ x ∈ b :: l, x ≤ 1 := by
        intro x hx
        have hx' : x = b ∨ x ∈ l := by simpa only [List.mem_cons] using hx
        rcases hx' with hxb | hxl
        · simpa [hxb] using hupper b (by simp)
        · exact hupper x (by
            simp only [List.mem_cons]
            exact Or.inr (Or.inr hxl))
      have hlast := ih hs'.2 htail hupper'
      simpa [List.length_cons] using hlast

private lemma candidate_odd_sum_le_of_pair_terminal {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} {q : ℝ}
    (hpair : ∀ i : Fin n, b i ≤ a i.castSucc)
    (hterm : q ≤ a (Fin.last n))
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1) :
    (∑ i : Fin n, b i) ≤ (1 - q) / 2 := by
  have hsum : (∑ i : Fin n, b i) ≤ ∑ i : Fin n, a i.castSucc := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_castSucc] at htotal
  linarith

private lemma sum_getD_diff_of_succ_length {k : ℕ} (l : List ℝ)
    (hlen : l.length = k + 1) :
    (∑ i : Fin k, (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) =
      l.getD k 0 - l.getD 0 0 := by
  have hsum := list_sum_getD_diff_eq_last_sub_first_pred l (by omega)
  have hk : k = l.length - 1 := by omega
  rw [hk]
  exact hsum

private lemma list_last_ge_of_pairwise_candidate (l : List ℝ) (hs : l.Pairwise (· ≤ ·)) :
    ∀ x ∈ l, x ≤ l.getD (l.length - 1) 0 := by
  revert hs
  induction l with
  | nil =>
      intro hs x hx
      simp at hx
  | cons a l ih =>
      intro hs
      cases l with
      | nil =>
          intro x hx
          simp_all
      | cons b l =>
          have hcons := List.pairwise_cons.mp hs
          have hs_tail : (b :: l).Pairwise (· ≤ ·) := hcons.2
          have hab : a ≤ b := hcons.1 b (by simp)
          have hbl : b ≤ (b :: l).getD ((b :: l).length - 1) 0 :=
            ih hs_tail b (by simp)
          have hlast : (a :: b :: l).getD ((a :: b :: l).length - 1) 0 =
              (b :: l).getD ((b :: l).length - 1) 0 := by
            simp
          intro x hx
          rw [hlast]
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hab.trans hbl
          · exact ih hs_tail x hx

private noncomputable def opponentPrefix {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k ≤ #s.points + #xiangPoints + 1) :
    Fin k → Fin (#s.points + #xiangPoints + 1) :=
  match k with
  | 0 => Fin.elim0
  | k + 1 =>
      Fin.snoc (opponentPrefix s xiangPoints hcard hd k (by omega))
        (if Even k then
          s.claims xiangPoints hcard hd k (by omega)
            (opponentPrefix s xiangPoints hcard hd k (by omega))
        else
          maxFreeIndex
            (fun i => s.playPieceLength xiangPoints i)
            (opponentPrefix s xiangPoints hcard hd k (by omega))
            (fin_exists_not_mem_range_of_le k (#s.points + #xiangPoints) (by omega)
              (opponentPrefix s xiangPoints hcard hd k (by omega))))
termination_by k

private noncomputable def opponentClaims {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints) :
    ℕ → Fin (#s.points + #xiangPoints + 1) :=
  fun m => if h : 2 * m + 2 ≤ #s.points + #xiangPoints + 1 then
    opponentPrefix s xiangPoints hcard hd (2 * m + 2) h
      ⟨2 * m + 1, by omega⟩
  else 0

private lemma total_piece_sum_eq_endpoint_diff {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hd : Disjoint s.points xiangPoints) :
    (∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i) =
      (s.playEnds xiangPoints).getD ((s.playEnds xiangPoints).length - 1) 0 -
        (s.playEnds xiangPoints).getD 0 0 := by
  have hlen := probe_playEnds_length s xiangPoints hd
  have hpos : 0 < (s.playEnds xiangPoints).length := by
    rw [hlen]
    omega
  have hsum := list_sum_getD_diff_eq_last_sub_first_pred (s.playEnds xiangPoints) hpos
  rw [hlen] at hsum ⊢
  change (∑ i : Fin (#s.points + #xiangPoints + 1),
      ((s.playEnds xiangPoints).getD ((i : ℕ) + 1) 0 -
        (s.playEnds xiangPoints).getD (i : ℕ) 0)) =
      (s.playEnds xiangPoints).getD (#s.points + #xiangPoints + 2 - 1) 0 -
        (s.playEnds xiangPoints).getD 0 0
  exact hsum

private lemma telescoping_sum_of_fixed_length (l : List ℝ) (k : ℕ)
    (hlen : l.length = k + 1) :
    (∑ i : Fin k,
      (l.getD ((i : ℕ) + 1) 0 - l.getD (i : ℕ) 0)) =
      l.getD k 0 - l.getD 0 0 := by
  have hpos : 0 < l.length := by
    rw [hlen]
    omega
  have h := list_sum_getD_diff_eq_last_sub_first_pred l hpos
  rw [hlen] at h
  have hk : k + 1 - 1 = k := by omega
  rw [hk] at h
  exact h

private lemma odd_sum_le_even_tail_new {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ)
    (h : ∀ i : Fin n, b i ≤ a i.succ) :
    (∑ i : Fin n, b i) ≤ (∑ i : Fin (n + 1), a i) - a 0 := by
  have htail : (∑ i : Fin n, b i) ≤ (∑ i : Fin n, a i.succ) := by
    exact Finset.sum_le_sum (fun i hi => h i)
  rw [Fin.sum_univ_succ]
  linarith

private lemma play_prefix {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    ∀ (k l : ℕ) (hkl : k ≤ l) (i : Fin k),
      s.play xiangPoints hcard hd xiangClaims k i =
        s.play xiangPoints hcard hd xiangClaims l ⟨i, lt_of_lt_of_le i.isLt hkl⟩ := by
  intro k l hkl
  induction l with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      intro i
      exact Fin.elim0 i
  | succ l ih =>
      by_cases hkl' : k ≤ l
      · intro i
        have hi := ih hkl' i
        simpa [Strategy.play, Fin.snoc, lt_of_lt_of_le i.isLt hkl'] using hi
      · have hk : k = l + 1 := by omega
        subst k
        intro i
        have hi : (⟨i.val, by omega⟩ : Fin (l + 1)) = i := Fin.ext rfl
        simpa [hi]

private lemma odd_sum_bound_of_succ_le_new {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} {q : ℝ}
    (hpair : ∀ i : Fin n, b i ≤ a i.succ)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1)
    (hfirst : q ≤ a 0) :
    (∑ i : Fin n, b i) ≤ (1 - q) / 2 := by
  have htail : (∑ i : Fin n, b i) ≤ (∑ i : Fin n, a i.succ) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ] at htotal
  linarith

private lemma top_sum_bound {N M : ℕ} (f : Fin N → ℝ) (g : Fin M → Fin N)
    (hmono : ∀ i : Fin M, ∀ j : Fin N, f j ≤ f (g i)) :
    (M : ℝ) * (∑ j : Fin N, f j) ≤
      (N : ℝ) * (∑ i : Fin M, f (g i)) := by
  classical
  have h_each : ∀ i : Fin M, (∑ j : Fin N, f j) ≤ (N : ℝ) * f (g i) := by
    intro i
    calc
      ∑ j : Fin N, f j ≤ ∑ j : Fin N, f (g i) := by
        exact Finset.sum_le_sum (fun j hj => hmono i j)
      _ = (N : ℝ) * f (g i) := by simp
  have hs : (∑ i : Fin M, (∑ j : Fin N, f j)) ≤
      ∑ i : Fin M, (N : ℝ) * f (g i) :=
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i hi => h_each i)
  simpa [Finset.sum_const, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hs

private lemma opponentPrefix_injective {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k ≤ #s.points + #xiangPoints + 1) :
    Function.Injective (opponentPrefix s xiangPoints hcard hd k hk) := by
  induction k with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ k ih =>
      simp only [opponentPrefix]
      apply Fin.snoc_injective_of_injective
      · exact ih (by omega)
      · by_cases he : Even k
        · simpa [opponentPrefix, he] using
            (strategy_claim_fresh s xiangPoints hcard hd k (by omega)
              (opponentPrefix s xiangPoints hcard hd k (by omega)))
        · have hfree : ∃ i : Fin (#s.points + #xiangPoints + 1),
              i ∉ Set.range (opponentPrefix s xiangPoints hcard hd k (by omega)) := by
            apply fin_exists_not_mem_range_of_le k (#s.points + #xiangPoints)
            omega
          simpa [opponentPrefix, he] using
            (maxFreeIndex (fun i => s.playPieceLength xiangPoints i)
              (opponentPrefix s xiangPoints hcard hd k (by omega)) hfree).property

private lemma alternating_odd_bound_fin {k : ℕ} (f : Fin (2 * k + 1) → ℝ) {q : ℝ}
    (hpair : ∀ i : Fin k,
      f ⟨2 * (i : ℕ) + 1, by have hi := i.isLt; omega⟩ ≤
        f ⟨2 * (i.succ : ℕ), by have hi := i.isLt; omega⟩)
    (htotal : (∑ i : Fin (2 * k + 1), f i) = 1)
    (hfirst : q ≤ f ⟨0, by omega⟩) :
    (∑ i : Fin (2 * k + 1) with Odd ((i : Fin (2 * k + 1)) : ℕ), f i) ≤ (1 - q) / 2 := by
  classical
  let evenMap : Fin (k + 1) → Fin (2 * k + 1) := fun i =>
    ⟨2 * (i : ℕ), by have hi := i.isLt; omega⟩
  let oddMap : Fin k → Fin (2 * k + 1) := fun i =>
    ⟨2 * (i : ℕ) + 1, by have hi := i.isLt; omega⟩
  have heven :
      (∑ i : Fin (k + 1), f (evenMap i)) =
        ∑ i : Fin (2 * k + 1) with Even ((i : Fin (2 * k + 1)) : ℕ), f i := by
    refine Finset.sum_bij (f := fun i : Fin (k + 1) => f (evenMap i)) (g := f)
      (s := (Finset.univ : Finset (Fin (k + 1))))
      (t := Finset.univ.filter (fun i : Fin (2 * k + 1) =>
        Even ((i : Fin (2 * k + 1)) : ℕ))) (fun i _ => evenMap i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(i : ℕ), by dsimp [evenMap]; omega⟩
    · intro i₁ hi₁ i₂ hi₂ h
      apply Fin.ext
      simpa [evenMap] using congrArg Fin.val h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨j, hj⟩
      refine ⟨⟨j, by omega⟩, by simp, ?_⟩
      apply Fin.ext
      dsimp [evenMap]
      omega
    · intro i hi
      rfl
  have hodd :
      (∑ i : Fin k, f (oddMap i)) =
        ∑ i : Fin (2 * k + 1) with Odd ((i : Fin (2 * k + 1)) : ℕ), f i := by
    refine Finset.sum_bij (f := fun i : Fin k => f (oddMap i)) (g := f)
      (s := (Finset.univ : Finset (Fin k)))
      (t := Finset.univ.filter (fun i : Fin (2 * k + 1) =>
        Odd ((i : Fin (2 * k + 1)) : ℕ))) (fun i _ => oddMap i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      change Odd (2 * (i : ℕ) + 1)
      exact ⟨i, by omega⟩
    · intro i₁ hi₁ i₂ hi₂ h
      apply Fin.ext
      simpa [oddMap] using congrArg Fin.val h
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨j, hj⟩
      refine ⟨⟨j, by omega⟩, by simp, ?_⟩
      apply Fin.ext
      dsimp [oddMap]
      omega
    · intro i hi
      rfl
  have hab :
      (∑ i : Fin (k + 1), f (evenMap i)) + (∑ i : Fin k, f (oddMap i)) = 1 := by
    rw [heven, hodd]
    calc
      (∑ i : Fin (2 * k + 1) with Even ((i : Fin (2 * k + 1)) : ℕ), f i) +
          ∑ i : Fin (2 * k + 1) with Odd ((i : Fin (2 * k + 1)) : ℕ), f i =
          ∑ i : Fin (2 * k + 1), f i := even_odd_sum_partition f
      _ = 1 := htotal
  have hp : ∀ i : Fin k, f (oddMap i) ≤ f (evenMap i.succ) := by
    intro i
    exact hpair i
  have hf : q ≤ f (evenMap 0) := by
    simpa [evenMap] using hfirst
  have hbound := odd_sum_bound_of_succ_le_new (a := fun i => f (evenMap i))
    (b := fun i => f (oddMap i)) hp hab hf
  rw [hodd] at hbound
  exact hbound

private lemma alternating_sum_bound_forward {n : ℕ} (a : Fin (n + 1) → ℝ) (b : Fin n → ℝ) (q : ℝ)
    (hpair : ∀ i : Fin n, b i ≤ a i.succ)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1)
    (hfirst : q ≤ a 0) :
    (1 + q) / 2 ≤ (∑ i : Fin (n + 1), a i) := by
  have htail : (∑ i : Fin n, b i) ≤ (∑ i : Fin n, a i.succ) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ] at htotal ⊢
  linarith

private lemma playLength_le_of_odd_lower_parametric {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    {T B : ℝ}
    (htotal : (∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i) = T)
    (hodd : B ≤ (∑ i : Fin (#s.points + #xiangPoints + 1),
      if Odd ((i : Fin _) : ℕ) then
        s.playPieceLength xiangPoints
          (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
      else 0)) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ T - B := by
  have hdecomp := playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid
  linarith

private lemma playLength_le_answer_of_odd_lower_parametric {n : ℕ+} (s : Strategy (n : ℕ))
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ (n : ℕ))
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (odd : ℝ)
    (hodd : (n : ℝ) / (2 * (n : ℝ) + 1) ≤ odd)
    (htotal : (∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i) = 1)
    (hodd_def : odd = (∑ i : Fin (#s.points + #xiangPoints + 1),
      if Odd ((i : Fin _) : ℕ) then
        s.playPieceLength xiangPoints
          (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
      else 0)) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ answer n := by
  have hbound := playLength_le_of_odd_lower_parametric s xiangPoints hcard hd xiangClaims hvalid
    htotal (B := (n : ℝ) / (2 * (n : ℝ) + 1)) (by simpa [hodd_def] using hodd)
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hidentity : 1 - (n : ℝ) / (2 * (n : ℝ) + 1) = answer n := by
    dsimp [answer]
    field_simp
    ring
  calc
    s.playLength xiangPoints hcard hd xiangClaims ≤
        1 - (n : ℝ) / (2 * (n : ℝ) + 1) := hbound
    _ = answer n := hidentity

private lemma playLength_add_odd_play_sum_eq_one_parametric {n : ℕ+} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims +
      (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) = 1 := by
  calc
    s.playLength xiangPoints hcard hd xiangClaims +
        (∑ i : Fin (#s.points + #xiangPoints + 1),
          if Odd ((i : Fin _) : ℕ) then
            s.playPieceLength xiangPoints
              (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
          else 0) =
        ∑ i : Fin (#s.points + #xiangPoints + 1), s.playPieceLength xiangPoints i :=
      playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid
    _ = 1 := total_piece_sum_eq_one_parametric s xiangPoints hd

private lemma score_le_answer_of_odd_lower {n : ℕ+} {score odd : ℝ}
    (htotal : score + odd = 1)
    (hodd : (n : ℝ) / (2 * (n : ℝ) + 1) ≤ odd) :
    score ≤ answer n := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hidentity : ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) +
      (n : ℝ) / (2 * (n : ℝ) + 1) = 1 := by
    field_simp
    ring
  dsimp [answer]
  linarith

private lemma playLength_le_answer_of_odd_lower {n : ℕ+}
    (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (hodd : (n : ℝ) / (2 * (n : ℝ) + 1) ≤
      ∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ answer n := by
  have hsum := playLength_add_odd_play_sum_eq_total_new
    s xiangPoints hcard hd xiangClaims hvalid
  have htotal := total_piece_sum_eq_one_parametric s xiangPoints hd
  have hidentity : answer n + (n : ℝ) / (2 * (n : ℝ) + 1) = 1 := by
    dsimp [answer]
    field_simp
    ring
  linarith

private lemma alternating_sum_bound_parametric {m : ℕ} (a : Fin (m + 1) → ℝ)
    (b : Fin m → ℝ) (q total : ℝ)
    (hpair : ∀ i : Fin m, a i.succ ≤ b i)
    (htotal : (∑ i : Fin (m + 1), a i) + (∑ i : Fin m, b i) = total)
    (hfirst : a 0 ≤ q) :
    (∑ i : Fin (m + 1), a i) ≤ (total + q) / 2 := by
  have htail : (∑ i : Fin m, a i.succ) ≤ (∑ i : Fin m, b i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ] at htotal ⊢
  linarith

private lemma play_slot_not_mem_prefix {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (m : ℕ) (hm : m ≤ #s.points + #xiangPoints + 1)
    (k : Fin (#s.points + #xiangPoints + 1)) (hk : m ≤ (k : ℕ)) :
    s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) k ∉
      Set.range (fun j : Fin m =>
        s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1)
          ⟨j, j.isLt.trans_le hm⟩) := by
  intro hmem
  rcases hmem with ⟨j, hj⟩
  have hEq : (⟨j, j.isLt.trans_le hm⟩ : Fin (#s.points + #xiangPoints + 1)) = k :=
    hvalid hj
  have hval : (j : ℕ) = (k : ℕ) := congrArg Fin.val hEq
  omega

private lemma sum_le_half_of_injective_pair
    {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    {e : Fin n → Fin (n + 1)} {z : Fin (n + 1)} {q : ℝ}
    (he : Function.Injective e)
    (hz : z ∉ Set.range e)
    (ha : ∀ i, 0 ≤ a i)
    (hpair : ∀ i, b i ≤ a (e i))
    (hterm : q ≤ a z)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1) :
    (∑ i : Fin n, b i) ≤ (1 - q) / 2 := by
  classical
  have hpair_sum : (∑ i : Fin n, b i) ≤ ∑ i : Fin n, a (e i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  let im : Finset (Fin (n + 1)) := Finset.univ.image e
  have him_eq : im.sum a = ∑ i : Fin n, a (e i) := by
    dsimp [im]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact he hij
  have hsubset : im ⊆ (Finset.univ : Finset (Fin (n + 1))).erase z := by
    intro x hx
    have hxne : x ≠ z := by
      intro hxz
      rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
      apply hz
      exact ⟨i, hix.trans hxz⟩
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ x⟩
  have him_le : im.sum a ≤
      ((Finset.univ : Finset (Fin (n + 1))).erase z).sum a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx hxim
      exact ha x)
  have hsum : (∑ i : Fin n, b i) + q ≤ ∑ i : Fin (n + 1), a i := by
    calc
      (∑ i : Fin n, b i) + q ≤ im.sum a + a z := by
        rw [him_eq]
        exact add_le_add hpair_sum hterm
      _ ≤ ((Finset.univ : Finset (Fin (n + 1))).erase z).sum a + a z := by
        linarith [him_le]
      _ = ∑ i : Fin (n + 1), a i := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ z)
  linarith

private lemma exists_disjoint_points {n : ℕ} (s : Finset (Set.Ioo (0 : ℝ) 1)) :
    ∃ t : Finset (Set.Ioo (0 : ℝ) 1), #t = n ∧ Disjoint s t := by
  classical
  let U := oddGrid (#s + n)
  let V := U.filter (fun x => x ∉ s)
  have hU : #U = #s + n := by
    dsimp [U]
    exact odd_grid_card (#s + n)
  have hmem : #(U.filter (fun x => x ∈ s)) ≤ #s := by
    apply Finset.card_le_card
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hsplit := U.card_filter_add_card_filter_not
    (fun x : Set.Ioo (0 : ℝ) 1 => x ∈ s)
  have hV : n ≤ #V := by
    dsimp [V]
    omega
  obtain ⟨t, htv, ht⟩ := V.exists_subset_card_eq hV
  refine ⟨t, ht, ?_⟩
  rw [Finset.disjoint_left]
  intro x hxs hxt
  have hxV : x ∈ V := htv hxt
  exact (Finset.mem_filter.mp hxV).2 hxs

private lemma sum_le_half_of_finite_injective_pair
    {α β : Type*} [Fintype α] [Fintype β]
    {a : α → ℝ} {b : β → ℝ} {e : β → α} {z : α} {q : ℝ}
    (he : Function.Injective e)
    (hz : z ∉ Set.range e)
    (ha : ∀ i, 0 ≤ a i)
    (hpair : ∀ i, b i ≤ a (e i))
    (hterm : q ≤ a z)
    (htotal : (∑ i : α, a i) + (∑ i : β, b i) = 1) :
    (∑ i : β, b i) ≤ (1 - q) / 2 := by
  classical
  have hpair_sum : (∑ i : β, b i) ≤ ∑ i : β, a (e i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  let im : Finset α := Finset.univ.image e
  have him_eq : im.sum a = ∑ i : β, a (e i) := by
    dsimp [im]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact he hij
  have hsubset : im ⊆ (Finset.univ : Finset α).erase z := by
    intro x hx
    have hxne : x ≠ z := by
      intro hxz
      rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
      apply hz
      exact ⟨i, hix.trans hxz⟩
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ x⟩
  have him_le : im.sum a ≤ ((Finset.univ : Finset α).erase z).sum a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx hxim
      exact ha x)
  have hsum : (∑ i : β, b i) + q ≤ ∑ i : α, a i := by
    calc
      (∑ i : β, b i) + q ≤ im.sum a + a z := by
        rw [him_eq]
        exact add_le_add hpair_sum hterm
      _ ≤ ((Finset.univ : Finset α).erase z).sum a + a z := by
        linarith [him_le]
      _ = ∑ i : α, a i := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ z)
  linarith

private lemma opponent_play_prefix {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k ≤ #s.points + #xiangPoints + 1) :
    s.play xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd) k =
      opponentPrefix s xiangPoints hcard hd k hk := by
  induction k with
  | zero => simp [Strategy.play, opponentPrefix]
  | succ k ih =>
      have hk' : k ≤ #s.points + #xiangPoints + 1 := by omega
      have hprev := ih hk'
      simp only [Strategy.play, opponentPrefix]
      rw [hprev]
      by_cases he : Even k
      · have hkbound : k ≤ #s.points + #xiangPoints := by omega
        simp [he, hkbound]
      · obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp he
        subst k
        have hdiv : (2 * m + 1) / 2 = m := by omega
        have hbound : 2 * m + 2 ≤ #s.points + #xiangPoints + 1 := by omega
        rw [hdiv]
        simp [opponentClaims, hbound]
        simp [opponentPrefix, he]
        have hidx :
            (⟨2 * m + 1, by omega⟩ : Fin (2 * m + 2)) = Fin.last (2 * m + 1) := by
          apply Fin.ext
          rfl
        rw [hidx, Fin.snoc_last]

private lemma candidate_odd_sum_le_of_first_gap {n : ℕ+}
    {a : Fin ((n : ℕ) + 1) → ℝ} {b : Fin (n : ℕ) → ℝ}
    (hpair : ∀ i : Fin (n : ℕ), b i ≤ a i.castSucc)
    (hterm : 1 / (2 * (n : ℝ) + 1) ≤ a (Fin.last (n : ℕ)))
    (htotal : (∑ i : Fin ((n : ℕ) + 1), a i) +
      (∑ i : Fin (n : ℕ), b i) = 1) :
    (∑ i : Fin (n : ℕ), b i) ≤ (n : ℝ) / (2 * (n : ℝ) + 1) := by
  have h := candidate_odd_sum_le_of_pair_terminal hpair hterm htotal
  have hidentity : (1 - 1 / (2 * (n : ℝ) + 1)) / 2 =
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
    have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [← hidentity]
  exact h

lemma evidence_even_grid_below_xiang {n : ℕ} (i j : Fin n) :
    (2 * (j : ℝ) + 2) / (2 * (n : ℝ) + 1) <
      2 * (n : ℝ) / (2 * (n : ℝ) + 1) +
        ((i : ℝ) + 1) / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) := by
  have hd : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hjnat : j.1 + 1 ≤ n := Nat.succ_le_of_lt j.2
  have hjreal : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hjnat
  have hleft : (2 * (j : ℝ) + 2) / (2 * (n : ℝ) + 1) ≤
      2 * (n : ℝ) / (2 * (n : ℝ) + 1) := by
    apply (div_le_div_iff_of_pos_right hd).2
    nlinarith
  have hfrac : 0 < ((i : ℝ) + 1) /
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) := by positivity
  linarith

private lemma opponent_claims_valid {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) :
    s.PlayValid xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd) := by
  unfold Strategy.PlayValid
  have hprefix := opponent_play_prefix s xiangPoints hcard hd
    (#s.points + #xiangPoints + 1) (by rfl)
  rw [hprefix]
  exact opponentPrefix_injective s xiangPoints hcard hd
    (#s.points + #xiangPoints + 1) (by rfl)

lemma evidence_xiang_mem {n : ℕ} (i : Fin n) :
    (0 : ℝ) < 2 * (n : ℝ) / (2 * (n : ℝ) + 1) +
        ((i : ℝ) + 1) / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) ∧
      2 * (n : ℝ) / (2 * (n : ℝ) + 1) +
        ((i : ℝ) + 1) / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) < 1 := by
  have hd : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hD : 0 < (2 * (n : ℝ) + 1) * ((n : ℝ) + 1) := mul_pos hd hn1
  constructor
  · positivity
  · have hi : (i : ℝ) < (n : ℝ) := by exact_mod_cast i.2
    have hfrac : ((i : ℝ) + 1) /
        ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) <
          1 / (2 * (n : ℝ) + 1) := by
      apply (div_lt_iff₀ hD).2
      calc
        (i : ℝ) + 1 < (n : ℝ) + 1 := by linarith
        _ = (1 / (2 * (n : ℝ) + 1)) *
            ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) := by
          field_simp
    calc
      2 * (n : ℝ) / (2 * (n : ℝ) + 1) +
          ((i : ℝ) + 1) / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) <
        2 * (n : ℝ) / (2 * (n : ℝ) + 1) + 1 / (2 * (n : ℝ) + 1) := by linarith
      _ = 1 := by
        field_simp

private lemma test_fin_snoc_injective {m : ℕ} {α : Type} (f : Fin m → α) (x : α)
    (hnot : x ∉ Set.range f) (hinj : Function.Injective f) :
    Function.Injective (Fin.snoc f x) := by
  intro a b hab
  by_cases ha : a.val < m
  · let ai : Fin m := ⟨a.val, ha⟩
    have haeq : a = ai.castSucc := by
      apply Fin.ext
      rfl
    by_cases hb : b.val < m
    · let bi : Fin m := ⟨b.val, hb⟩
      have hbeq : b = bi.castSucc := by
        apply Fin.ext
        rfl
      have hab' : f ai = f bi := by
        simpa [haeq, hbeq] using hab
      have hi : ai = bi := hinj hab'
      rw [haeq, hbeq, hi]
    · have hbeq : b = Fin.last m := by
        apply Fin.ext
        simp
        omega
      have hax : f ai = x := by
        simpa [haeq, hbeq] using hab
      exact False.elim (hnot ⟨ai, hax⟩)
  · have haeq : a = Fin.last m := by
      apply Fin.ext
      simp
      omega
    by_cases hb : b.val < m
    · let bi : Fin m := ⟨b.val, hb⟩
      have hbeq : b = bi.castSucc := by
        apply Fin.ext
        rfl
      have hax : x = f bi := by
        simpa [haeq, hbeq] using hab
      exact False.elim (hnot ⟨bi, hax.symm⟩)
    · have hbeq : b = Fin.last m := by
        apply Fin.ext
        simp
        omega
      rw [haeq, hbeq]

private lemma opponent_claims_eq_maxFreeIndex {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (m : ℕ) (hm : 2 * m + 2 ≤ #s.points + #xiangPoints + 1) :
    opponentClaims s xiangPoints hcard hd m =
      maxFreeIndex
        (fun i => s.playPieceLength xiangPoints i)
        (opponentPrefix s xiangPoints hcard hd (2 * m + 1) (by omega))
        (fin_exists_not_mem_range_of_le (2 * m + 1) (#s.points + #xiangPoints)
          (by omega)
          (opponentPrefix s xiangPoints hcard hd (2 * m + 1) (by omega))) := by
  have hi : (⟨2 * m + 1, by omega⟩ : Fin (2 * m + 2)) = Fin.last (2 * m + 1) := Fin.ext rfl
  simp [opponentClaims, hm, opponentPrefix, hi]

private lemma odd_grid_first_gap_arithmetic {p n : ℕ} (hp : p ≤ n) :
    (2 * (p : ℝ) + 1) / (2 * ((p + n : ℕ) : ℝ) + 1) ≤
      ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) := by
  have h₁ : 0 < 2 * ((p + n : ℕ) : ℝ) + 1 := by positivity
  have h₂ : 0 < 2 * (n : ℝ) + 1 := by positivity
  rw [Nat.cast_add]
  field_simp
  have hp' : (p : ℝ) ≤ n := by exact_mod_cast hp
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hdiff : 0 ≤ 2 * (n : ℝ) + 1 - 2 * (p : ℝ) := by nlinarith
  have hprod := mul_nonneg hn hdiff
  nlinarith

private lemma sorted_second_le_mem {l : List ℝ} {x : ℝ}
    (hs : l.Pairwise (· ≤ ·)) (hfirst : l.getD 0 0 = 0)
    (hx : x ∈ l) (hxpos : 0 < x) : l.getD 1 0 ≤ x := by
  cases l with
  | nil => simp at hx
  | cons a l =>
      have ha : a = 0 := by simpa using hfirst
      subst a
      cases l with
      | nil =>
          have hx0 : x = 0 := by simpa using hx
          linarith
      | cons b l =>
          simp only [List.mem_cons] at hx
          simp only [List.getD_cons_succ, List.getD_cons_zero]
          rcases hx with hx0 | hxb | hx
          · linarith
          · simpa [hxb]
          · have htail := (List.pairwise_cons.mp hs).2
            exact (List.pairwise_cons.mp htail).1 x hx

private lemma playLength_add_odd_eq_one_parametric {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims +
      (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) = 1 := by
  rw [playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid]
  exact total_piece_sum_eq_one_parametric s xiangPoints hd

private lemma test_opponent_prefix_last {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k + 1 ≤ #s.points + #xiangPoints + 1) :
    opponentPrefix s xiangPoints hcard hd (k + 1) hk (Fin.last k) =
      (if Even k then
        s.claims xiangPoints hcard hd k (by omega)
          (opponentPrefix s xiangPoints hcard hd k (by omega))
      else
        maxFreeIndex
          (fun i => s.playPieceLength xiangPoints i)
          (opponentPrefix s xiangPoints hcard hd k (by omega))
          (fin_exists_not_mem_range_of_le k (#s.points + #xiangPoints)
            (by omega) (opponentPrefix s xiangPoints hcard hd k (by omega)))) := by
  simp [opponentPrefix, Fin.snoc]
  by_cases he : Even k <;> simp [he]

private lemma opponentClaims_eq_prefix_last {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (m : ℕ) (hm : 2 * m + 2 ≤ #s.points + #xiangPoints + 1) :
    opponentClaims s xiangPoints hcard hd m =
      opponentPrefix s xiangPoints hcard hd (2 * m + 2) hm
        ⟨2 * m + 1, by omega⟩ := by
  simp [opponentClaims, hm]

private lemma fin_snoc_injective_test {k N : ℕ} {f : Fin k → Fin N} {x : Fin N}
    (hf : Function.Injective f) (hx : x ∉ Set.range f) :
    Function.Injective (Fin.snoc f x) := by
  intro i j hij
  by_cases hi : i.val = k
  · have hi' : i = Fin.last k := by
      apply Fin.ext
      exact hi
    subst i
    by_cases hj : j.val = k
    · have hj' : j = Fin.last k := by
        apply Fin.ext
        exact hj
      exact hj'.symm
    · have hjlt : j.val < k := by omega
      have hval : x = f (Fin.castLT j hjlt) := by
        simpa [Fin.snoc, hjlt] using hij
      exact False.elim (hx ⟨Fin.castLT j hjlt, hval.symm⟩)
  · have hilt : i.val < k := by omega
    by_cases hj : j.val = k
    · have hj' : j = Fin.last k := by
        apply Fin.ext
        exact hj
      subst j
      have hval : f (Fin.castLT i hilt) = x := by
        simpa [Fin.snoc, hilt] using hij
      exact False.elim (hx ⟨Fin.castLT i hilt, hval⟩)
    · have hjlt : j.val < k := by omega
      have hval : f (Fin.castLT i hilt) = f (Fin.castLT j hjlt) := by
        simpa [Fin.snoc, hilt, hjlt] using hij
      have heq : Fin.castLT i hilt = Fin.castLT j hjlt := hf hval
      apply Fin.ext
      simpa using congrArg Fin.val heq


private lemma opponent_prefix_last_eq_claim {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k + 1 ≤ #s.points + #xiangPoints + 1) (he : Even k) :
    opponentPrefix s xiangPoints hcard hd (k + 1) hk (Fin.last k) =
      (s.claims xiangPoints hcard hd k (by omega)
        (opponentPrefix s xiangPoints hcard hd k (by omega)) : Fin (#s.points + #xiangPoints + 1)) := by
  simp [opponentPrefix, Fin.snoc, he]

private lemma playLength_eq_one_sub_odd_sum_parametric {n : ℕ}
    (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims =
      1 - (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
        else 0) := by
  have hsplit := playLength_add_odd_play_sum_eq_total_new
    s xiangPoints hcard hd xiangClaims hvalid
  have htotal := total_piece_sum_eq_one_parametric s xiangPoints hd
  linarith

private noncomputable def oddGreedyStrategy (n : ℕ) : Strategy n :=
  { points := oddGrid n
    card_points_le := by rw [odd_grid_card]
    claims := by
      intro xiangPoints hcard hd m hm priorClaims
      have hfree : ∃ i : Fin (#(oddGrid n) + #xiangPoints + 1),
          i ∉ Set.range priorClaims := by
        apply fin_exists_not_mem_range_of_le m (#(oddGrid n) + #xiangPoints)
        exact hm
      exact maxFreeIndex
        (fun i => (strategyOfPoints n (oddGrid n) (by rw [odd_grid_card])).playPieceLength
          xiangPoints i) priorClaims hfree }

private lemma oddGreedy_claim_is_max {n : ℕ}
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint (oddGrid n) xiangPoints) (m : ℕ)
    (hm : m ≤ #(oddGrid n) + #xiangPoints)
    (priorClaims : Fin m → Fin (#(oddGrid n) + #xiangPoints + 1)) :
    ∀ j ∉ Set.range priorClaims,
      (oddGreedyStrategy n).playPieceLength xiangPoints j ≤
        (oddGreedyStrategy n).playPieceLength xiangPoints
          ((oddGreedyStrategy n).claims xiangPoints hcard hd m hm priorClaims) := by
  intro j hj
  have hp (i : Fin (#(oddGrid n) + #xiangPoints + 1)) :
      (oddGreedyStrategy n).playPieceLength xiangPoints i =
        (strategyOfPoints n (oddGrid n) (by rw [odd_grid_card])).playPieceLength xiangPoints i := by
    rfl
  rw [hp, hp]
  simpa [oddGreedyStrategy] using
    (maxFreeIndex_max
      (fun i => (strategyOfPoints n (oddGrid n) (by rw [odd_grid_card])).playPieceLength xiangPoints i)
      priorClaims
      (fin_exists_not_mem_range_of_le m (#(oddGrid n) + #xiangPoints) hm priorClaims)
      j hj)

private lemma result_lower_branch_cut {n : ℕ+}
    (hgreedyOdd : ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (hcard : #xiangPoints ≤ n)
      (hd : Disjoint (greedyStrategy n).points xiangPoints)
      (xiangClaims : ℕ → Fin (#(greedyStrategy n).points + #xiangPoints + 1)),
      (hvalid : (greedyStrategy n).PlayValid xiangPoints hcard hd xiangClaims) →
      (∑ i : Fin (#(greedyStrategy n).points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          (greedyStrategy n).playPieceLength xiangPoints
            ((greedyStrategy n).play xiangPoints hcard hd xiangClaims
              (#(greedyStrategy n).points + #xiangPoints + 1) i)
        else 0) ≤ (n : ℝ) / (2 * (n : ℝ) + 1)) :
    ∃ s : Strategy n, ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
      (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
      (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints hcard hd xiangClaims →
      answer n ≤ s.playLength xiangPoints hcard hd xiangClaims := by
  refine ⟨greedyStrategy n, ?_⟩
  intro xiangPoints hcard hd xiangClaims hvalid
  apply candidate_score_lower_of_odd_bound (n := n) (greedyStrategy n)
    xiangPoints hcard hd xiangClaims hvalid
    (total_piece_sum_eq_one_parametric (greedyStrategy n) xiangPoints hd)
  exact hgreedyOdd xiangPoints hcard hd xiangClaims hvalid

private lemma result_upper_branch_from_forcing_cut {n : ℕ+} {c : ℝ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    (hc : c ≤ s.playLength xiangPoints hcard hd xiangClaims)
    (hodd : (n : ℝ) / (2 * (n : ℝ) + 1) ≤
      (∑ i : Fin (#s.points + #xiangPoints + 1),
        if Odd ((i : Fin _) : ℕ) then
          s.playPieceLength xiangPoints
            (s.play xiangPoints hcard hd xiangClaims
              (#s.points + #xiangPoints + 1) i)
        else 0)) :
    c ≤ answer n := by
  have htotal := total_piece_sum_eq_one_parametric s xiangPoints hd
  have hupper := playLength_le_of_odd_lower_parametric s xiangPoints hcard hd
    xiangClaims hvalid htotal hodd
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hidentity : 1 - (n : ℝ) / (2 * (n : ℝ) + 1) = answer n := by
    dsimp [answer]
    field_simp
    ring
  linarith

private lemma greedy_odd_le_even_before_candidate {n : ℕ}
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint (greedyStrategy n).points xiangPoints)
    (xiangClaims : ℕ → Fin (#(greedyStrategy n).points + #xiangPoints + 1))
    (hvalid : (greedyStrategy n).PlayValid xiangPoints hcard hd xiangClaims)
    (i : ℕ)
    (hi : 2 * i + 1 < #(greedyStrategy n).points + #xiangPoints + 1) :
    (greedyStrategy n).playPieceLength xiangPoints
        ((greedyStrategy n).play xiangPoints hcard hd xiangClaims
          (#(greedyStrategy n).points + #xiangPoints + 1)
          ⟨2 * i + 1, hi⟩) ≤
      (greedyStrategy n).playPieceLength xiangPoints
        ((greedyStrategy n).play xiangPoints hcard hd xiangClaims
          (#(greedyStrategy n).points + #xiangPoints + 1)
          ⟨2 * i, by omega⟩) := by
  let N := #(greedyStrategy n).points + #xiangPoints + 1
  have hi0 : 2 * i ≤ #(greedyStrategy n).points + #xiangPoints := by omega
  let prior : Fin (2 * i) → Fin N :=
    (greedyStrategy n).play xiangPoints hcard hd xiangClaims (2 * i)
  have hfree :
      ((greedyStrategy n).play xiangPoints hcard hd xiangClaims N
        ⟨2 * i + 1, by dsimp [N]; omega⟩) ∉ Set.range prior := by
    intro hmem
    rcases hmem with ⟨j, hj⟩
    have hprefix := play_prefix (greedyStrategy n) xiangPoints hcard hd xiangClaims
      (2 * i) N (by dsimp [N]; omega) j
    have heq :
        (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨2 * i + 1, by dsimp [N]; omega⟩ =
          (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨j.val, by dsimp [N]; omega⟩ := by
      calc
        (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨2 * i + 1, by dsimp [N]; omega⟩ = prior j := hj.symm
        _ = (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨j.val, by dsimp [N]; omega⟩ := hprefix
    have hidx := hvalid heq
    have hval : 2 * i + 1 = j.val := by
      exact congrArg (fun z : Fin N => z.val) hidx
    omega
  have hmax := greedy_claim_is_max_probe xiangPoints hcard
    (by simpa [greedyStrategy] using hd) (2 * i) hi0 prior
  have hmax' := hmax
    ((greedyStrategy n).play xiangPoints hcard hd xiangClaims N
      ⟨2 * i + 1, by dsimp [N]; omega⟩) hfree
  have hev : Even (2 * i) := ⟨i, by omega⟩
  have hfull_even :
      (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
          ⟨2 * i, by dsimp [N]; omega⟩ =
        (greedyStrategy n).claims xiangPoints hcard hd (2 * i) hi0 prior := by
    rw [← play_prefix (greedyStrategy n) xiangPoints hcard hd xiangClaims
      (2 * i + 1) N (by dsimp [N]; omega) ⟨2 * i, by omega⟩]
    simp [N, prior, Strategy.play, Fin.snoc, hev, dif_pos hi0]
  change (greedyStrategy n).playPieceLength xiangPoints
      ((greedyStrategy n).play xiangPoints hcard hd xiangClaims N
        ⟨2 * i + 1, by dsimp [N]; omega⟩) ≤
    (greedyStrategy n).playPieceLength xiangPoints
      ((greedyStrategy n).claims xiangPoints hcard hd (2 * i) hi0 prior) at hmax'
  rw [← hfull_even] at hmax'
  exact hmax'

private lemma reciprocal_le_of_sum_eq_one_of_le {N : ℕ} (f : Fin (N + 1) → ℝ)
    (hmax : ∀ i, f i ≤ f 0)
    (htotal : (∑ i : Fin (N + 1), f i) = 1) :
    1 / ((N : ℝ) + 1) ≤ f 0 := by
  have hs : (1 : ℝ) ≤ ((N : ℝ) + 1) * f 0 := by
    calc
      (1 : ℝ) = ∑ i : Fin (N + 1), f i := htotal.symm
      _ ≤ ∑ i : Fin (N + 1), f 0 := by
        exact Finset.sum_le_sum (fun i hi => hmax i)
      _ = ((N : ℝ) + 1) * f 0 := by simp
  have hden : 0 < (N : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

private lemma opponentPrefix_last {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : k + 1 ≤ #s.points + #xiangPoints + 1) :
    opponentPrefix s xiangPoints hcard hd (k + 1) hk (Fin.last k) =
      if Even k then
        (s.claims xiangPoints hcard hd k (by omega)
          (opponentPrefix s xiangPoints hcard hd k (by omega)) : Fin (#s.points + #xiangPoints + 1))
      else
        (maxFreeIndex (fun i => s.playPieceLength xiangPoints i)
          (opponentPrefix s xiangPoints hcard hd k (by omega))
          (fin_exists_not_mem_range_of_le k (#s.points + #xiangPoints) (by omega)
            (opponentPrefix s xiangPoints hcard hd k (by omega))) : Fin (#s.points + #xiangPoints + 1)) := by
  simp [opponentPrefix]

private lemma answer_sub_half_eq_gap {n : ℕ+} :
    answer n - (1 / 2 : ℝ) = 1 / (2 * (2 * (n : ℝ) + 1)) := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  dsimp [answer]
  field_simp
  ring

private lemma opponent_odd_ge_next_claim {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (k : ℕ) (hk : 2 * k + 3 ≤ #s.points + #xiangPoints + 1) :
    s.playPieceLength xiangPoints
        (opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)
          ⟨2 * k + 1, by omega⟩) ≥
      s.playPieceLength xiangPoints
        (s.claims xiangPoints hcard hd (2 * k + 2) (by omega)
          (opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega))) := by
  let f : Fin (#s.points + #xiangPoints + 1) → ℝ :=
    s.playPieceLength xiangPoints
  let prior : Fin (2 * k + 1) → Fin (#s.points + #xiangPoints + 1) :=
    opponentPrefix s xiangPoints hcard hd (2 * k + 1) (by omega)
  let longer : Fin (2 * k + 2) → Fin (#s.points + #xiangPoints + 1) :=
    opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)
  have hfree : ∃ j : Fin (#s.points + #xiangPoints + 1), j ∉ Set.range prior := by
    apply fin_exists_not_mem_range_of_le (2 * k + 1) (#s.points + #xiangPoints)
    omega
  let p : Fin (#s.points + #xiangPoints + 1) :=
    s.claims xiangPoints hcard hd (2 * k + 2) (by omega) longer
  have hp : p ∉ Set.range prior := by
    intro hp
    rcases hp with ⟨i, hi⟩
    have hlong : p ∈ Set.range longer := by
      refine ⟨i.castSucc, ?_⟩
      simpa [prior, longer, opponentPrefix] using hi
    exact (strategy_claim_fresh s xiangPoints hcard hd (2 * k + 2) (by omega) longer) hlong
  have hmax := maxFreeIndex_max f prior hfree p hp
  have hidx : (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 2)) = Fin.last (2 * k + 1) := by
    apply Fin.ext
    rfl
  have hoddval :
      f (opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)
          (Fin.last (2 * k + 1))) = f (maxFreeIndex f prior hfree) := by
    simp [opponentPrefix, f, prior]
  change f (opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)
      (⟨2 * k + 1, by omega⟩ : Fin (2 * k + 2))) ≥ f p
  rw [hidx, hoddval]
  exact hmax

private lemma greedy_odd_bound_arithmetic {n : ℕ+} {m : ℕ} (hm : m ≤ (n : ℕ)) :
    (1 - 1 / (((n : ℕ) + m : ℝ) + 1)) / 2 ≤
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) := by positivity
  have hm' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hden' : (0 : ℝ) < (((n : ℕ) + m : ℝ) + 1) := by positivity
  field_simp [ne_of_gt hden, ne_of_gt hden']
  nlinarith

private lemma alternating_sum_lower_equal {m : ℕ} (a b : Fin (m + 1) → ℝ) (q total : ℝ)
    (hpair : ∀ i : Fin m, a i.succ ≤ b i.castSucc)
    (hbn : ∀ i : Fin (m + 1), 0 ≤ b i)
    (htotal : (∑ i : Fin (m + 1), a i) + (∑ i : Fin (m + 1), b i) = total)
    (hfirst : a 0 ≤ q) :
    (total - q) / 2 ≤ ∑ i : Fin (m + 1), b i := by
  have htail : (∑ i : Fin m, a i.succ) ≤ (∑ i : Fin m, b i.castSucc) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at htotal
  rw [Fin.sum_univ_castSucc]
  have hlast : 0 ≤ b (Fin.last m) := hbn _
  linarith

private lemma oddGrid_sdiff_valid {n : ℕ} (s : Strategy n) :
    #(oddGrid n \ s.points) ≤ n ∧ Disjoint s.points (oddGrid n \ s.points) := by
  constructor
  · calc
      #(oddGrid n \ s.points) ≤ #(oddGrid n) := Finset.card_le_card Finset.sdiff_subset
      _ = n := odd_grid_card n
  · refine Finset.disjoint_left.2 ?_
    intro x hxS hxDiff
    exact (Finset.mem_sdiff.mp hxDiff).2 hxS

private lemma oddGrid_subset_union_sdiff {n : ℕ} (s : Strategy n) :
    oddGrid n ⊆ s.points ∪ (oddGrid n \ s.points) := by
  intro x hx
  by_cases hxs : x ∈ s.points
  · exact Finset.mem_union_left _ hxs
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxs⟩)

private lemma sum_le_half_of_finite_injective_pair_parametric
    {α β : Type*} [Fintype α] [Fintype β]
    {a : α → ℝ} {b : β → ℝ} {e : β → α} {z : α} {q total : ℝ}
    (he : Function.Injective e)
    (hz : z ∉ Set.range e)
    (ha : ∀ i : α, 0 ≤ a i)
    (hpair : ∀ i : β, b i ≤ a (e i))
    (hterm : q ≤ a z)
    (htotal : (∑ i : α, a i) + (∑ i : β, b i) = total) :
    (∑ i : β, b i) ≤ (total - q) / 2 := by
  classical
  have hpair_sum : (∑ i : β, b i) ≤ ∑ i : β, a (e i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  let im : Finset α := Finset.univ.image e
  have him_eq : im.sum a = ∑ i : β, a (e i) := by
    dsimp [im]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact he hij
  have hsubset : im ⊆ (Finset.univ : Finset α).erase z := by
    intro x hx
    have hxne : x ≠ z := by
      intro hxz
      rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
      apply hz
      exact ⟨i, hix.trans hxz⟩
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ x⟩
  have him_le : im.sum a ≤ ((Finset.univ : Finset α).erase z).sum a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx hxim
      exact ha x)
  have hsum : (∑ i : β, b i) + q ≤ ∑ i : α, a i := by
    calc
      (∑ i : β, b i) + q ≤ im.sum a + a z := by
        rw [him_eq]
        exact add_le_add hpair_sum hterm
      _ ≤ ((Finset.univ : Finset α).erase z).sum a + a z := by
        linarith [him_le]
      _ = ∑ i : α, a i := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ z)
  linarith [hsum, htotal]

private lemma odd_sum_lower_of_succ_le {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} {q : ℝ}
    (hpair : ∀ i : Fin n, a i.succ ≤ b i)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1)
    (hfirst : a 0 ≤ q) :
    (1 - q) / 2 ≤ ∑ i : Fin n, b i := by
  have htail : (∑ i : Fin n, a i.succ) ≤ (∑ i : Fin n, b i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_succ] at htotal
  linarith

private lemma odd_sum_lower_of_injective_pair
    {α β : Type*} [Fintype α] [Fintype β]
    {a0 : ℝ} {a : α → ℝ} {b : β → ℝ} {e : α → β} {q : ℝ}
    (he : Function.Injective e)
    (hb : ∀ j, 0 ≤ b j)
    (hpair : ∀ i, a i ≤ b (e i))
    (htotal : a0 + (∑ i : α, a i) + (∑ j : β, b j) = 1)
    (hfirst : a0 ≤ q) :
    (1 - q) / 2 ≤ ∑ j : β, b j := by
  classical
  have hpair_sum : (∑ i : α, a i) ≤ ∑ i : α, b (e i) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  let im : Finset β := Finset.univ.image e
  have him_eq : im.sum b = ∑ i : α, b (e i) := by
    dsimp [im]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact he hij
  have hsubset : im ⊆ (Finset.univ : Finset β) := by
    intro x hx
    exact Finset.mem_univ x
  have him_le : im.sum b ≤ (Finset.univ : Finset β).sum b := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx hxim
      exact hb x)
  linarith [hpair_sum, him_eq, him_le]

private lemma opponent_witness_reduction {n : ℕ} (s : Strategy n) :
    ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)),
      ∃ (hcard : #xiangPoints ≤ n),
      ∃ (hd : Disjoint s.points xiangPoints),
      ∃ (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      ∃ (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims),
      ∃ odd : ℝ,
        odd = (∑ i : Fin (#s.points + #xiangPoints + 1),
          if Odd ((i : Fin _) : ℕ) then
            s.playPieceLength xiangPoints
              (s.play xiangPoints hcard hd xiangClaims
                (#s.points + #xiangPoints + 1) i)
          else 0) ∧
        (∑ i : Fin (#s.points + #xiangPoints + 1),
          s.playPieceLength xiangPoints i) = 1 := by
  obtain ⟨t, htcard, htd⟩ := exists_disjoint_points (n := n) s.points
  let hcard : #t ≤ n := by omega
  let claims : ℕ → Fin (#s.points + #t + 1) := opponentClaims s t hcard htd
  have hvalid : s.PlayValid t hcard htd claims := by
    exact opponent_claims_valid s t hcard htd
  refine ⟨t, hcard, htd, claims, hvalid, ?_, ?_, ?_⟩
  · exact ∑ i : Fin (#s.points + #t + 1),
      if Odd ((i : Fin _) : ℕ) then
        s.playPieceLength t (s.play t hcard htd claims (#s.points + #t + 1) i)
      else 0
  · rfl
  · exact total_piece_sum_eq_one_parametric s t htd

private lemma parity_total_decomposition {N : ℕ} (f : Fin (N + 1) → ℝ) :
    f 0 + (∑ i : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0}, f i.1) +
      (∑ i : {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}, f i.1) = ∑ i : Fin (N + 1), f i := by
  classical
  let E : Finset (Fin (N + 1)) := Finset.univ.filter (fun i => Even ((i : Fin (N + 1)) : ℕ))
  let O : Finset (Fin (N + 1)) := Finset.univ.filter (fun i => Odd ((i : Fin (N + 1)) : ℕ))
  let EvenTail := {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0}
  let OddIndex := {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}
  have htail : (∑ i : EvenTail, f i.1) = (E.erase 0).sum f := by
    refine Finset.sum_bij (f := fun i : EvenTail => f i.1) (g := f)
      (s := (Finset.univ : Finset EvenTail)) (t := E.erase 0)
      (fun i _ => i.1) ?_ ?_ ?_ ?_
    · intro i hi
      apply Finset.mem_erase.mpr
      refine ⟨i.2.2, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, i.2.1⟩
    · intro i₁ hi₁ i₂ hi₂ h
      exact Subtype.ext h
    · intro b hb
      rcases Finset.mem_erase.mp hb with ⟨hb0, hbE⟩
      have hbEven : Even ((b : Fin (N + 1)) : ℕ) :=
        (Finset.mem_filter.mp hbE).2
      refine ⟨⟨b, hbEven, hb0⟩, Finset.mem_univ _, ?_⟩
      rfl
    · intro i hi
      rfl
  have hodd : (∑ i : OddIndex, f i.1) = O.sum f := by
    refine Finset.sum_bij (f := fun i : OddIndex => f i.1) (g := f)
      (s := (Finset.univ : Finset OddIndex)) (t := O)
      (fun i _ => i.1) ?_ ?_ ?_ ?_
    · intro i hi
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, i.2⟩
    · intro i₁ hi₁ i₂ hi₂ h
      exact Subtype.ext h
    · intro b hb
      have hbOdd : Odd ((b : Fin (N + 1)) : ℕ) :=
        (Finset.mem_filter.mp hb).2
      refine ⟨⟨b, hbOdd⟩, Finset.mem_univ _, ?_⟩
      rfl
    · intro i hi
      rfl
  have hE : (E.erase 0).sum f + f 0 = E.sum f := by
    exact Finset.sum_erase_add _ _ (by simp [E])
  have hpart : E.sum f + O.sum f = ∑ i : Fin (N + 1), f i := by
    simpa [E, O] using (even_odd_sum_partition f)
  dsimp [EvenTail, OddIndex] at htail hodd ⊢
  linarith [htail, hodd, hE, hpart]

private lemma odd_sum_lower_of_parity_decomposition {N : ℕ}
    (f : Fin (N + 1) → ℝ) {q : ℝ}
    (e : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0} →
      {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)})
    (he : Function.Injective e)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hpair : ∀ i, f i.1 ≤ f (e i).1)
    (htotal : f 0 +
      (∑ i : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0}, f i.1) +
      (∑ i : {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}, f i.1) = 1)
    (hfirst : f 0 ≤ q) :
    (1 - q) / 2 ≤ (∑ i : Fin (N + 1) with Odd ((i : Fin (N + 1)) : ℕ), f i) := by
  classical
  let OddIndex := {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}
  have hb : ∀ j : OddIndex, 0 ≤ f j.1 := by
    intro j
    exact hnonneg j.1
  have h := odd_sum_lower_of_injective_pair
    (a := fun i : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0} => f i.1)
    (b := fun j : OddIndex => f j.1) he hb hpair htotal hfirst
  have hodd : (∑ j : OddIndex, f j.1) =
      ∑ i : Fin (N + 1) with Odd ((i : Fin (N + 1)) : ℕ), f i := by
    let O : Finset (Fin (N + 1)) := Finset.univ.filter
      (fun i => Odd ((i : Fin (N + 1)) : ℕ))
    refine Finset.sum_bij (f := fun j : OddIndex => f j.1) (g := f)
      (s := (Finset.univ : Finset OddIndex)) (t := O)
      (fun j _ => j.1) ?_ ?_ ?_ ?_
    · intro j hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, j.2⟩
    · intro j₁ hj₁ j₂ hj₂ h'
      exact Subtype.ext h'
    · intro b hb'
      have hbodd : Odd ((b : Fin (N + 1)) : ℕ) :=
        (Finset.mem_filter.mp hb').2
      refine ⟨⟨b, hbodd⟩, Finset.mem_univ _, ?_⟩
      rfl
    · intro j hj
      rfl
  rw [hodd] at h
  exact h

private lemma playLength_le_answer_iff_odd_lower_research {n : ℕ+} (s : Strategy (n : ℕ))
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ (n : ℕ))
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims) :
    s.playLength xiangPoints hcard hd xiangClaims ≤ answer n ↔
      (n : ℝ) / (2 * (n : ℝ) + 1) ≤
        (∑ i : Fin (#s.points + #xiangPoints + 1),
          if Odd ((i : Fin _) : ℕ) then
            s.playPieceLength xiangPoints
              (s.play xiangPoints hcard hd xiangClaims
                (#s.points + #xiangPoints + 1) i)
          else 0) := by
  have hsum := playLength_add_odd_play_sum_eq_one_parametric
    s xiangPoints hcard hd xiangClaims hvalid
  have hidentity : answer n + (n : ℝ) / (2 * (n : ℝ) + 1) = 1 := by
    dsimp [answer]
    field_simp
    ring
  constructor <;> intro h
  · linarith
  · linarith

private lemma playLength_ge_of_odd_upper_total {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1))
    (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims)
    {T B : ℝ}
    (htotal : (∑ i : Fin (#s.points + #xiangPoints + 1),
      s.playPieceLength xiangPoints i) = T)
    (hodd : (∑ i : Fin (#s.points + #xiangPoints + 1),
      if Odd ((i : Fin _) : ℕ) then
        s.playPieceLength xiangPoints
          (s.play xiangPoints hcard hd xiangClaims (#s.points + #xiangPoints + 1) i)
      else 0) ≤ B) :
    T - B ≤ s.playLength xiangPoints hcard hd xiangClaims := by
  have hdecomp := playLength_add_odd_play_sum_eq_total_new s xiangPoints hcard hd xiangClaims hvalid
  linarith

lemma audit_answer_n2 : (1 / 2 : ℝ) < answer (2 : ℕ+) := by
  norm_num [answer]

private lemma greedy_claim_dominates_free_bridge {n : ℕ}
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint (evenGrid n) xiangPoints)
    (m : ℕ) (hm : m ≤ #(evenGrid n) + #xiangPoints)
    (priorClaims : Fin m → Fin (#(evenGrid n) + #xiangPoints + 1))
    (j : Fin (#(evenGrid n) + #xiangPoints + 1))
    (hj : j ∉ Set.range priorClaims) :
    (strategyOfPoints n (evenGrid n) (by rw [even_grid_card])).playPieceLength xiangPoints j ≤
      (greedyStrategy n).playPieceLength xiangPoints
        ((greedyStrategy n).claims xiangPoints hcard hd m hm priorClaims) := by
  exact greedy_claim_is_max_probe xiangPoints hcard hd m hm priorClaims j hj

private lemma opponent_max_pair_given_fresh {n : ℕ}
    (s : Strategy n) (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n) (hd : Disjoint s.points xiangPoints)
    (m : ℕ) (hm : 2 * m + 2 ≤ #s.points + #xiangPoints + 1)
    (j : Fin (#s.points + #xiangPoints + 1))
    (hj : j ∉ Set.range (opponentPrefix s xiangPoints hcard hd (2 * m + 1) (by omega))) :
    s.playPieceLength xiangPoints j ≤
      s.playPieceLength xiangPoints (opponentClaims s xiangPoints hcard hd m) := by
  rw [opponent_claims_eq_maxFreeIndex s xiangPoints hcard hd m hm]
  exact maxFreeIndex_max (fun i => s.playPieceLength xiangPoints i)
    (opponentPrefix s xiangPoints hcard hd (2 * m + 1) (by omega))
    (fin_exists_not_mem_range_of_le (2 * m + 1) (#s.points + #xiangPoints)
      (by omega) (opponentPrefix s xiangPoints hcard hd (2 * m + 1) (by omega)))
    j hj

private lemma max_piece_ge_of_total {n N : ℕ} (f : Fin N → ℝ) (c : Fin N)
    (hN : 0 < N) (hmax : ∀ j : Fin N, f j ≤ f c)
    (hnonneg : ∀ j : Fin N, 0 ≤ f j)
    (htotal : (∑ j : Fin N, f j) = 1)
    (hNle : N ≤ 2 * n + 1) :
    1 / (2 * (n : ℝ) + 1) ≤ f c := by
  have htop := top_sum_bound f (fun _ : Fin 1 => c) (by
    intro i j
    exact hmax j)
  have hsum : (1 : ℝ) ≤ (N : ℝ) * f c := by
    simpa [htotal] using htop
  have hNreal : 0 < (N : ℝ) := by positivity
  have hNle_real : (N : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    exact_mod_cast hNle
  have hfc : 0 ≤ f c := hnonneg c
  have hden : 0 < 2 * (n : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith

private lemma even_grid_split_odd_residual_exceeds_bound {r : ℕ} {b : ℝ}
    (hb : 0 < b) :
    (2 * (r : ℝ)) / (4 * (r : ℝ) + 1) <
      (r : ℝ) * (2 / (4 * (r : ℝ) + 1)) + b := by
  have hden : 4 * (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  nlinarith

private lemma even_grid_split_odd_sum_exceeds_bound {r : ℕ} {b O : ℝ}
    (hb : 0 < b)
    (hO : O = (∑ _i : Fin r, 2 / (4 * (r : ℝ) + 1)) + b) :
    (2 * (r : ℝ)) / (4 * (r : ℝ) + 1) < O := by
  have hsum : (∑ _i : Fin r, 2 / (4 * (r : ℝ) + 1)) =
      (r : ℝ) * (2 / (4 * (r : ℝ) + 1)) := by simp
  rw [hO, hsum]
  have hden : 4 * (r : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hden]
  nlinarith

private lemma even_length_odd_bound_boundary {n : ℕ+} {m k : ℕ}
    (hm : m ≤ (n : ℕ)) (_hP : (n : ℕ) + m = 2 * k) (f : Fin (2 * k + 1) → ℝ)
    (hnext : ∀ i : Fin k, f ⟨2 * (i : ℕ) + 1, by omega⟩ ≤
      f ⟨2 * (i.succ : ℕ), by omega⟩)
    (htotal : (∑ i : Fin (2 * k + 1), f i) = 1)
    (hfirst : 1 / ((((n : ℕ) + m : ℝ) + 1)) ≤ f ⟨0, by omega⟩) :
    (∑ i : Fin (2 * k + 1) with Odd ((i : Fin (2 * k + 1)) : ℕ), f i) ≤
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
  have hodd := alternating_odd_bound_fin f hnext htotal hfirst
  have harith := greedy_odd_bound_arithmetic (n := n) (m := m) hm
  exact le_trans hodd harith

private lemma odd_sum_bound_of_prev_le_terminal {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} {q : ℝ}
    (hpair : ∀ i : Fin n, b i ≤ a i.castSucc)
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1)
    (hlast : q ≤ a (Fin.last n)) :
    (∑ i : Fin n, b i) ≤ (1 - q) / 2 := by
  have htail : (∑ i : Fin n, b i) ≤ (∑ i : Fin n, a i.castSucc) := by
    exact Finset.sum_le_sum (fun i hi => hpair i)
  rw [Fin.sum_univ_castSucc] at htotal
  linarith

private lemma odd_sum_identity_of_prev_pair {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1) :
    2 * (∑ i : Fin n, b i) =
      1 - a (Fin.last n) - (∑ i : Fin n, (a i.castSucc - b i)) := by
  rw [Fin.sum_univ_castSucc] at htotal
  rw [Finset.sum_sub_distrib]
  linarith

private lemma even_sum_ge_of_odd_sum_le {N : ℕ} {f : Fin N → ℝ} {B : ℝ}
    (htotal : (∑ i : Fin N, f i) = 1)
    (hodd : (∑ i : Fin N with Odd ((i : Fin N) : ℕ), f i) ≤ B) :
    1 - B ≤ ∑ i : Fin N with Even ((i : Fin N) : ℕ), f i := by
  have hpart := even_odd_sum_partition f
  linarith

private lemma greedy_odd_upper_of_residual {n N : ℕ} {f : Fin (N + 1) → ℝ}
    (hres : 1 / (2 * (n : ℝ) + 1) ≤
      (∑ i : Fin (N + 1) with Even ((i : Fin _) : ℕ), f i) -
        (∑ i : Fin (N + 1) with Odd ((i : Fin _) : ℕ), f i))
    (htotal : (∑ i : Fin (N + 1), f i) = 1) :
    (∑ i : Fin (N + 1) with Odd ((i : Fin _) : ℕ), f i) ≤
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
  have hpart := even_odd_sum_partition f
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hid : (1 - 1 / (2 * (n : ℝ) + 1)) / 2 =
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
    field_simp [hden]
    ring
  linarith

private lemma odd_sum_lower_target_of_injective_pair
    {n : ℕ+}
    {α β : Type*} [Fintype α] [Fintype β]
    {a0 : ℝ} {a : α → ℝ} {b : β → ℝ} {e : α → β}
    (he : Function.Injective e)
    (hb : ∀ j, 0 ≤ b j)
    (hpair : ∀ i, a i ≤ b (e i))
    (htotal : a0 + (∑ i : α, a i) + (∑ j : β, b j) = 1)
    (hfirst : a0 ≤ 1 / (2 * (n : ℝ) + 1)) :
    (n : ℝ) / (2 * (n : ℝ) + 1) ≤ ∑ j : β, b j := by
  have h := odd_sum_lower_of_injective_pair he hb hpair htotal hfirst
  have hidentity :
      (1 - 1 / (2 * (n : ℝ) + 1)) / 2 =
        (n : ℝ) / (2 * (n : ℝ) + 1) := by
    have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [← hidentity]
  exact h

private lemma parametric_odd_bound_of_terminal_pair {n : ℕ+} {m : ℕ}
    {a : Fin (m + 1) → ℝ} {b : Fin m → ℝ}
    (hpair : ∀ i : Fin m, b i ≤ a i.castSucc)
    (hterm : 1 / (2 * (n : ℝ) + 1) ≤ a (Fin.last m))
    (htotal : (∑ i : Fin (m + 1), a i) + (∑ i : Fin m, b i) = 1) :
    (∑ i : Fin m, b i) ≤ (n : ℝ) / (2 * (n : ℝ) + 1) := by
  have h := candidate_odd_sum_le_of_pair_terminal hpair hterm htotal
  have hidentity : (1 - 1 / (2 * (n : ℝ) + 1)) / 2 =
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
    have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [← hidentity]
  exact h

private lemma sum_le_half_of_injective_pair_fintype
    {α β : Type*} [Fintype α] [Fintype β]
    {a : α → ℝ} {b : β → ℝ} {e : β → α} {z : α} {q : ℝ}
    (he : Function.Injective e)
    (hz : z ∉ Set.range e)
    (ha : ∀ i, 0 ≤ a i)
    (hpair : ∀ i, b i ≤ a (e i))
    (hterm : q ≤ a z)
    (htotal : (∑ i : α, a i) + (∑ j : β, b j) = 1) :
    (∑ j : β, b j) ≤ (1 - q) / 2 := by
  classical
  have hpair_sum : (∑ j : β, b j) ≤ ∑ j : β, a (e j) := by
    exact Finset.sum_le_sum (fun j hj => hpair j)
  let im : Finset α := Finset.univ.image e
  have him_eq : im.sum a = ∑ j : β, a (e j) := by
    dsimp [im]
    rw [Finset.sum_image]
    intro i hi j hj hij
    exact he hij
  have hsubset : im ⊆ (Finset.univ : Finset α).erase z := by
    intro x hx
    have hxne : x ≠ z := by
      intro hxz
      rcases Finset.mem_image.mp hx with ⟨j, hj, hjx⟩
      apply hz
      exact ⟨j, hjx.trans hxz⟩
    exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ x⟩
  have him_le : im.sum a ≤ ((Finset.univ : Finset α).erase z).sum a := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
      intro x hx hxim
      exact ha x)
  have hsum : (∑ j : β, b j) + q ≤ ∑ i : α, a i := by
    calc
      (∑ j : β, b j) + q ≤ im.sum a + a z := by
        rw [him_eq]
        exact add_le_add hpair_sum hterm
      _ ≤ ((Finset.univ : Finset α).erase z).sum a + a z := by
        linarith [him_le]
      _ = ∑ i : α, a i := by
        exact Finset.sum_erase_add _ _ (Finset.mem_univ z)
  linarith

private lemma odd_sum_lower_reduction_boundary {N : ℕ} {q : ℝ}
    (f : Fin (N + 1) → ℝ)
    (e : {j : Fin (N + 1) //
      Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0} →
      {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)})
    (he : Function.Injective e)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hpair : ∀ i, f i.1 ≤ f (e i).1)
    (htotal : (∑ i : Fin (N + 1), f i) = 1)
    (hfirst : f 0 ≤ q) :
    (1 - q) / 2 ≤
      (∑ i : Fin (N + 1) with Odd ((i : Fin _) : ℕ), f i) := by
  have hpart := parity_total_decomposition f
  rw [htotal] at hpart
  exact odd_sum_lower_of_parity_decomposition f e he hnonneg hpair hpart hfirst

private lemma opponent_odd_lower_arith_bridge {p n : ℕ}
    (h : (2 * (p : ℝ) + 1) / (2 * ((p + n : ℕ) : ℝ) + 1) ≤
      ((n : ℝ) + 1) / (2 * (n : ℝ) + 1)) :
    (n : ℝ) / (2 * (n : ℝ) + 1) ≤
      1 - (2 * (p : ℝ) + 1) / (2 * ((p + n : ℕ) : ℝ) + 1) := by
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hid : (n : ℝ) / (2 * (n : ℝ) + 1) =
      1 - ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  calc
    (n : ℝ) / (2 * (n : ℝ) + 1) =
        1 - ((n : ℝ) + 1) / (2 * (n : ℝ) + 1) := hid
    _ ≤ 1 - (2 * (p : ℝ) + 1) / (2 * ((p + n : ℕ) : ℝ) + 1) := by linarith

private lemma audit_actual_odd_le_max_free {n : ℕ}
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint (greedyStrategy n).points xiangPoints)
    (xiangClaims : ℕ → Fin (#(greedyStrategy n).points + #xiangPoints + 1))
    (hvalid : (greedyStrategy n).PlayValid xiangPoints hcard hd xiangClaims)
    (m : ℕ)
    (hm : 2 * m + 2 ≤ #(greedyStrategy n).points + #xiangPoints + 1) :
    let N := #(greedyStrategy n).points + #xiangPoints + 1
    let prior : Fin (2 * m + 1) → Fin N := fun i =>
      (greedyStrategy n).play xiangPoints hcard hd xiangClaims (2 * m + 1) i
    let hfree : ∃ q : Fin N, q ∉ Set.range prior :=
      fin_exists_not_mem_range_of_le (2 * m + 1)
        (#(greedyStrategy n).points + #xiangPoints) (by omega) prior
    (greedyStrategy n).playPieceLength xiangPoints
        ((greedyStrategy n).play xiangPoints hcard hd xiangClaims N
          ⟨2 * m + 1, by omega⟩) ≤
      (greedyStrategy n).playPieceLength xiangPoints
        (maxFreeIndex
          (fun j => (greedyStrategy n).playPieceLength xiangPoints j)
          prior hfree) := by
  dsimp
  let N : ℕ := #(greedyStrategy n).points + #xiangPoints + 1
  let prior : Fin (2 * m + 1) → Fin N := fun i =>
    (greedyStrategy n).play xiangPoints hcard hd xiangClaims (2 * m + 1) i
  have hfree : ∃ q : Fin N, q ∉ Set.range prior := by
    exact fin_exists_not_mem_range_of_le (2 * m + 1)
      (#(greedyStrategy n).points + #xiangPoints) (by omega) prior
  have hodd : (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
      ⟨2 * m + 1, by omega⟩ ∉ Set.range prior := by
    intro h
    rcases h with ⟨i, hi⟩
    have hprefix := play_prefix (greedyStrategy n) xiangPoints hcard hd
      xiangClaims (2 * m + 1) N (by omega) i
    have heq :
        (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨2 * m + 1, by omega⟩ =
          (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨i.val, by omega⟩ := by
      calc
        (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨2 * m + 1, by omega⟩ = prior i := hi.symm
        _ = (greedyStrategy n).play xiangPoints hcard hd xiangClaims N
            ⟨i.val, by omega⟩ := hprefix
    have hargs := hvalid heq
    have hvals := congrArg Fin.val hargs
    have hvals' : 2 * m + 1 = i.val := by simpa using hvals
    have hilt : i.val < 2 * m + 1 := i.isLt
    omega
  exact maxFreeIndex_max
    (fun j => (greedyStrategy n).playPieceLength xiangPoints j)
    prior hfree
    ((greedyStrategy n).play xiangPoints hcard hd xiangClaims N
      ⟨2 * m + 1, by omega⟩) hodd

private lemma lower_odd_from_first_bound {n : ℕ+} {N : ℕ} (f : Fin (N + 1) → ℝ)
    (e : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ) ∧ (j : Fin (N + 1)) ≠ 0} →
      {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)})
    (he : Function.Injective e) (hnonneg : ∀ i, 0 ≤ f i)
    (hpair : ∀ i, f i.1 ≤ f (e i).1)
    (htotal : (∑ i : Fin (N + 1), f i) = 1)
    (hfirst : f 0 ≤ 1 / (2 * (n : ℝ) + 1)) :
    (n : ℝ) / (2 * (n : ℝ) + 1) ≤
      (∑ i : Fin (N + 1) with Odd ((i : Fin _) : ℕ), f i) := by
  have h := odd_sum_lower_reduction_boundary f e he hnonneg hpair htotal hfirst
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hid : (1 - 1 / (2 * (n : ℝ) + 1)) / 2 =
      (n : ℝ) / (2 * (n : ℝ) + 1) := by
    field_simp [hden]
    ring
  rw [← hid]
  exact h

private lemma first_piece_lower_of_card_bound {n : ℕ+} {N : ℕ} {f : Fin (N + 1) → ℝ}
    (hmax : ∀ i, f i ≤ f 0)
    (htotal : (∑ i : Fin (N + 1), f i) = 1)
    (hN : N ≤ 2 * (n : ℕ)) :
    1 / (2 * (n : ℝ) + 1) ≤ f 0 := by
  have hrec := reciprocal_le_of_sum_eq_one_of_le f hmax htotal
  have hdenN : 0 < (N : ℝ) + 1 := by positivity
  have hden : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hcast : (N : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast hN
  have hinv : 1 / (2 * (n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
    apply (div_le_div_iff₀ hden hdenN).2
    linarith
  exact le_trans hinv hrec

private lemma residual_of_prev_pair_checked {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ} {q : ℝ}
    (hpair : ∀ i : Fin n, b i ≤ a i.castSucc)
    (hterm : q ≤ a (Fin.last n))
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1) :
    q ≤ (∑ i : Fin (n + 1), a i) - (∑ i : Fin n, b i) := by
  have hid := odd_sum_identity_of_prev_pair htotal
  have hnonneg : 0 ≤ ∑ i : Fin n, (a i.castSucc - b i) := by
    apply Finset.sum_nonneg
    intro i hi
    linarith [hpair i]
  linarith [hid, htotal, hnonneg, hterm]

private lemma residual_identity_checked {n : ℕ} {a : Fin (n + 1) → ℝ} {b : Fin n → ℝ}
    (htotal : (∑ i : Fin (n + 1), a i) + (∑ i : Fin n, b i) = 1) :
    (∑ i : Fin (n + 1), a i) - (∑ i : Fin n, b i) =
      a (Fin.last n) + (∑ i : Fin n, (a i.castSucc - b i)) := by
  have hid := odd_sum_identity_of_prev_pair htotal
  linarith [hid, htotal]

private lemma parity_residual_lower_of_injective_pair
    {N : ℕ} {f : Fin (N + 1) → ℝ} {q : ℝ}
    (e : {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)} →
      {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)})
    (he : Function.Injective e)
    (hz : (⟨0, by simp⟩ : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)}) ∉ Set.range e)
    (hnonneg : ∀ i, 0 ≤ f i)
    (hpair : ∀ i, f i.1 ≤ f (e i).1)
    (htotal :
      (∑ i : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)}, f i.1) +
        (∑ j : {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}, f j.1) = 1)
    (hfirst : q ≤ f 0) :
    q ≤
      (∑ i : {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)}, f i.1) -
        (∑ j : {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)}, f j.1) := by
  have hhalf := sum_le_half_of_injective_pair_fintype
    (α := {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)})
    (β := {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)})
    (a := fun i => f i.1) (b := fun j => f j.1) (e := e)
    he hz (fun i => hnonneg i.1) hpair hfirst htotal
  linarith

private lemma test_sum_subtype_filter {N : ℕ} {f : Fin (N + 1) → ℝ}
    (p : Fin (N + 1) → Prop) [DecidablePred p] :
    (∑ i : {j : Fin (N + 1) // p j}, f i.1) =
      Finset.sum ((Finset.univ : Finset (Fin (N + 1))).filter p) f := by
  classical
  change Finset.sum (Finset.univ : Finset {j : Fin (N + 1) // p j}) (fun i => f i.1) =
    Finset.sum ((Finset.univ : Finset (Fin (N + 1))).filter p) f
  refine Finset.sum_bij
    (fun i (_ : i ∈ (Finset.univ : Finset {j : Fin (N + 1) // p j})) => i.1) ?_ ?_ ?_ ?_
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.2⟩
  · intro a₁ ha₁ a₂ ha₂ h
    exact Subtype.ext h
  · intro b hb
    exact ⟨⟨b, (Finset.mem_filter.mp hb).2⟩, Finset.mem_univ _, rfl⟩
  · intro a ha
    rfl

private lemma test_map {N : ℕ} :
    ∃ e :
      {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)} →
        {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)},
      Function.Injective e := by
  let e :
      {j : Fin (N + 1) // Odd ((j : Fin (N + 1)) : ℕ)} →
        {j : Fin (N + 1) // Even ((j : Fin (N + 1)) : ℕ)} :=
    fun j =>
      have hjlt : (j.1 : ℕ) < N + 1 := j.1.isLt
      ⟨⟨(j.1 : ℕ) - 1, by omega⟩, by
        obtain ⟨m, hm⟩ := j.2
        refine ⟨m, ?_⟩
        change (j.1 : ℕ) - 1 = m + m
        omega⟩
  refine ⟨e, ?_⟩
  intro i j hij
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg (fun x => (x.1 : ℕ)) hij
  dsimp [e] at hval
  obtain ⟨mi, hmi⟩ := i.2
  obtain ⟨mj, hmj⟩ := j.2
  omega

private lemma prev_pair_residual_identity_general {m : ℕ}
    {a : Fin (m + 1) → ℝ} {b : Fin m → ℝ} :
    (∑ i : Fin (m + 1), a i) - (∑ i : Fin m, b i) =
      a (Fin.last m) + (∑ i : Fin m, (a i.castSucc - b i)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Finset.sum_sub_distrib]
  ring

private lemma play_piece_nonneg_parametric {n : ℕ}
    (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1))
    (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints)
    (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)) :
    ∀ i : Fin (#s.points + #xiangPoints + 1),
      0 ≤ s.playPieceLength xiangPoints
        (s.play xiangPoints hcard hd xiangClaims
          (#s.points + #xiangPoints + 1) i) := by
  intro i
  exact play_pieceLength_nonneg s xiangPoints hd
    (s.play xiangPoints hcard hd xiangClaims
      (#s.points + #xiangPoints + 1) i)

private lemma opponent_play_even_le_odd {n : ℕ} (s : Strategy n)
    (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (hcard : #xiangPoints ≤ n)
    (hd : Disjoint s.points xiangPoints) (k : ℕ)
    (hk : 2 * k + 3 ≤ #s.points + #xiangPoints + 1) :
    s.playPieceLength xiangPoints
        (s.play xiangPoints hcard hd
          (opponentClaims s xiangPoints hcard hd)
          (#s.points + #xiangPoints + 1) ⟨2 * k + 2, by omega⟩) ≤
      s.playPieceLength xiangPoints
        (s.play xiangPoints hcard hd
          (opponentClaims s xiangPoints hcard hd)
          (#s.points + #xiangPoints + 1) ⟨2 * k + 1, by omega⟩) := by
  have h := opponent_odd_ge_next_claim s xiangPoints hcard hd k hk
  have hodd :
      s.play xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd)
          (#s.points + #xiangPoints + 1) ⟨2 * k + 1, by omega⟩ =
        opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)
          ⟨2 * k + 1, by omega⟩ := by
    calc
      _ = s.play xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd)
          (2 * k + 2) ⟨2 * k + 1, by omega⟩ := by
            exact (play_prefix s xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd)
              (2 * k + 2) (#s.points + #xiangPoints + 1) (by omega)
              ⟨2 * k + 1, by omega⟩).symm
      _ = _ := congrFun (opponent_play_prefix s xiangPoints hcard hd (2 * k + 2) (by omega))
        ⟨2 * k + 1, by omega⟩
  have hev :
      s.play xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd)
          (#s.points + #xiangPoints + 1) ⟨2 * k + 2, by omega⟩ =
        s.claims xiangPoints hcard hd (2 * k + 2) (by omega)
          (opponentPrefix s xiangPoints hcard hd (2 * k + 2) (by omega)) := by
    calc
      _ = opponentPrefix s xiangPoints hcard hd (2 * k + 3) (by omega)
          ⟨2 * k + 2, by omega⟩ := by
            have hp := play_prefix s xiangPoints hcard hd (opponentClaims s xiangPoints hcard hd)
              (2 * k + 3) (#s.points + #xiangPoints + 1) (by omega)
              ⟨2 * k + 2, by omega⟩
            have ho := congrFun (opponent_play_prefix s xiangPoints hcard hd
              (2 * k + 3) (by omega)) ⟨2 * k + 2, by omega⟩
            exact hp.symm.trans ho
      _ = _ := by
        have hlast := opponent_prefix_last_eq_claim s xiangPoints hcard hd
          (2 * k + 2) (by omega) (by exact ⟨k + 1, by omega⟩)
        have hidx : (⟨2 * k + 2, by omega⟩ : Fin (2 * k + 3)) = Fin.last (2 * k + 2) := by
          apply Fin.ext
          rfl
        rw [hidx]
        exact hlast
  rw [hodd, hev]
  exact h

theorem result {n : ℕ+} : IsGreatest {c | ∃ s : Strategy n,
    ∀ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)) (card_xiangPoints_le : #xiangPoints ≤ n)
      (hd : Disjoint s.points xiangPoints) (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
      s.PlayValid xiangPoints card_xiangPoints_le hd xiangClaims →
      c ≤ s.playLength xiangPoints card_xiangPoints_le hd xiangClaims} (answer n) := by
  classical
  simp only [IsGreatest]
  refine ⟨?_, ?_⟩
  · apply result_lower_branch_cut (n := n)
    intro xiangPoints hcard hd xiangClaims hvalid
    let P := #(greedyStrategy n).points + #xiangPoints
    let f : Fin (P + 1) → ℝ := fun i =>
      (greedyStrategy n).playPieceLength xiangPoints
        ((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1) i)
    have htotalf : (∑ i : Fin (P + 1), f i) = 1 := by
      dsimp [f, P]
      calc
        (∑ i : Fin (#(greedyStrategy n).points + #xiangPoints + 1),
            (greedyStrategy n).playPieceLength xiangPoints
              ((greedyStrategy n).play xiangPoints hcard hd xiangClaims
                (#(greedyStrategy n).points + #xiangPoints + 1) i)) =
            ∑ j : Fin (#(greedyStrategy n).points + #xiangPoints + 1),
              (greedyStrategy n).playPieceLength xiangPoints j :=
          play_sum_reindex (greedyStrategy n) xiangPoints hcard hd xiangClaims hvalid
        _ = 1 := total_piece_sum_eq_one_parametric (greedyStrategy n) xiangPoints hd
    have hmax0 : ∀ j : Fin (P + 1), f j ≤ f 0 := by
      let prior : Fin 0 → Fin (P + 1) := Fin.elim0
      have hmax := greedy_claim_is_max_probe xiangPoints hcard
        (by simpa [greedyStrategy] using hd) 0 (by omega) prior
      have hzero :
          (greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1)
              ⟨0, by omega⟩ =
            (greedyStrategy n).claims xiangPoints hcard hd 0 (by omega) prior := by
        rw [← play_prefix (greedyStrategy n) xiangPoints hcard hd xiangClaims
          1 (P + 1) (by omega) ⟨0, by omega⟩]
        simp [P, prior, Strategy.play, Fin.snoc]
      intro j
      have hj := hmax
        ((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1) j)
        (by simp [prior])
      change (greedyStrategy n).playPieceLength xiangPoints
          ((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1) j) ≤
        (greedyStrategy n).playPieceLength xiangPoints
          ((greedyStrategy n).claims xiangPoints hcard hd 0 (by omega) prior) at hj
      change (greedyStrategy n).playPieceLength xiangPoints
          ((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1) j) ≤
        (greedyStrategy n).playPieceLength xiangPoints
          ((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1)
            ⟨0, by omega⟩)
      rw [hzero]
      exact hj
    have hq0 := reciprocal_le_of_sum_eq_one_of_le f hmax0 htotalf
    have hPle : P ≤ 2 * (n : ℕ) := by
      change #(evenGrid (n : ℕ)) + #xiangPoints ≤ 2 * (n : ℕ)
      rw [even_grid_card]
      omega
    have htry := greedy_odd_le_even_before_candidate xiangPoints hcard
      (by simpa [greedyStrategy] using hd) xiangClaims hvalid 0 (by
        simpa [greedyStrategy, even_grid_card] using
          (show 1 ≤ (n : ℕ) + #xiangPoints by omega))
    rw [← Finset.sum_filter]
    apply greedy_odd_upper_of_residual
    have hpair : ∀ m : ℕ, ∀ hm : 2 * m + 2 ≤ P + 1,
        f ⟨2 * m + 1, by omega⟩ ≤ f ⟨2 * m, by omega⟩ := by
      intro m hm
      dsimp [P] at hm
      have hm' : 2 * m + 2 ≤ #(greedyStrategy n).points + #xiangPoints + 1 := by
        simpa [greedyStrategy, even_grid_card] using hm
      dsimp [f, P]
      exact greedy_odd_le_even_before_candidate xiangPoints hcard
        (by simpa [greedyStrategy] using hd) xiangClaims hvalid m hm'
    have hfirst := first_piece_lower_of_card_bound (n := n) (N := P)
      hmax0 htotalf hPle
    have hnonneg : ∀ i : Fin (P + 1), 0 ≤ f i := by
      intro i
      dsimp [f]
      unfold Strategy.playPieceLength
      let j : Fin ((greedyStrategy n).playEnds xiangPoints).length :=
        ⟨((greedyStrategy n).play xiangPoints hcard hd xiangClaims (P + 1) i : ℕ), by
          rw [probe_playEnds_length (greedyStrategy n) xiangPoints hd]
          dsimp [P]
          omega⟩
      have hj := adjacent_getD_nonneg
        ((greedyStrategy n).playEnds xiangPoints)
        (play_ends_sorted (greedyStrategy n) xiangPoints) j (by
          dsimp [j]
          rw [probe_playEnds_length (greedyStrategy n) xiangPoints hd]
          dsimp [P]
          omega)
      simpa [j] using hj
    sorry
    exact htotalf
  · intro c hc
    rcases hc with ⟨s, hs⟩
    have hex : ∃ (xiangPoints : Finset (Set.Ioo (0 : ℝ) 1)),
        ∃ (hcard : #xiangPoints ≤ (n : ℕ)),
        ∃ (hd : Disjoint s.points xiangPoints),
        ∃ (xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1)),
        ∃ (hvalid : s.PlayValid xiangPoints hcard hd xiangClaims),
        ∃ odd : ℝ,
          (n : ℝ) / (2 * (n : ℝ) + 1) ≤ odd ∧
          (∑ i : Fin (#s.points + #xiangPoints + 1),
            s.playPieceLength xiangPoints i) = 1 ∧
          odd = (∑ i : Fin (#s.points + #xiangPoints + 1),
            if Odd ((i : Fin _) : ℕ) then
              s.playPieceLength xiangPoints
                (s.play xiangPoints hcard hd xiangClaims
                  (#s.points + #xiangPoints + 1) i)
            else 0) := by
      let U := oddGrid (#s.points + (n : ℕ))
      let V := U.filter (fun x => x ∉ s.points)
      have hU : #U = #s.points + (n : ℕ) := by
        dsimp [U]
        exact odd_grid_card (#s.points + (n : ℕ))
      have hmem : #(U.filter (fun x => x ∈ s.points)) ≤ #s.points := by
        apply Finset.card_le_card
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hsplit := U.card_filter_add_card_filter_not
        (fun x : Set.Ioo (0 : ℝ) 1 => x ∈ s.points)
      have hUsub : U ⊆ s.points ∪ V := by
        let t : Strategy (#s.points + (n : ℕ)) :=
          strategyOfPoints (#s.points + (n : ℕ)) s.points (by omega)
        have ht := oddGrid_subset_union_sdiff t
        change oddGrid (#s.points + (n : ℕ)) ⊆
          s.points ∪ (oddGrid (#s.points + (n : ℕ)) \ s.points) at ht
        simpa [U, V, Finset.sdiff_eq_filter] using ht
      have hV : (n : ℕ) ≤ #V := by
        dsimp [V]
        omega
      have h_arith := odd_grid_first_gap_arithmetic (p := #s.points)
        (n := (n : ℕ)) s.card_points_le
      obtain ⟨xiangPoints, htv, hcard_eq⟩ := V.exists_subset_card_eq hV
      have hcard : #xiangPoints ≤ (n : ℕ) := by omega
      have hd : Disjoint s.points xiangPoints := by
        rw [Finset.disjoint_left]
        intro x hxs hxt
        have hxV : x ∈ V := htv hxt
        exact (Finset.mem_filter.mp hxV).2 hxs
      let xiangClaims : ℕ → Fin (#s.points + #xiangPoints + 1) :=
        opponentClaims s xiangPoints hcard hd
      have hvalid : s.PlayValid xiangPoints hcard hd xiangClaims := by
        exact opponent_claims_valid s xiangPoints hcard hd
      refine ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, ?_⟩
      let odd : ℝ :=
        ∑ i : Fin (#s.points + #xiangPoints + 1),
          if Odd ((i : Fin _) : ℕ) then
            s.playPieceLength xiangPoints
              (s.play xiangPoints hcard hd xiangClaims
                (#s.points + #xiangPoints + 1) i)
          else 0
      refine ⟨odd, ?_, ?_, ?_⟩
      · have hnonneg : ∀ i : Fin (#s.points + #xiangPoints + 1),
            0 ≤ s.playPieceLength xiangPoints
              (s.play xiangPoints hcard hd xiangClaims
                (#s.points + #xiangPoints + 1) i) := by
          intro i
          exact play_piece_nonneg_parametric s xiangPoints hcard hd xiangClaims i
        sorry
      · exact total_piece_sum_eq_one_parametric s xiangPoints hd
      · rfl
    rcases hex with ⟨xiangPoints, hcard, hd, xiangClaims, hvalid, odd,
      hodd, htotal, hodd_def⟩
    exact le_trans (hs xiangPoints hcard hd xiangClaims hvalid)
      (playLength_le_answer_of_odd_lower_parametric s xiangPoints hcard hd
        xiangClaims hvalid odd hodd htotal hodd_def)

end IMO2026P3
