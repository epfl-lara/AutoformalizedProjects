import LeanFlowProofs.PB021EventualRankRepresentation
import LeanFlowProofs.PB021RankWalkPeriodicity
import Mathlib

/-- The property that a sequence `c` of positive integers satisfies the recursive rule
starting from index `N + 1`. Indices start at 1. -/
def SatisfiesRule (c : ℕ → ℕ) (N : ℕ) : Prop :=
  (N > 0) ∧
  -- (1) All chosen numbers are positive integers (for i ≥ 1).
  (∀ i : ℕ, i > 0 → c i > 0) ∧
  -- (2) For m > N, the rule applies.
  (∀ m : ℕ, m > N →
    -- The set of indices {k | 1 ≤ k ≤ m - 2} is Finset.Icc 1 (m - 2)
    c m = 1 + Finset.card (
      (Finset.Icc 1 (m - 2)).filter (fun k => c k = c (m - 1)))
    )

variable (c : ℕ → ℕ)

/-- The sequence of numbers chosen by the boys (at odd positions 1, 3, 5, ...). -/
def boys_sequence : ℕ → ℕ :=
  fun i => c (2 * i - 1)

/-- The sequence of numbers chosen by the girls (at even positions 2, 4, 6, ...). -/
def girls_sequence : ℕ → ℕ :=
  fun i => c (2 * i)

/-- A sequence `a : ℕ → ℕ` is eventually periodic. We require the starting index M and period P to be positive. -/
def IsEventuallyPeriodic (a : ℕ → ℕ) : Prop :=
  -- M is the index after which periodicity starts, P is the period.
  ∃ M P : ℕ, M > 0 ∧ P > 0 ∧ ∀ n : ℕ, n ≥ M → a n = a (n + P)

-- The main claim of the problem: At least one of the gender subsequences is eventually periodic.
theorem PBAdvanced021 {N : ℕ} (h_valid : SatisfiesRule c N) :
  IsEventuallyPeriodic (boys_sequence c) ∨ IsEventuallyPeriodic (girls_sequence c) := by classical
  rcases h_valid with ⟨hN, hpos, hr⟩
  have hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hN ht
    have heq : Finset.Icc 1 t = insert t (Finset.Icc 1 (t - 1)) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hr (t + 1) (by omega), heq]
    simp only [Finset.filter_insert, ite_true]
    rw [Finset.card_insert_of_notMem]
    · have h1 : t + 1 - 2 = t - 1 := by omega
      simp only [h1, Nat.add_sub_cancel]
      omega
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
  let B := N + (Finset.Icc 1 N).sum c
  have hNB : N ≤ B := Nat.le_add_right _ _
  have hinit : ∀ i : ℕ, 1 ≤ i → i ≤ N → c i ≤ B := by
    intro i hi hiN
    have hh : c i ≤ (Finset.Icc 1 N).sum c := Finset.single_le_sum (fun j hj => Nat.zero_le (c j)) (Finset.mem_Icc.mpr ⟨hi, hiN⟩)
    dsimp [B]
    omega
  obtain ⟨t0, ht0, A, x, hc, hstep, hrank⟩ := LeanFlow.pb021_eventual_rank_representation hN hpos hNB hinit hrule
  obtain ⟨M, P, hM, hP, hp⟩ := LeanFlow.pb021_rank_walk_eventually_periodic (lt_of_lt_of_le hN hNB) A x hstep hrank
  have hperiod : ∀ n, M ≤ n → c (t0 + 2 * n) = c (t0 + 2 * (n + P)) := by
    intro n hn
    rw [hc, hc, hp n hn]
  have hmod : t0 % 2 = 0 ∨ t0 % 2 = 1 := by omega
  rcases hmod with heven | hodd
  · right
    refine ⟨t0 / 2 + M, P, by omega, hP, ?_⟩
    intro n hn
    dsimp [girls_sequence]
    have h := hperiod (n - t0 / 2) (by omega)
    convert h using 1 <;> congr 1 <;> omega
  · left
    refine ⟨t0 / 2 + 1 + M, P, by omega, hP, ?_⟩
    intro n hn
    dsimp [boys_sequence]
    have h := hperiod (n - (t0 / 2 + 1)) (by omega)
    convert h using 1 <;> congr 1 <;> omega
