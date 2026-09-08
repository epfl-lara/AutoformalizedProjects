import LeanFlowProofs.PB021EventualAlternation
import LeanFlowProofs.PB021LargeOccurrenceRankCount
import Mathlib

theorem LeanFlow.pb021_eventual_rank_representation {c : ℕ → ℕ} {N B : ℕ} (hN : 0 < N) (hpos : ∀ i : ℕ, 0 < i → 0 < c i) (hNB : N ≤ B) (hinit : ∀ i : ℕ, 1 ≤ i → i ≤ N → c i ≤ B) (hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card) : ∃ t0 : ℕ, N ≤ t0 ∧ ∃ A : ℕ → Fin B → ℕ, ∃ x : ℕ → Fin B, (∀ n : ℕ, c (t0 + 2 * n) = (x n).val + 1) ∧ (∀ (n : ℕ) (i : Fin B), A (n + 1) i = A n i + (if i = x n then 1 else 0)) ∧ (∀ n : ℕ, (x (n + 1)).val + 1 = (Finset.univ.filter (fun j : Fin B => A (n + 1) (x n) ≤ A (n + 1) j)).card) := by   classical
  obtain ⟨t0, ht0, halt⟩ := LeanFlow.pb021_eventual_small_large_alternation hN hpos hNB hinit hrule
  let q (t j : ℕ) := ((Finset.Ico 1 t).filter (fun k => c k = j)).card
  have qs (t j : ℕ) (ht : 1 ≤ t) : q (t + 1) j = q t j + (if c t = j then 1 else 0) := by
    have he : Finset.Ico 1 (t + 1) = insert t (Finset.Ico 1 t) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    dsimp [q]
    rw [he]
    by_cases h : c t = j <;> simp [Finset.filter_insert, h, Finset.mem_Ico]
  let x (n : ℕ) : Fin B := ⟨c (t0 + 2 * n) - 1, by
    have := (halt n).1
    have := hpos (t0 + 2 * n) (by omega)
    omega⟩
  have hx (n : ℕ) : c (t0 + 2 * n) = (x n).val + 1 := by
    have := hpos (t0 + 2 * n) (by omega)
    dsimp [x]
    omega
  let A (n : ℕ) (i : Fin B) := q (t0 + 2 * n) (i.val + 1)
  have hskip (n : ℕ) (i : Fin B) : A (n + 1) i = q (t0 + 2 * n + 1) (i.val + 1) := by
    have hn : t0 + 2 * (n + 1) = (t0 + 2 * n + 1) + 1 := by omega
    dsimp [A]
    rw [hn, qs _ _ (by omega)]
    have hne : c (t0 + 2 * n + 1) ≠ i.val + 1 := by
      have := (halt n).2
      have := i.isLt
      omega
    simp [hne]
  refine ⟨t0, ht0, A, x, hx, ?_, ?_⟩
  · intro n i
    rw [hskip, qs _ _ (by omega)]
    have he : c (t0 + 2 * n) = i.val + 1 ↔ i = x n := by
      rw [hx]
      constructor
      · intro h
        apply Fin.ext
        omega
      · intro h
        simp [h]
    simp only [he]
    rfl
  · intro n
    have hy : c (t0 + 2 * n + 1) = A (n + 1) (x n) := by
      rw [hskip, hrule _ (by omega)]
      dsimp [q]
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      rw [hx]
      omega
    have hr := LeanFlow.pb021_large_occurrence_rank_count hN hpos hNB hinit hrule
      (t0 + 2 * n + 1) (c (t0 + 2 * n + 1)) (by omega) (halt n).2
    rw [← hx (n + 1)]
    have hn : t0 + 2 * (n + 1) = (t0 + 2 * n + 1) + 1 := by omega
    rw [hn, hrule _ (by omega), hr]
    symm
    apply Finset.card_bij (fun i _ => i.val + 1)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by have := i.isLt; omega⟩, ?_⟩
      change c (t0 + 2 * n + 1) ≤ q (t0 + 2 * n + 1) (i.val + 1)
      rw [hy, ← hskip]
      exact hi
    · intro i hi j hj hij
      apply Fin.ext
      omega
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      let i : Fin B := ⟨j - 1, by omega⟩
      have hij : i.val + 1 = j := by dsimp [i]; omega
      refine ⟨i, ?_, hij⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hy, hskip n i, hij]
      exact hj.2

