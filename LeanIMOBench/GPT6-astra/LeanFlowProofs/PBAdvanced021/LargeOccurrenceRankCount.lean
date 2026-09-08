import LeanFlowProofs.PBAdvanced021.NoLargeLarge
import Mathlib

theorem LeanFlow.pb021_large_occurrence_rank_count {c : ℕ → ℕ} {N B : ℕ} (hN : 0 < N) (hpos : ∀ i : ℕ, 0 < i → 0 < c i) (hNB : N ≤ B) (hinit : ∀ i : ℕ, 1 ≤ i → i ≤ N → c i ≤ B) (hrule : ∀ t : ℕ, N ≤ t → c (t + 1) = ((Finset.Icc 1 t).filter (fun i => c i = c t)).card) : ∀ t y : ℕ, N ≤ t → B < y → ((Finset.Icc 1 t).filter (fun i => c i = y)).card = ((Finset.Icc 1 B).filter (fun j => y ≤ ((Finset.Ico 1 t).filter (fun i => c i = j)).card)).card := by 
  classical
  let q (t j : ℕ) := ((Finset.Ico 1 t).filter (fun i => c i = j)).card
  have hinc (t j : ℕ) (ht : 0 < t) :
      ((Finset.Icc 1 t).filter (fun i => c i = j)).card =
        q t j + if c t = j then 1 else 0 := by
    have he : Finset.Icc 1 t = insert t (Finset.Ico 1 t) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [he, Finset.filter_insert]
    by_cases h : c t = j <;> simp [h, q, Finset.mem_filter, Finset.mem_Ico, Nat.add_comm]
  have hq (t j : ℕ) (ht : 0 < t) :
      q (t + 1) j = q t j + if c t = j then 1 else 0 := by
    have he : Finset.Ico 1 (t + 1) = Finset.Icc 1 t := by
      ext i
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    simpa only [q, he] using hinc t j ht
  intro t y ht hy
  induction t, ht using Nat.le_induction with
  | base =>
    have hl : (Finset.Icc 1 N).filter (fun i => c i = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi
      have := hinit i hi.1.1 hi.1.2
      omega
    have hr : (Finset.Icc 1 B).filter (fun j => y ≤ q N j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hb : q N j ≤ N := by
        have := Finset.card_filter_le (Finset.Ico 1 N) (fun i => c i = j)
        simp only [Nat.card_Ico] at this
        dsimp [q]
        omega
      have := (Finset.mem_filter.mp hj).2
      omega
    change _ = ((Finset.Icc 1 B).filter (fun j => y ≤ q N j)).card
    rw [hl, hr]
  | succ t ht ih =>
    have htpos : 0 < t := by omega
    have hrule' : c (t + 1) = q t (c t) + 1 := by
      rw [hrule t ht, hinc t (c t) htpos]
      simp
    let R := (Finset.Icc 1 B).filter (fun j => y ≤ q t j)
    have hL : ((Finset.Icc 1 (t + 1)).filter (fun i => c i = y)).card =
        ((Finset.Icc 1 t).filter (fun i => c i = y)).card +
          if c (t + 1) = y then 1 else 0 := by
      rw [hinc (t + 1) y (by omega), hq t y htpos, hinc t y htpos]
    by_cases he : c (t + 1) = y
    · have hc : c t ≤ B := by
        rcases pb021_no_large_large hN hpos hNB hinit hrule t ht with h | h
        · exact h
        · omega
      have hn : c t ∉ R := by
        simp only [R, Finset.mem_filter, Finset.mem_Icc]
        omega
      have hR : (Finset.Icc 1 B).filter (fun j => y ≤ q (t + 1) j) = insert (c t) R := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, R]
        rw [hq t j htpos]
        have hp := hpos t htpos
        by_cases hj : c t = j
        · subst j
          simp only [ite_true, eq_self_iff_true, true_or, iff_true]
          omega
        · simp [hj, Ne.symm hj]
      change _ = ((Finset.Icc 1 B).filter (fun j => y ≤ q (t + 1) j)).card
      rw [hL, hR, Finset.card_insert_of_notMem hn, if_pos he]
      change _ + 1 = R.card + 1
      exact congrArg (fun n => n + 1) ih
    · have hR : (Finset.Icc 1 B).filter (fun j => y ≤ q (t + 1) j) = R := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc, R]
        rw [hq t j htpos]
        by_cases hj : c t = j
        · subst j
          simp only [ite_true]
          omega
        · simp [hj]
      change _ = ((Finset.Icc 1 B).filter (fun j => y ≤ q (t + 1) j)).card
      rw [hL, hR, if_neg he, Nat.add_zero]
      exact ih

