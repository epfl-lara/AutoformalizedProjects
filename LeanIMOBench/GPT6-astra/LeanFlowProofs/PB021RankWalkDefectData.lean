import LeanFlowProofs.PB021SortedIncrementIdentity
import LeanFlowProofs.PB021SortedPrefixDominance
import Mathlib

theorem LeanFlow.pb021_rank_walk_defect_data {d : ℕ} (A : ℕ → Fin d → ℕ) (x : ℕ → Fin d) (hstep : ∀ (n : ℕ) (i : Fin d), A (n + 1) i = A n i + (if i = x n then 1 else 0)) (hrank : ∀ n : ℕ, (x (n + 1)).val + 1 = (Finset.univ.filter (fun j : Fin d => A (n + 1) (x n) ≤ A (n + 1) j)).card) : ∃ s : ℕ → Fin d → ℕ, ∃ b : Fin d → ℤ, (∀ n : ℕ, Antitone (s n)) ∧ (∀ n : ℕ, ∃ e : Equiv.Perm (Fin d), ∀ i : Fin d, s n i = A n (e i)) ∧ (∀ (n : ℕ) (i : Fin d), (A n i : ℤ) + (if i = x n then (1 : ℤ) else 0) - (s n i : ℤ) = b i) ∧ (∀ K : ℕ, K ≤ d → (Finset.univ.filter (fun i : Fin d => i.val < K)).sum b ≤ 1) ∧ Finset.univ.sum b = 1 := by 
  classical
  let e (n : ℕ) := Tuple.sort (α := OrderDual ℕ) (fun i => A n i)
  let s (n : ℕ) (i : Fin d) : ℕ := A n (e n i)
  have hs : ∀ n, Antitone (s n) := by
    intro n
    exact Tuple.monotone_sort (α := OrderDual ℕ) (fun i => A n i)
  have hp : ∀ n, ∃ e : Equiv.Perm (Fin d), ∀ i, s n i = A n (e i) := by
    intro n
    exact ⟨e n, fun i => rfl⟩
  have hss (n : ℕ) := LeanFlow.pb021_sorted_increment_identity
    (A n) (A (n + 1)) (s n) (s (n + 1)) (x n) (x (n + 1))
    (hstep n) (hrank n) (hp n) (hs n) (hp (n + 1)) (hs (n + 1))
  let b (i : Fin d) : ℤ := (A 0 i : ℤ) + (if i = x 0 then 1 else 0) - (s 0 i : ℤ)
  refine ⟨s, b, hs, hp, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => intro i; rfl
    | succ n ih =>
      intro i
      have ha := hstep n i
      have hb := hss n i
      have hi := ih i
      push_cast [ha, hb]
      split_ifs at * <;> omega
  · intro K hK
    have hdom := (LeanFlow.pb021_sorted_prefix_dominance (A 0) (s 0) (hp 0) (hs 0) K hK).1
    have hdomz : ((Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => (A 0 i : ℤ))) ≤
        (Finset.univ.filter (fun i : Fin d => i.val < K)).sum (fun i => (s 0 i : ℤ)) := by
      exact_mod_cast hdom
    simp only [b, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hind : (Finset.univ.filter (fun i : Fin d => i.val < K)).sum
        (fun i => if i = x 0 then (1 : ℤ) else 0) ≤ 1 := by
      simp only [Finset.sum_ite_eq']
      split_ifs <;> norm_num
    linarith
  · have hsum : (Finset.univ.sum (fun i => (s 0 i : ℤ))) =
        Finset.univ.sum (fun i => (A 0 i : ℤ)) := by
      exact Equiv.sum_comp (e 0) (fun i => (A 0 i : ℤ))
    simp only [b, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hsum]
    simp
