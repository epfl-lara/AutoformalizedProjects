import LeanFlowProofs.PB021BoundedRankWalkPeriodicity
import LeanFlowProofs.PB021RankWalkBoundedWidth
import LeanFlowProofs.PB021RankWalkDefectData
import LeanFlowProofs.PB021SortedPrefixDominance
import Mathlib

theorem LeanFlow.pb021_rank_walk_eventually_periodic {d : ℕ} (hd : 0 < d) (A : ℕ → Fin d → ℕ) (x : ℕ → Fin d) (hstep : ∀ (n : ℕ) (i : Fin d), A (n + 1) i = A n i + (if i = x n then 1 else 0)) (hrank : ∀ n : ℕ, (x (n + 1)).val + 1 = (Finset.univ.filter (fun j : Fin d => A (n + 1) (x n) ≤ A (n + 1) j)).card) : ∃ M P : ℕ, 0 < M ∧ 0 < P ∧ ∀ n : ℕ, M ≤ n → x n = x (n + P) := by 
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨s, b, hs, hp, hb, hpre, htotal⟩ :=
      pb021_rank_walk_defect_data A x hstep hrank
    by_cases hex : ∃ K, 0 < K ∧ K < d ∧
        (Finset.univ.filter (fun i : Fin d => i.val < K)).sum b = 1
    · obtain ⟨K, hK0, hKd, hK⟩ := hex
      let S := Finset.univ.filter (fun i : Fin d => i.val < K)
      have hclosed (n : ℕ) : (x n).val < K ∧
          ∀ i j : Fin d, i.val < K → K ≤ j.val → A n j ≤ A n i := by
        have hdom := pb021_sorted_prefix_dominance (A n) (s n) (hp n) (hs n) K (by omega)
        have he : (∑ i ∈ S, (A n i : ℤ)) +
            (if (x n).val < K then (1 : ℤ) else 0) -
            (∑ i ∈ S, (s n i : ℤ)) = 1 := by
          have hh := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun i _ => hb n i)
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hh
          simpa [S, Finset.sum_ite_eq', hK] using hh
        have hle : (∑ i ∈ S, (A n i : ℤ)) ≤ ∑ i ∈ S, (s n i : ℤ) := by
          exact_mod_cast hdom.1
        have hx : (x n).val < K := by
          split_ifs at he <;> omega
        refine ⟨hx, hdom.2.mp ?_⟩
        have heq : (∑ i ∈ S, (A n i : ℤ)) = ∑ i ∈ S, (s n i : ℤ) := by
          simp only [if_pos hx] at he
          omega
        exact_mod_cast heq
      let emb : Fin K → Fin d := fun i => ⟨i.val, lt_trans i.isLt hKd⟩
      let y : ℕ → Fin K := fun n => ⟨(x n).val, (hclosed n).1⟩
      let B : ℕ → Fin K → ℕ := fun n i => A n (emb i)
      have hey (n : ℕ) : emb (y n) = x n := by apply Fin.ext; rfl
      have hinj : Function.Injective emb := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun z : Fin d => z.val) hij
      have hB (n : ℕ) (i : Fin K) :
          B (n + 1) i = B n i + (if i = y n then 1 else 0) := by
        dsimp [B]
        rw [hstep, ← hey n]
        simp only [hinj.eq_iff]
      have hy (n : ℕ) : (y (n + 1)).val + 1 =
          (Finset.univ.filter (fun j : Fin K => B (n + 1) (y n) ≤ B (n + 1) j)).card := by
        change (x (n + 1)).val + 1 = _
        rw [hrank]
        symm
        apply Finset.card_bij (fun i _ => emb i)
        · intro i hi
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, B, hey] using hi
        · intro i hi j hj hij
          exact hinj hij
        · intro j hj
          have hj' : A (n + 1) (x n) ≤ A (n + 1) j := by simpa using hj
          have hjK : j.val < K := by
            by_contra hh
            have hsep := (hclosed n).2 (x n) j (hclosed n).1 (by omega)
            have hne : j ≠ x n := by
              intro heq
              subst j
              exact hh (hclosed n).1
            rw [hstep, hstep, if_pos rfl, if_neg hne] at hj'
            omega
          let i : Fin K := ⟨j.val, hjK⟩
          have hei : emb i = j := by apply Fin.ext; rfl
          refine ⟨i, ?_, hei⟩
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, B, hey, hei] using hj'
      obtain ⟨M, P, hM, hP, hper⟩ := ih K hKd hK0 B y hB hy
      refine ⟨M, P, hM, hP, ?_⟩
      intro n hn
      simpa only [hey] using congrArg emb (hper n hn)
    · apply pb021_bounded_rank_walk_eventually_periodic hd A x hstep hrank
      apply pb021_rank_walk_bounded_width_of_defect hd A x s b hstep hrank hs hp hb
      intro K hK0 hKd
      have hle := hpre K (by omega)
      have hne : (Finset.univ.filter (fun i : Fin d => i.val < K)).sum b ≠ 1 := by
        intro he
        exact hex ⟨K, hK0, hKd, he⟩
      omega

