import LeanFlowProofs.PBAdvanced021.SortedIncrementIdentity
import LeanFlowProofs.PBAdvanced021.SortedPrefixDominance
import Mathlib

theorem LeanFlow.pb021_rank_walk_bounded_width_of_defect {d : ℕ} (hd : 0 < d) (A : ℕ → Fin d → ℕ) (x : ℕ → Fin d) (s : ℕ → Fin d → ℕ) (b : Fin d → ℤ) (hstep : ∀ (n : ℕ) (i : Fin d), A (n + 1) i = A n i + (if i = x n then 1 else 0)) (hrank : ∀ n : ℕ, (x (n + 1)).val + 1 = (Finset.univ.filter (fun j : Fin d => A (n + 1) (x n) ≤ A (n + 1) j)).card) (hs : ∀ n : ℕ, Antitone (s n)) (hperm : ∀ n : ℕ, ∃ e : Equiv.Perm (Fin d), ∀ i : Fin d, s n i = A n (e i)) (hdefect : ∀ (n : ℕ) (i : Fin d), (A n i : ℤ) + (if i = x n then (1 : ℤ) else 0) - (s n i : ℤ) = b i) (hprefix : ∀ K : ℕ, 0 < K → K < d → (Finset.univ.filter (fun i : Fin d => i.val < K)).sum b ≤ 0) : ∃ W : ℕ, ∀ (n : ℕ) (i j : Fin d), A n i ≤ A n j + W := by 
  classical
  let C := (Finset.univ.sum fun i => (b i).natAbs) + 1
  have hb (i : Fin d) : -(C : ℤ) + 1 ≤ b i ∧ b i ≤ C := by
    have hh : (b i).natAbs ≤ Finset.univ.sum (fun j => (b j).natAbs) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((b j).natAbs)) (Finset.mem_univ i)
    have h1 : b i ≤ ((b i).natAbs : ℤ) := Int.le_natAbs
    have h2 : -(b i) ≤ ((b i).natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -(b i)))
    dsimp [C]
    omega
  have hclose (n : ℕ) (i : Fin d) : A n i ≤ s n i + C ∧ s n i ≤ A n i + C := by
    have := hdefect n i
    have := hb i
    split_ifs at * <;> omega
  have hout (n K : ℕ) (hK0 : 0 < K) (hKd : K < d)
      (hsep : ∀ i j : Fin d, i.val < K → K ≤ j.val → A n j ≤ A n i) :
      K ≤ (x n).val := by
    have heq := (pb021_sorted_prefix_dominance (A n) (s n) (hperm n) (hs n) K (by omega)).2.mpr hsep
    let S := Finset.univ.filter (fun i : Fin d => i.val < K)
    have hz : S.sum (fun i => (A n i : ℤ)) = S.sum (fun i => (s n i : ℤ)) := by
      exact_mod_cast heq
    have hh := Finset.sum_congr (s₁ := S) (s₂ := S) rfl (fun i _ => hdefect n i)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hz] at hh
    have hp := hprefix K hK0 hKd
    simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and] at hh
    dsimp [S] at hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    split_ifs at hh <;> omega
  have hinc (n : ℕ) := pb021_sorted_increment_identity (A n) (A (n+1))
    (s n) (s (n+1)) (x n) (x (n+1)) (hstep n) (hrank n)
    (hperm n) (hs n) (hperm (n+1)) (hs (n+1))
  have hlarge (n : ℕ) (p q : Fin d) (hpq : q.val = p.val + 1)
      (hg : s n q + 2*C + 1 < s n p) : s (n+1) p ≤ s n p := by
    have hsep (i j : Fin d) (hi : i.val < q.val) (hj : q.val ≤ j.val) :
        A n j + 1 ≤ A n i := by
      have hsi := hs n (show i ≤ p from by change i.val ≤ p.val; omega)
      have hsj := hs n (show q ≤ j from hj)
      have hci := hclose n i
      have hcj := hclose n j
      omega
    have hx := hout n q.val (by omega) q.isLt (fun i j hi hj => by have := hsep i j hi hj; omega)
    have hx' := hout (n+1) q.val (by omega) q.isLt (by
      intro i j hi hj
      have hi' : i ≠ x n := by intro he; subst i; omega
      have hh := hsep i j hi hj
      rw [hstep, hstep, if_neg hi']
      split_ifs <;> omega)
    have hp' : p ≠ x (n+1) := by intro he; subst p; omega
    rw [hinc n p, if_neg hp']
    omega
  let D := 2*C + 2 + Finset.univ.sum (s 0)
  have hgap (n : ℕ) : ∀ p q : Fin d, q.val = p.val + 1 → s n p ≤ s n q + D := by
    induction n with
    | zero =>
      intro p q hpq
      have hh : s 0 p ≤ Finset.univ.sum (s 0) :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ p)
      dsimp [D]
      omega
    | succ n ih =>
      intro p q hpq
      have hh := ih p q hpq
      have hq := hinc n q
      have hp := hinc n p
      by_cases hg : s n q + 2*C + 1 < s n p
      · have hl := hlarge n p q hpq hg
        split_ifs at hq <;> omega
      · dsimp [D] at *
        split_ifs at hp hq <;> omega
  have hchain (n k : ℕ) (hk : k < d) :
      s n ⟨0, hd⟩ ≤ s n ⟨k, hk⟩ + k * D := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k < d := by omega
      have hh := ih hk'
      have hg := hgap n ⟨k, hk'⟩ ⟨k+1, hk⟩ rfl
      simp only [Nat.succ_mul]
      omega
  refine ⟨d*D, ?_⟩
  intro n i j
  obtain ⟨e, he⟩ := hperm n
  have hi := he (e.symm i)
  have hj := he (e.symm j)
  simp only [Equiv.apply_symm_apply] at hi hj
  have ht := hs n (show (⟨0, hd⟩ : Fin d) ≤ e.symm i from Nat.zero_le _)
  have hc := hchain n (e.symm j).val (e.symm j).isLt
  have hm : (e.symm j).val * D ≤ d*D := Nat.mul_le_mul_right D (Nat.le_of_lt (e.symm j).isLt)
  change s n ⟨0, hd⟩ ≤ s n (e.symm j) + (e.symm j).val * D at hc
  omega

