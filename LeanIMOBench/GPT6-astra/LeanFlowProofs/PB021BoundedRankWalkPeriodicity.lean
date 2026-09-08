import Mathlib

theorem LeanFlow.pb021_bounded_rank_walk_eventually_periodic {d : ℕ} (hd : 0 < d) (A : ℕ → Fin d → ℕ) (x : ℕ → Fin d) (hstep : ∀ (n : ℕ) (i : Fin d), A (n + 1) i = A n i + (if i = x n then 1 else 0)) (hrank : ∀ n : ℕ, (x (n + 1)).val + 1 = (Finset.univ.filter (fun j : Fin d => A (n + 1) (x n) ≤ A (n + 1) j)).card) (hwidth : ∃ W : ℕ, ∀ (n : ℕ) (i j : Fin d), A n i ≤ A n j + W) : ∃ M P : ℕ, 0 < M ∧ 0 < P ∧ ∀ n : ℕ, M ≤ n → x n = x (n + P) := by 
  classical
  obtain ⟨W, hw⟩ := hwidth
  let z : Fin d := ⟨0, hd⟩
  let v (n : ℕ) (i : Fin d) : Fin (2 * W + 1) :=
    ⟨A n i + W - A n z, by
      have h := hw n i z
      omega⟩
  let state (n : ℕ) := (x n, v n)
  have decode {m n : ℕ} (h : state m = state n) :
      x m = x n ∧ ∀ i, A m i + A n z = A n i + A m z := by
    refine ⟨congrArg Prod.fst h, ?_⟩
    intro i
    have hv := congrArg (fun s : Fin d × (Fin d → Fin (2 * W + 1)) => (s.2 i).val) h
    change A m i + W - A m z = A n i + W - A n z at hv
    have hm := hw m z i
    have hn := hw n z i
    omega
  have advance {m n : ℕ} (h : state m = state n) : state (m + 1) = state (n + 1) := by
    obtain ⟨hx, hv⟩ := decode h
    have hv' (i : Fin d) :
        A (m + 1) i + A (n + 1) z = A (n + 1) i + A (m + 1) z := by
      simp only [hstep, hx]
      have hh := hv i
      omega
    have hcmp (j : Fin d) :
        A (m + 1) (x m) ≤ A (m + 1) j ↔ A (n + 1) (x n) ≤ A (n + 1) j := by
      have hi := hv' (x n)
      have hj := hv' j
      rw [hx]
      omega
    have hx' : x (m + 1) = x (n + 1) := by
      apply Fin.ext
      have hm := hrank m
      have hn := hrank n
      have hf : (Finset.univ.filter (fun j : Fin d => A (m + 1) (x m) ≤ A (m + 1) j)) =
          (Finset.univ.filter (fun j : Fin d => A (n + 1) (x n) ≤ A (n + 1) j)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcmp]
      rw [hf] at hm
      omega
    apply Prod.ext hx'
    funext i
    apply Fin.ext
    change A (m + 1) i + W - A (m + 1) z = A (n + 1) i + W - A (n + 1) z
    have hh := hv' i
    omega
  obtain ⟨a, b, hab, heq⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := state) (t := Set.univ) (fun _ => Set.mem_univ _) (Set.finite_univ)
  have htail : ∀ k, state (a + k) = state (b + k) := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih => simpa [Nat.add_assoc] using advance ih
  refine ⟨a + 1, b - a, by omega, by omega, ?_⟩
  intro n hn
  have hh := congrArg Prod.fst (htail (n - a))
  change x (a + (n - a)) = x (b + (n - a)) at hh
  convert hh using 1 <;> congr 1 <;> omega
