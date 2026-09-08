import LeanFlowProofs.PBAdvanced018.Countercoloring
import LeanFlowProofs.PBAdvanced018.NoMonoPath
import Mathlib

/-
For given integers $n \ge 5$ and $k \ge 1$, we color each of the $n^2$ cells of an $n \times n$ grid  using one of $k$ colors. If $q$ is the largest integer which is not larger than $\frac{n^2}{k}$, then, each of the $k$ colors must be used to color exactly $q$ or $q+1$ cells. A sequence of $n$ different cells $c_1, c_2, \ldots, c_n$ in the grid is called a \textit{snake} if it satisfies the following conditions simultaneously:

\begin{enumerate}
\item[(a)] For each $1 \le i \le n-1$, two cells $c_i$ and $c_{i+1}$ are adjacent to their sides,
\item[(b)] For each $1 \le i \le n-1$, cell $c_i$ and cell $c_{i+1}$ are colored with different colors.
\end{enumerate}
Let $a(n)$ be the minimum $k$ such that a snake exists regardless of the method of coloring. Find a constant $L$ that satisfies the following inequality and prove it:

\[
|La(n)- n^2 | \le n +2 \sqrt n + 3 \;.
\]

Answer: 3
-/

-- The set of valid coloring: each of the $k$ colors must be used to color exactly $q$ or $q+1$ cells
def validColorings (n k : ℕ) : Set (Matrix (Fin n) (Fin n) (Fin k)) :=
  let q : ℕ := ⌊ n^2 / k ⌋₊
  { M |
    ∀ c : Fin k, let cn := Finset.card {coor : Fin n × Fin n | M.uncurry coor = c}
    cn = q ∨ cn = q+1
  }

-- Definition of a snake on a fixed grid
structure Snake {n k : ℕ} (M : Matrix (Fin n) (Fin n) (Fin k)) where
  c : List (Fin n × Fin n)
  c_nodup : c.Nodup -- the cells must be different
  c_len : c.length = n
  c_adj : c.Chain' (fun (y₁,x₁) (y₂,x₂) ↦
    abs (x₁ - x₂ : ℤ) + abs (y₁ - y₂ : ℤ) = 1 ∧ -- the cells are adjacent
    M y₁ x₁ ≠ M y₂ x₂ -- and they have a different color
  )

-- Let $a(n)$ be the minimum $k$ such that a snake exists regardless of the method of coloring.
-- We are given k ≥ 1 among the main assumptions, so we will force k ≥ 1 here.
noncomputable
def a (n : ℕ) := sInf { k : ℕ | k ≥ 1 ∧ ∀ M ∈ validColorings n k, Nonempty (Snake M) }

theorem PBAdvanced018 (n : ℕ) (hn : n ≥ 5) : |(3 * a n - n^2 : ℤ)| ≤ n + 2 * √ n + 3 := by classical
  have bridge (k : ℕ) (M : Fin n → Fin n → Fin k) : M ∈ validColorings n k ↔ ∀ i : Fin k, (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k ∨ (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card = n ^ 2 / k + 1 := by
    simp [validColorings, Function.uncurry]
    rfl
  let K := n ^ 2 / 3 + 1
  have hK : K ≥ 1 ∧ ∀ M ∈ validColorings n K, Nonempty (Snake M) := by
    refine ⟨by omega, ?_⟩
    intro M hM
    have hcard (i : Fin K) : (Finset.univ.filter (fun x : Fin n × Fin n => M x.1 x.2 = i)).card ≤ 3 := by
      have hq : n ^ 2 / K < 3 := (Nat.div_lt_iff_lt_mul (by dsimp [K]; omega)).2 (by dsimp [K]; omega)
      have := (bridge K M).1 hM i
      omega
    have hmono : ∀ y₀ y₁ x₀ x₁ : Fin n, y₁.val = y₀.val + 1 → x₁.val = x₀.val + 1 → ¬ (M y₀ x₀ = M y₀ x₁ ∧ M y₀ x₀ = M y₁ x₀ ∧ M y₀ x₀ = M y₁ x₁) := by
      intro y₀ y₁ x₀ x₁ hy hx he
      have hyne : y₀ ≠ y₁ := by intro h; subst y₁; omega
      have hxne : x₀ ≠ x₁ := by intro h; subst x₁; omega
      have hsub : ({(y₀,x₀), (y₀,x₁), (y₁,x₀), (y₁,x₁)} : Finset (Fin n × Fin n)) ⊆ Finset.univ.filter (fun x => M x.1 x.2 = M y₀ x₀) := by
        intro x hx'
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with rfl | rfl | rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> first | rfl | exact he.1.symm | exact he.2.1.symm | exact he.2.2.symm
      have hfour : ({(y₀,x₀), (y₀,x₁), (y₁,x₀), (y₁,x₁)} : Finset (Fin n × Fin n)).card = 4 := by
        simp [hyne, hxne, Ne.symm hyne, Ne.symm hxne]
      have := Finset.card_le_card hsub
      have := hcard (M y₀ x₀)
      omega
    obtain ⟨c, hc, hl, ha⟩ := LeanFlowProofs.PB018.no_mono_path n K (by omega) M hmono
    exact ⟨⟨c, hc, hl, ha⟩⟩
  have hne : {k : ℕ | k ≥ 1 ∧ ∀ M ∈ validColorings n k, Nonempty (Snake M)}.Nonempty := ⟨K, hK⟩
  have ha : a n ≥ 1 ∧ ∀ M ∈ validColorings n (a n), Nonempty (Snake M) := Nat.sInf_mem hne
  have hau : a n ≤ K := Nat.sInf_le hK
  have upper : 3 * a n ≤ n ^ 2 + 3 := by dsimp [K] at hau; omega
  have lower : n ^ 2 ≤ 3 * a n + n + 2 * Nat.sqrt n + 3 := by
    by_contra h
    obtain ⟨M, hM, hpath⟩ := LeanFlowProofs.PB018.countercoloring n (a n) hn ha.1 (by omega)
    obtain ⟨s⟩ := ha.2 M ((bridge (a n) M).2 hM)
    have := hpath s.c s.c_nodup s.c_adj
    have := s.c_len
    omega
  have hi : |(3 * a n - n^2 : ℤ)| ≤ (n + 2 * Nat.sqrt n + 3 : ℕ) := by
    have hu : 3 * (a n : ℤ) ≤ (n : ℤ)^2 + 3 := by exact_mod_cast upper
    have hl : (n : ℤ)^2 ≤ 3 * (a n : ℤ) + n + 2 * Nat.sqrt n + 3 := by exact_mod_cast lower
    rw [abs_le]
    push_cast
    constructor <;> linarith
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' n
  have hir := (Int.cast_le (R := ℝ)).2 hi
  push_cast at hir
  simpa only [Int.cast_abs, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_natCast] using (le_trans hir (by linarith : (n : ℝ) + 2 * Nat.sqrt n + 3 ≤ n + 2 * Real.sqrt n + 3))
