import Mathlib

theorem LeanFlowPB002.long_iterate_visits_cycle {V : Type*} [Fintype V] (R : V → V → Prop) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  ∀ (ell : ℕ) (x y : V), Fintype.card V ≤ ell →
    y ∈ F^[ell] ({x} : Set V) →
    ∃ (v : V) (a b c : ℕ),
      a + b = ell ∧ 0 < c ∧
      v ∈ F^[a] ({x} : Set V) ∧
      y ∈ F^[b] ({v} : Set V) ∧
      v ∈ F^[c] ({v} : Set V) := by classical
  dsimp only
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  have paths : ∀ (n : ℕ) (x y : V), y ∈ F^[n] ({x} : Set V) →
      ∃ p : ℕ → V, p 0 = x ∧ p n = y ∧ ∀ i, i < n → R (p i) (p (i+1)) := by
    intro n
    induction n with
    | zero =>
      intro x y hy
      have he : y = x := by simpa using hy
      subst y
      exact ⟨fun _ => x, rfl, rfl, by omega⟩
    | succ n ih =>
      intro x y hy
      rw [Function.iterate_succ_apply'] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      obtain ⟨p, hp0, hpn, hp⟩ := ih x z hz
      refine ⟨fun i => if i ≤ n then p i else y, ?_, ?_, ?_⟩
      · simpa using hp0
      · simp
      · intro i hi
        by_cases h : i < n
        · simpa [show i ≤ n by omega, show i+1 ≤ n by omega] using hp i h
        · have he : i = n := by omega
          subst i
          simpa [hpn] using hzy
  intro ell x y hcard hy
  obtain ⟨p, hp0, hpell, hp⟩ := paths ell x y hy
  have segment : ∀ (d i : ℕ), i + d ≤ ell →
      p (i+d) ∈ F^[d] ({p i} : Set V) := by
    intro d
    induction d with
    | zero => intro i hi; simp
    | succ d ih =>
      intro i hi
      rw [Function.iterate_succ_apply']
      exact ⟨p (i+d), ih i (by omega), by simpa [Nat.add_assoc] using hp (i+d) (by omega)⟩
  have hninj : ¬ Function.Injective (fun i : Fin (ell+1) => p i.val) := by
    intro hinj
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hninj
  have ordered : ∃ a b : ℕ, a < b ∧ b ≤ ell ∧ p a = p b := by
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i.val, j.val, h, by omega, heq⟩
    · exact ⟨j.val, i.val, h, by omega, heq.symm⟩
  obtain ⟨a, j, haj, hj, heq⟩ := ordered
  refine ⟨p a, a, ell-a, j-a, by omega, by omega, ?_, ?_, ?_⟩
  · simpa [hp0] using segment a 0 (by omega)
  · simpa [Nat.add_sub_of_le (show a ≤ ell by omega), hpell] using segment (ell-a) a (by omega)
  · simpa [Nat.add_sub_of_le (show a ≤ j by omega), ← heq] using segment (j-a) a (by omega)
