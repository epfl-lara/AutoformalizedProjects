import Mathlib

theorem LeanFlow.pb021_sorted_increment_identity {d : ℕ} (v w s t : Fin d → ℕ) (x r : Fin d) (hstep : ∀ i : Fin d, w i = v i + (if i = x then 1 else 0)) (hrank : r.val + 1 = (Finset.univ.filter (fun j : Fin d => w x ≤ w j)).card) (hsperm : ∃ e : Equiv.Perm (Fin d), ∀ i : Fin d, s i = v (e i)) (hs : Antitone s) (htperm : ∃ e : Equiv.Perm (Fin d), ∀ i : Fin d, t i = w (e i)) (ht : Antitone t) : ∀ i : Fin d, t i = s i + (if i = r then 1 else 0) := by classical
  let C (f : Fin d → ℕ) (k : ℕ) := (Finset.univ.filter (fun j => k ≤ f j)).card
  have char (f : Fin d → ℕ) (hf : Antitone f) (k : ℕ) (i : Fin d) : k ≤ f i ↔ i.val < C f k := by
    constructor
    · intro hi
      have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => k ≤ f j) := by
        intro j hj
        simp only [Finset.mem_Iic] at hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi.trans (hf hj)
      have h := Finset.card_le_card hsub
      rw [Fin.card_Iic] at h
      exact Nat.lt_of_succ_le h
    · intro hi
      by_contra hh
      have hsub : Finset.univ.filter (fun j => k ≤ f j) ⊆ Finset.Iio i := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_Iio]
        by_contra hn
        have := hf (le_of_not_gt hn)
        omega
      have h := Finset.card_le_card hsub
      rw [Fin.card_Iio] at h
      exact (Nat.not_lt_of_ge h) hi
  have permcount (f g : Fin d → ℕ) (hp : ∃ e : Equiv.Perm (Fin d), ∀ i, f i = g (e i)) (k : ℕ) : C f k = C g k := by
    obtain ⟨e, he⟩ := hp
    apply Finset.card_bij (fun i _ => e i)
    · intro i hi
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, he] using hi
    · intro i hi j hj hij
      exact e.injective hij
    · intro j hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, he, e.apply_symm_apply] using hj
  have hx : w x = v x + 1 := by simpa using hstep x
  have same (k : ℕ) (hk : k ≠ w x) : C w k = C v k := by
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hj := hstep j
    by_cases hjx : j = x
    · subst j
      omega
    · simp only [hjx, if_false, Nat.add_zero] at hj
      rw [hj]
  have jump : C w (w x) = C v (w x) + 1 := by
    have he : Finset.univ.filter (fun j => w x ≤ w j) = insert x (Finset.univ.filter (fun j => w x ≤ v j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hjx : j = x
      · subst j
        simp
      · have hj := hstep j
        simp only [hjx, if_false, Nat.add_zero] at hj
        simp [hjx, hj]
    dsimp [C]
    rw [he, Finset.card_insert_of_notMem]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have rankv : C v (w x) = r.val := by change r.val + 1 = C w (w x) at hrank; omega
  have ranks : C s (w x) = r.val := (permcount s v hsperm _).trans rankv
  have rankt : C t (w x) = r.val + 1 := (permcount t w htperm _).trans hrank.symm
  have other (k : ℕ) (hk : k ≠ w x) (i : Fin d) : k ≤ t i ↔ k ≤ s i := by
    rw [char t ht, char s hs, permcount t w htperm, permcount s v hsperm, same k hk]
  intro i
  by_cases hir : i = r
  · subst i
    have hst : s r < w x := by
      have := char s hs (w x) r
      rw [ranks] at this
      omega
    have htt : w x ≤ t r := by
      apply (char t ht (w x) r).mpr
      rw [rankt]
      omega
    have hslo : v x ≤ s r := by
      apply (other (v x) (by omega) r).mp
      omega
    have hthi : t r < w x + 1 := by
      have := other (w x + 1) (by omega) r
      omega
    simp only [ite_true]
    omega
  · have hidx : i.val ≠ r.val := fun h => hir (Fin.ext h)
    have hall (k : ℕ) : k ≤ t i ↔ k ≤ s i := by
      by_cases hk : k = w x
      · subst k
        rw [char t ht, char s hs, ranks, rankt]
        omega
      · exact other k hk i
    have h1 := (hall (t i)).mp (le_refl _)
    have h2 := (hall (s i)).mpr (le_refl _)
    simp only [hir, if_false, Nat.add_zero]
    omega
