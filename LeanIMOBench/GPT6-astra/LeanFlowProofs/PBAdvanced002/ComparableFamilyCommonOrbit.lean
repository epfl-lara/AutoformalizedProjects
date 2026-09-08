import Mathlib

theorem LeanFlowPB002.comparable_family_common_orbit
    {I X : Type*} [Fintype I] [Nonempty I] (g : X → X) (A : I → X)
    (hcomp : ∀ i j : I, i ≠ j →
      (∃ k : ℕ, g^[k] (A i) = A j) ∨
      (∃ k : ℕ, g^[k] (A j) = A i)) :
    ∃ i₀ : I, ∀ i : I, ∃ k : ℕ, g^[k] (A i₀) = A i := by classical
  have hall (s : Finset I) : ∃ r : I, ∀ i ∈ s, ∃ k : ℕ, g^[k] (A r) = A i := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨Classical.choice inferInstance, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨r, hr⟩ := ih
      have hcmp : (∃ k : ℕ, g^[k] (A r) = A a) ∨
          (∃ k : ℕ, g^[k] (A a) = A r) := by
        by_cases h : r = a
        · exact Or.inl ⟨0, by simp [h]⟩
        · exact hcomp r a h
      rcases hcmp with hra | ⟨n, hnar⟩
      · refine ⟨r, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hra
        · exact hr i hi
      · refine ⟨a, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact ⟨0, rfl⟩
        · obtain ⟨k, hk⟩ := hr i hi
          exact ⟨k + n, by rw [Function.iterate_add_apply, hnar, hk]⟩
  obtain ⟨r, hr⟩ := hall Finset.univ
  exact ⟨r, fun i => hr i (Finset.mem_univ i)⟩
