import LeanFlowProofs.PBAdvanced002.ComparableFamilyCommonOrbit
import Mathlib

theorem LeanFlowPB002.eventual_period_configuration_bound
    {X : Type*} (g : X → X) (T P : ℕ) (hP : 0 < P)
    (hperiod : ∀ (x : X) (k : ℕ), T ≤ k → g^[k + P] x = g^[k] x)
    (t : ℕ) (A : Fin t → X) (hinj : Function.Injective A)
    (hcomp : ∀ i j : Fin t, i ≠ j →
      (∃ k : ℕ, g^[k] (A i) = A j) ∨
      (∃ k : ℕ, g^[k] (A j) = A i)) :
    t ≤ T + P := by classical
  by_cases ht : t = 0
  · subst t
    omega
  haveI : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i₀, horbit⟩ := LeanFlowPB002.comparable_family_common_orbit g A hcomp
  have hreduce : ∀ (k : ℕ), ∃ n : Fin (T + P),
      g^[n.val] (A i₀) = g^[k] (A i₀) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hk : k < T + P
      · exact ⟨⟨k, hk⟩, rfl⟩
      · obtain ⟨n, hn⟩ := ih (k - P) (by omega)
        refine ⟨n, hn.trans ?_⟩
        have hp := hperiod (A i₀) (k - P) (by omega)
        have heq : k - P + P = k := by omega
        rw [heq] at hp
        exact hp.symm
  have hex : ∀ i : Fin t, ∃ n : Fin (T + P), g^[n.val] (A i₀) = A i := by
    intro i
    obtain ⟨k, hk⟩ := horbit i
    obtain ⟨n, hn⟩ := hreduce k
    exact ⟨n, hn.trans hk⟩
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hinj
    rw [← hf i, ← hf j, hij]
  simpa using Fintype.card_le_of_injective f hf_inj
