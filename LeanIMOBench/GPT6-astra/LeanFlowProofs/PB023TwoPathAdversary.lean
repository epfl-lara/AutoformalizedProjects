import LeanFlowProofs.PB023GridCrossing
import LeanFlowProofs.PB023SelectionExtension
import Mathlib

theorem LeanFlow.PB023.twoPathAdversary (C : ℕ) (hC : 3 ≤ C) :
    let onBoard : ℕ × ℕ → Prop := fun x =>
      0 < x.1 ∧ x.1 ≤ C + 1 ∧ 0 < x.2 ∧ x.2 ≤ C;
    let valid : List (ℕ × ℕ) → Prop := fun P =>
      P.head? = some (1, 1) ∧
      (∃ x : ℕ × ℕ, (x.1 = C + 1 ∧ onBoard x) ∧ P.getLast? = some x) ∧
      (∀ x : ℕ × ℕ, x ∈ P → onBoard x) ∧
      P.Chain' (fun a b => onBoard b ∧
        abs ((a.1 : ℤ) - (b.1 : ℤ)) + abs ((a.2 : ℤ) - (b.2 : ℤ)) = 1);
    let legal : Set (ℕ × ℕ) → Prop := fun S =>
      (∀ r c : ℕ, (r, c) ∈ S →
        (2 ≤ r ∧ r ≤ C) ∧ (1 ≤ c ∧ c ≤ C)) ∧
      (∀ r : ℕ, (2 ≤ r ∧ r ≤ C) → ∃! c : ℕ, (r, c) ∈ S) ∧
      (∀ r₁ c₁ r₂ c₂ : ℕ,
        (r₁, c₁) ∈ S → (r₂, c₂) ∈ S → c₁ = c₂ → r₁ = r₂);
    let first : (P : List (ℕ × ℕ)) → Set (ℕ × ℕ) → Fin P.length → Prop :=
      fun P S i => P.get i ∈ S ∧
        ∀ j : Fin P.length, j.val < i.val → P.get j ∉ S;
    ∀ P : List (ℕ × ℕ), valid P →
      ∃ i : Fin P.length,
        ∀ Q : List (ℕ × ℕ), valid Q →
          ∃ S : Set (ℕ × ℕ),
            legal S ∧ first P S i ∧
            ∃ j : Fin Q.length, Q.get j ∈ S := by classical
  intro onBoard valid legal first P hP
  obtain ⟨i, p, hpi, hi, hp, hearly⟩ :=
    gridCrossing C hC P hP 2 (by omega) (by omega)
  let c := (P.get i).2
  have hic : P.get i = (2, c) := Prod.ext hi rfl
  have hc := hP.2.2.1 (P.get i) (List.get_mem P i)
  have hc1 : 1 ≤ c := hc.2.2.1
  have hcC : c ≤ C := hc.2.2.2
  have hfirst : ∀ S, legal S → (2, c) ∈ S → first P S i := by
    intro S hS hm
    refine ⟨hic ▸ hm, ?_⟩
    intro k hk hmem
    have hrow := (hS.1 (P.get k).1 (P.get k).2 hmem).1.1
    have := hearly k hk
    omega
  refine ⟨i, ?_⟩
  intro Q hQ
  by_cases hit : ∃ j : Fin Q.length, Q.get j = (2, c)
  · obtain ⟨j, hj⟩ := hit
    have hd : ∃ d : ℕ, 1 ≤ d ∧ d ≤ C ∧ c ≠ d := by
      by_cases h : c = 1
      · exact ⟨2, by omega, by omega, by omega⟩
      · exact ⟨1, by omega, by omega, h⟩
    obtain ⟨d, hd1, hdC, hcd⟩ := hd
    obtain ⟨S, hS, hSc, hSd⟩ := selectionExtension C hC c d hc1 hcC hd1 hdC hcd
    exact ⟨S, hS, hfirst S hS hSc, j, hj ▸ hSc⟩
  · obtain ⟨j, k, hkj, hj, hk, hbefore⟩ :=
      gridCrossing C hC Q hQ 3 (by omega) (by omega)
    let d := (Q.get j).2
    have hd := hQ.2.2.1 (Q.get j) (List.get_mem Q j)
    have hd1 : 1 ≤ d := hd.2.2.1
    have hdC : d ≤ C := hd.2.2.2
    have hcd : c ≠ d := by
      intro heq
      apply hit
      refine ⟨k, ?_⟩
      simpa [d, heq] using hk
    obtain ⟨S, hS, hSc, hSd⟩ := selectionExtension C hC c d hc1 hcC hd1 hdC hcd
    refine ⟨S, hS, hfirst S hS hSc, j, ?_⟩
    have hjd : Q.get j = (3, d) := Prod.ext hj rfl
    exact hjd ▸ hSd
