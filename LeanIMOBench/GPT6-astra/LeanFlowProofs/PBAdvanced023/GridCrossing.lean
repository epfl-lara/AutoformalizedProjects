import Mathlib

theorem LeanFlow.PB023.gridCrossing (C : ℕ) (hC : 3 ≤ C) :
    let onBoard : ℕ × ℕ → Prop := fun x =>
      0 < x.1 ∧ x.1 ≤ C + 1 ∧ 0 < x.2 ∧ x.2 ≤ C;
    let valid : List (ℕ × ℕ) → Prop := fun P =>
      P.head? = some (1, 1) ∧
      (∃ x : ℕ × ℕ, (x.1 = C + 1 ∧ onBoard x) ∧ P.getLast? = some x) ∧
      (∀ x : ℕ × ℕ, x ∈ P → onBoard x) ∧
      P.Chain' (fun a b => onBoard b ∧
        abs ((a.1 : ℤ) - (b.1 : ℤ)) + abs ((a.2 : ℤ) - (b.2 : ℤ)) = 1);
    ∀ P : List (ℕ × ℕ), valid P →
      ∀ t : ℕ, 2 ≤ t → t ≤ C + 1 →
        ∃ i j : Fin P.length,
          j.val + 1 = i.val ∧
          (P.get i).1 = t ∧
          P.get j = (t - 1, (P.get i).2) ∧
          ∀ k : Fin P.length, k.val < i.val → (P.get k).1 < t := by 
  classical
  dsimp only
  intro P hv t ht htC
  rcases hv with ⟨hh, ⟨x, hx, hl⟩, hb, hc⟩
  have xm : x ∈ P := by
    have := List.mem_of_mem_getLast? hl
    exact this
  obtain ⟨q, hq⟩ := List.get_of_mem xm
  have ex : ∃ n : ℕ, ∃ hn : n < P.length, t ≤ (P.get ⟨n, hn⟩).1 := by
    refine ⟨q.val, q.isLt, ?_⟩
    change t ≤ (P.get q).1
    rw [hq, hx.1]
    exact htC
  let n := Nat.find ex
  obtain ⟨hn, hr⟩ := Nat.find_spec ex
  have earlier : ∀ k : Fin P.length, k.val < n → (P.get k).1 < t := by
    intro k hk
    have hm := Nat.find_min ex hk
    exact lt_of_not_ge (fun h => hm ⟨k.isLt, h⟩)
  have hn0 : n ≠ 0 := by
    intro he
    have hhead : P.get ⟨n, hn⟩ = (1, 1) := by
      have hh' := hh
      rw [List.head?_eq_getElem?] at hh'
      have hz : 0 < P.length := by omega
      rw [List.getElem?_eq_getElem hz] at hh'
      have heq := Option.some.inj hh'
      simpa only [List.get_eq_getElem, he] using heq
    rw [hhead] at hr
    omega
  let i : Fin P.length := ⟨n, hn⟩
  let j : Fin P.length := ⟨n - 1, by omega⟩
  have hj : j.val + 1 = i.val := by dsimp [i, j]; omega
  have hjr := earlier j (by dsimp [j]; omega)
  have adj := (List.isChain_iff_getElem.mp hc) (n - 1) (by omega)
  have step : abs ((P.get j).1 - ((P.get i).1 : ℤ)) +
      abs ((P.get j).2 - ((P.get i).2 : ℤ)) = 1 := by
    simpa [i, j, List.get_eq_getElem, show n - 1 + 1 = n by omega] using adj.2
  have row : (P.get i).1 = t := by
    have h := le_abs_self (((P.get j).1 : ℤ) - (P.get i).1)
    have h' := neg_le_abs (((P.get j).1 : ℤ) - (P.get i).1)
    have h'' := abs_nonneg (((P.get j).2 : ℤ) - (P.get i).2)
    change t ≤ (P.get i).1 at hr
    omega
  have prev : P.get j = (t - 1, (P.get i).2) := by
    have h := neg_le_abs (((P.get j).1 : ℤ) - (P.get i).1)
    have h' := le_abs_self (((P.get j).2 : ℤ) - (P.get i).2)
    have h'' := neg_le_abs (((P.get j).2 : ℤ) - (P.get i).2)
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  exact ⟨i, j, hj, row, prev, earlier⟩
