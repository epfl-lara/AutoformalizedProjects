import Mathlib

theorem LeanFlowProofs.PB018.rectangle_atoms (n u v : ℕ) (hn : 1 ≤ n) (hu : 2 ≤ u) (hv : 2 ≤ v) : let h : ℕ := (n - 1) / u; let j : ℕ := (n - 1) / v; ∃ b : (Fin n × Fin n) → (Fin (n - h) × Fin (n - j)), let w : (Fin (n - h) × Fin (n - j)) → ℕ := fun a => (Finset.univ.filter (fun x : Fin n × Fin n => b x = a)).card; (∀ a, w a = 1 ∨ w a = 2 ∨ w a = 4) ∧ Finset.sum Finset.univ w = n ^ 2 ∧ (Finset.univ.filter (fun a : Fin (n - h) × Fin (n - j) => w a = 1)).card = (n - 2 * h) * (n - 2 * j) ∧ (Finset.univ.filter (fun a : Fin (n - h) × Fin (n - j) => w a = 4)).card = h * j ∧ (∀ r s : ℕ, (Finset.univ.filter (fun x : Fin n × Fin n => x.1.val / u = r ∧ x.2.val / v = s)).card ≤ u * v) ∧ (∀ x y : Fin n × Fin n, abs ((x.2 : ℤ) - (y.2 : ℤ)) + abs ((x.1 : ℤ) - (y.1 : ℤ)) = 1 → (x.1.val / u, x.2.val / v) ≠ (y.1.val / u, y.2.val / v) → b x = b y) := by classical
  have coord (n u : ℕ) (hn : 1 ≤ n) (hu : 2 ≤ u) :
      ∃ f : Fin n → Fin (n - (n-1)/u),
        (∀ i, (f i).val = i.val - i.val/u) ∧
        (∀ a, (Finset.univ.filter (fun i => f i = a)).card = 1 ∨ (Finset.univ.filter (fun i => f i = a)).card = 2) ∧
        (Finset.univ.filter (fun a => (Finset.univ.filter (fun i => f i = a)).card = 1)).card = n-2*((n-1)/u) ∧
        (Finset.univ.filter (fun a => (Finset.univ.filter (fun i => f i = a)).card = 2)).card = (n-1)/u := by
    have mono : Monotone (fun i : ℕ => i - i/u) := by
      apply monotone_nat_of_le_succ
      intro i
      have h₁ := Nat.div_le_self i u
      have h₂ := Nat.div_le_self (i+1) u
      have h₃ : (i+1)/u ≤ i/u+1 := by
        have hi := Nat.mod_add_div i u
        have hm := Nat.mod_lt i (show 0 < u by omega)
        apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        nlinarith
      omega
    have near (i j : ℕ) (h : i-i/u = j-j/u) : i ≤ j+1 := by
      have hi := Nat.div_le_self i u
      have hj := Nat.div_le_self j u
      have hi' := Nat.mod_add_div i u
      have hj' := Nat.mod_add_div j u
      have hmi := Nat.mod_lt i (show 0 < u by omega)
      have hmj := Nat.mod_lt j (show 0 < u by omega)
      by_contra hh
      have hd : j/u+2 ≤ i/u := by omega
      have he : i + j/u = j + i/u := by omega
      have hm : u * (j/u+2) + i/u ≤ u * (i/u) + (j/u+2) := by
        have hh := Nat.mul_le_mul_left (u-1) hd
        rw [Nat.sub_mul, Nat.sub_mul] at hh
        have h₁ := Nat.le_mul_of_pos_left (j/u+2) (show 0 < u by omega)
        have h₂ := Nat.le_mul_of_pos_left (i/u) (show 0 < u by omega)
        simp only [one_mul] at hh
        omega
      nlinarith only [hm, he, hi', hj', hmj, hu, Nat.zero_le (i % u)]
    have hit : ∀ t a : ℕ, a ≤ t-t/u → ∃ i, i ≤ t ∧ i-i/u = a := by
      intro t
      induction t with
      | zero => intro a ha; exact ⟨0, by omega, by simpa [eq_comm] using ha⟩
      | succ t ih =>
        intro a ha
        by_cases h : a ≤ t-t/u
        · obtain ⟨i, hi, he⟩ := ih a h
          exact ⟨i, by omega, he⟩
        · refine ⟨t+1, le_rfl, ?_⟩
          have := Nat.div_le_div_right (show t ≤ t+1 by omega) (c := u)
          have := Nat.div_le_self t u
          have := Nat.div_le_self (t+1) u
          omega
    have hend := Nat.div_le_self (n-1) u
    let f : Fin n → Fin (n - (n-1)/u) := fun i => ⟨i.val-i.val/u, by
      have hh := mono (show i.val ≤ n-1 by omega)
      dsimp only at hh
      omega⟩
    have surj : Function.Surjective f := by
      intro a
      obtain ⟨i, hi, he⟩ := hit (n-1) a.val (by omega)
      exact ⟨⟨i, by omega⟩, Fin.ext he⟩
    let w := fun a => (Finset.univ.filter (fun i => f i = a)).card
    have hw (a) : w a = 1 ∨ w a = 2 := by
      have hlo : 0 < w a := by
        obtain ⟨i, hi⟩ := surj a
        apply Finset.card_pos.mpr
        exact ⟨i, by simp [hi]⟩
      have hhi : w a ≤ 2 := by
        have hh : w a ≤ (Finset.range 2).card := by
          apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val % 2)
          · intro i hi
            exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
          · intro i hi j hj he
            have hi' : f i = a := (Finset.mem_filter.mp hi).2
            have hj' : f j = a := (Finset.mem_filter.mp hj).2
            have hh : i.val-i.val/u = j.val-j.val/u := congrArg Fin.val (hi'.trans hj'.symm)
            have h₁ := near i.val j.val hh
            have h₂ := near j.val i.val hh.symm
            apply Fin.ext
            change i.val % 2 = j.val % 2 at he
            omega
        simpa using hh
      omega
    have total : (∑ a, w a) = n := by
      simpa [w] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin (n-(n-1)/u))) f
    have counts : (Finset.univ.filter (fun a => w a = 1)).card + (Finset.univ.filter (fun a => w a = 2)).card = n-(n-1)/u := by
      have he : (Finset.univ.filter (fun a => w a = 2)) = (Finset.univ.filter (fun a => ¬ w a = 1)) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := hw a
        omega
      rw [he]
      simpa using (Finset.univ : Finset (Fin (n-(n-1)/u))).card_filter_add_card_filter_not (fun a => w a = 1)
    have weighted : (∑ a, w a) = (Finset.univ.filter (fun a => w a = 1)).card + 2 * (Finset.univ.filter (fun a => w a = 2)).card := by
      have he (a) : w a = (if w a = 1 then 1 else 0) + (if w a = 2 then 2 else 0) := by
        rcases hw a with h | h <;> simp [h]
      calc
        (∑ a, w a) = ∑ a, ((if w a = 1 then 1 else 0) + (if w a = 2 then 2 else 0)) := Finset.sum_congr rfl (fun a ha => he a)
        _ = _ := by rw [Finset.sum_add_distrib]; simp [Finset.sum_ite, mul_comm]
    refine ⟨f, fun i => rfl, hw, ?_, ?_⟩
    · change (Finset.univ.filter (fun a => w a = 1)).card = _
      omega
    · change (Finset.univ.filter (fun a => w a = 2)).card = _
      omega
  obtain ⟨f, hf, hwf, hsf, htf⟩ := coord n u hn hu
  obtain ⟨g, hg, hwg, hsg, htg⟩ := coord n v hn hv
  dsimp only
  let b := fun x : Fin n × Fin n => (f x.1, g x.2)
  let wf := fun a => (Finset.univ.filter (fun i => f i = a)).card
  let wg := fun a => (Finset.univ.filter (fun i => g i = a)).card
  let w := fun a => (Finset.univ.filter (fun x => b x = a)).card
  have hw (a) : w a = wf a.1 * wg a.2 := by
    rcases a with ⟨a,c⟩
    dsimp [w, wf, wg, b]
    simp only [Prod.mk.injEq, ← Finset.univ_product_univ]
    rw [Finset.filter_product (fun i => f i = a) (fun i => g i = c), Finset.card_product]
  refine ⟨b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    change w a = 1 ∨ w a = 2 ∨ w a = 4
    rw [hw]
    rcases hwf a.1 with h | h <;> rcases hwg a.2 with h' | h' <;> simp [wf, wg, h, h']
  · simpa [w, pow_two] using Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n × Fin n)) (Finset.univ : Finset (Fin (n-(n-1)/u) × Fin (n-(n-1)/v))) b
  · change (Finset.univ.filter (fun a => w a = 1)).card = _
    have he (a) : w a = 1 ↔ wf a.1 = 1 ∧ wg a.2 = 1 := by
      rw [hw]
      rcases hwf a.1 with h | h <;> rcases hwg a.2 with h' | h' <;> simp [wf, wg, h, h']
    simp_rw [he]
    rw [← Finset.univ_product_univ, Finset.filter_product (fun a => wf a = 1) (fun a => wg a = 1), Finset.card_product]
    exact congrArg₂ (· * ·) hsf hsg
  · change (Finset.univ.filter (fun a => w a = 4)).card = _
    have he (a) : w a = 4 ↔ wf a.1 = 2 ∧ wg a.2 = 2 := by
      rw [hw]
      rcases hwf a.1 with h | h <;> rcases hwg a.2 with h' | h' <;> simp [wf, wg, h, h']
    simp_rw [he]
    rw [← Finset.univ_product_univ, Finset.filter_product (fun a => wf a = 2) (fun a => wg a = 2), Finset.card_product]
    exact congrArg₂ (· * ·) htf htg
  · have bound (d r : ℕ) (hd : 0 < d) : (Finset.univ.filter (fun i : Fin n => i.val/d=r)).card ≤ d := by
      conv_rhs => rw [← Finset.card_range d]
      apply Finset.card_le_card_of_injOn (fun i : Fin n => i.val % d)
      · intro i hi
        exact Finset.mem_range.mpr (Nat.mod_lt _ hd)
      · intro i hi j hj he
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        have h₁ := Nat.mod_add_div i.val d
        have h₂ := Nat.mod_add_div j.val d
        apply Fin.ext
        rw [hi'] at h₁
        rw [hj'] at h₂
        change i.val % d = j.val % d at he
        omega
    intro r s
    rw [← Finset.univ_product_univ, Finset.filter_product (fun i : Fin n => i.val/u=r) (fun i : Fin n => i.val/v=s), Finset.card_product]
    exact Nat.mul_le_mul (bound u r (by omega)) (bound v s (by omega))
  · have step (d i j : ℕ) (hd : 2 ≤ d) (hij : i+1=j) (hdiv : i/d ≠ j/d) : i-i/d=j-j/d := by
      subst j
      have h₁ := Nat.div_le_self i d
      have h₂ := Nat.div_le_self (i+1) d
      have h₃ := Nat.div_le_div_right (show i ≤ i+1 by omega) (c := d)
      have h₄ : (i+1)/d ≤ i/d+1 := by
        have hi := Nat.mod_add_div i d
        have hm := Nat.mod_lt i (show 0 < d by omega)
        apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul (by omega)).2
        nlinarith
      omega
    intro x y he hne
    have hadj : (x.1.val = y.1.val ∧ (x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val)) ∨ (x.2.val = y.2.val ∧ (x.1.val+1=y.1.val ∨ y.1.val+1=x.1.val)) := by
      simp only [abs_eq_max_neg, max_def] at he
      split_ifs at he <;> omega
    have h₁ : (x.1 : ℤ) = y.1 ∨ (x.2 : ℤ) = y.2 := by omega
    apply Prod.ext
    · change f x.1 = f y.1
      rcases h₁ with h | h
      · congr 1
        exact Fin.ext (by omega)
      · have heq : x.2 = y.2 := Fin.ext (by omega)
        have hd : x.1.val/u ≠ y.1.val/u := by
          intro hh
          apply hne
          simp [heq, hh]
        apply Fin.ext
        rw [hf, hf]
        have hor : x.1.val+1=y.1.val ∨ y.1.val+1=x.1.val := by omega
        rcases hor with h | h
        · exact step u _ _ hu h hd
        · exact (step u _ _ hu h hd.symm).symm
    · change g x.2 = g y.2
      rcases h₁ with h | h
      · have heq : x.1 = y.1 := Fin.ext (by omega)
        have hd : x.2.val/v ≠ y.2.val/v := by
          intro hh
          apply hne
          simp [heq, hh]
        apply Fin.ext
        rw [hg, hg]
        have hor : x.2.val+1=y.2.val ∨ y.2.val+1=x.2.val := by omega
        rcases hor with h | h
        · exact step v _ _ hv h hd
        · exact (step v _ _ hv h hd.symm).symm
      · congr 1
        exact Fin.ext (by omega)
