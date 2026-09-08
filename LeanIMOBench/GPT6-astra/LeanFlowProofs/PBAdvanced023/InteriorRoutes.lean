import Mathlib

theorem LeanFlow.PB023.interiorRoutes (C : ℕ) (hC : 3 ≤ C) :
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
    ∀ c : ℕ, 1 < c → c < C →
      ∃ P Q : List (ℕ × ℕ),
        valid P ∧ valid Q ∧
        ∀ S : Set (ℕ × ℕ), legal S → (2, c) ∈ S →
          (∀ x : ℕ × ℕ, x ∈ P → x ∉ S) ∨
          (∀ x : ℕ × ℕ, x ∈ Q → x ∉ S) := by classical
  intro onBoard valid legal c hc hcC
  let R : (ℕ × ℕ) → (ℕ × ℕ) → Prop := fun a b => onBoard b ∧
    abs ((a.1 : ℤ) - (b.1 : ℤ)) + abs ((a.2 : ℤ) - (b.2 : ℤ)) = 1
  have prepend (A : (ℕ × ℕ) → Prop) : ∀ (n : ℕ) (f : ℕ → ℕ × ℕ)
      (T : List (ℕ × ℕ)) (z : ℕ × ℕ),
      T.head? = some (f n) → T.getLast? = some z →
      (∀ x ∈ T, A x) → T.Chain' R →
      (∀ i, i < n → A (f i)) → (∀ i, i < n → R (f i) (f (i+1))) →
      ∃ P : List (ℕ × ℕ), P.head? = some (f 0) ∧ P.getLast? = some z ∧
        (∀ x ∈ P, A x) ∧ P.Chain' R := by
    intro n
    induction n with
    | zero =>
      intro f T z hh hl ha hr hf hs
      exact ⟨T, hh, hl, ha, hr⟩
    | succ n ih =>
      intro f T z hh hl ha hr hf hs
      obtain ⟨P, ph, pl, pa, pr⟩ := ih (fun i => f (i+1)) T z hh hl ha hr
        (by intro i hi; exact hf (i+1) (by omega))
        (by intro i hi; exact hs (i+1) (by omega))
      refine ⟨f 0 :: P, rfl, ?_, ?_, ?_⟩
      · cases P with
        | nil => simp at ph
        | cons a l => simpa using pl
      · intro x hx
        rcases List.mem_cons.mp hx with h | h
        · subst x; exact hf 0 (by omega)
        · exact pa x h
      · cases P with
        | nil => simp at ph
        | cons a l =>
          simp only [List.head?_cons, Option.some.injEq] at ph
          subst a
          exact List.isChain_cons_cons.mpr ⟨hs 0 (by omega), pr⟩
  have route (d : ℕ) (hd : 0 < d) (hdC : d ≤ C)
      (hadj : abs ((d : ℤ) - (c : ℤ)) = 1) :
      ∃ P : List (ℕ × ℕ), valid P ∧
        ∀ x ∈ P, x.1 = 1 ∨ x = (2,d) ∨ x = (3,d) ∨ (3 ≤ x.1 ∧ x.2 = c) := by
    let A : (ℕ × ℕ) → Prop := fun x => onBoard x ∧
      (x.1 = 1 ∨ x = (2,d) ∨ x = (3,d) ∨ (3 ≤ x.1 ∧ x.2 = c))
    have hz : A (C+1,c) := by dsimp [A, onBoard]; omega
    obtain ⟨T, th, tl, ta, tr⟩ := prepend A (C-2) (fun i => (i+3,c))
      [(C+1,c)] (C+1,c)
      (by simp; congr 2; omega) (by simp)
      (by simpa using hz) (by change List.IsChain R [_]; simp)
      (by intro i hi; dsimp [A, onBoard]; omega)
      (by
        intro i hi
        dsimp [R, onBoard]
        constructor
        · omega
        · simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, sub_self, abs_zero, add_zero]
          have : (i : ℤ) + 3 - (↑i + 1 + 3) = -1 := by ring
          rw [this]; norm_num)
    have single (a b : ℕ × ℕ) (P : List (ℕ × ℕ))
        (ph : P.head? = some b) (pl : P.getLast? = some (C+1,c))
        (pa : ∀ x ∈ P, A x) (pr : P.Chain' R) (aa : A a) (ar : R a b) :
        ∃ Q : List (ℕ × ℕ), Q.head? = some a ∧ Q.getLast? = some (C+1,c) ∧
          (∀ x ∈ Q, A x) ∧ Q.Chain' R := by
      exact prepend A 1 (fun i => if i = 0 then a else b) P (C+1,c)
        (by simpa using ph) pl pa pr
        (by intro i hi; have hi0 : i = 0 := (by omega); simpa [hi0] using aa)
        (by intro i hi; have hi0 : i = 0 := (by omega); simpa [hi0] using ar)
    obtain ⟨U, uh, ul, ua, ur⟩ := single (3,d) (3,c) T th tl ta tr
      (by exact ⟨(by dsimp [onBoard]; omega), Or.inr (Or.inr (Or.inl rfl))⟩)
      (by simpa [R, onBoard, hadj] using (show 0 < (3:ℕ) ∧ 3 ≤ C+1 ∧ 0 < c ∧ c ≤ C by omega))
    obtain ⟨V, vh, vl, va, vr⟩ := prepend A 2 (fun i => (i+1,d)) U (C+1,c)
      uh ul ua ur
      (by
        intro i hi
        refine ⟨(by dsimp [onBoard]; omega), ?_⟩
        interval_cases i
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl))
      (by intro i hi; dsimp [R, onBoard]; constructor; omega
          simp only [Nat.cast_add, Nat.cast_one, sub_self, abs_zero, add_zero]
          have : (i : ℤ) + 1 - (↑i + 1 + 1) = -1 := by ring
          rw [this]; norm_num)
    obtain ⟨P, ph, pl, pa, pr⟩ := prepend A (d-1) (fun i => (1,i+1)) V (C+1,c)
      (by simpa [Nat.sub_add_cancel hd] using vh) vl va vr
      (by intro i hi; dsimp [A, onBoard]; omega)
      (by intro i hi; dsimp [R, onBoard]; constructor; omega
          simp only [Nat.cast_add, Nat.cast_one, sub_self, abs_zero, zero_add]
          have : (i : ℤ) + 1 - (↑i + 1 + 1) = -1 := by ring
          rw [this]; norm_num)
    exact ⟨P, ⟨ph, ⟨(C+1,c), ⟨rfl, hz.1⟩, pl⟩, fun x hx => (pa x hx).1, pr⟩,
      fun x hx => (pa x hx).2⟩
  obtain ⟨P, hp, hpm⟩ := route (c-1) (by omega) (by omega) (by
    rw [Nat.cast_sub (by omega : 1 ≤ c)]
    have : (c : ℤ) - ↑(1:ℕ) - ↑c = -1 := by push_cast; ring
    rw [this]; norm_num)
  obtain ⟨Q, hq, hqm⟩ := route (c+1) (by omega) (by omega) (by
    rw [Nat.cast_add, Nat.cast_one]
    have : (c : ℤ) + 1 - ↑c = 1 := by ring
    rw [this]; norm_num)
  refine ⟨P, Q, hp, hq, ?_⟩
  intro S hS hSc
  have row_unique (r a b : ℕ) (hr : 2 ≤ r ∧ r ≤ C)
      (ha : (r,a) ∈ S) (hb : (r,b) ∈ S) : a = b := by
    obtain ⟨k, hk, hu⟩ := hS.2.1 r hr
    exact (hu a ha).trans (hu b hb).symm
  have collision (d : ℕ) (hne : d ≠ c) (L : List (ℕ × ℕ))
      (hm : ∀ x ∈ L, x.1 = 1 ∨ x = (2,d) ∨ x = (3,d) ∨ (3 ≤ x.1 ∧ x.2 = c)) :
      ∀ x ∈ L, x ∈ S → x = (3,d) := by
    intro x hx hs
    rcases hm x hx with ht | ht | ht | ht
    · have := (hS.1 x.1 x.2 hs).1.1; omega
    · subst x
      exact False.elim (hne (row_unique 2 d c (by omega) hs hSc))
    · exact ht
    · have he := hS.2.2 x.1 x.2 2 c hs hSc ht.2
      omega
  by_cases hsafe : ∀ x ∈ P, x ∉ S
  · exact Or.inl hsafe
  · right
    push_neg at hsafe
    obtain ⟨x, hx, hsx⟩ := hsafe
    have he := collision (c-1) (by omega) P hpm x hx hsx
    have hleft : (3,c-1) ∈ S := he ▸ hsx
    intro y hy hsy
    have he' := collision (c+1) (by omega) Q hqm y hy hsy
    have hright : (3,c+1) ∈ S := he' ▸ hsy
    have := row_unique 3 (c-1) (c+1) (by omega) hleft hright
    omega
