import Mathlib

theorem LeanFlow.PB023.boundaryRecovery (C : ℕ) (hC : 3 ≤ C) :
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
    ∀ c : ℕ, (c = 1 ∨ c = C) →
      ∃ P : List (ℕ × ℕ),
        valid P ∧
        ∀ i : Fin P.length,
          ∃ Q : List (ℕ × ℕ),
            valid Q ∧
            ∀ S : Set (ℕ × ℕ),
              legal S → (2, c) ∈ S → first P S i →
              ∀ x : ℕ × ℕ, x ∈ Q → x ∉ S := by classical
  dsimp only
  intro c hc
  let B : ℕ × ℕ → Prop := fun x => 0 < x.1 ∧ x.1 ≤ C + 1 ∧ 0 < x.2 ∧ x.2 ≤ C
  let A : (ℕ × ℕ) → (ℕ × ℕ) → Prop := fun x y =>
    abs ((x.1 : ℤ) - y.1) + abs ((x.2 : ℤ) - y.2) = 1
  have mkvalid (n : ℕ) (hn : 0 < n) (f : ℕ → ℕ × ℕ)
      (h0 : f 0 = (1, 1)) (he : (f (n-1)).1 = C+1)
      (hb : ∀ k, k < n → B (f k))
      (ha : ∀ k, k+1 < n → A (f k) (f (k+1))) :
      let P := List.ofFn (fun i : Fin n => f i.val)
      P.head? = some (1,1) ∧
      (∃ x, (x.1 = C+1 ∧ B x) ∧ P.getLast? = some x) ∧
      (∀ x, x ∈ P → B x) ∧ P.Chain' (fun a b => B b ∧ A a b) := by
    dsimp only
    have hne : List.ofFn (fun i : Fin n => f i.val) ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_ofFn, List.length_nil] at this
      omega
    refine ⟨?_, ⟨f (n-1), ⟨he, hb _ (by omega)⟩, ?_⟩, ?_, ?_⟩
    · rw [List.head?_eq_head hne, List.head_ofFn]
      exact congrArg some h0
    · rw [List.getLast?_eq_getLast hne, List.getLast_ofFn]
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hb _ i.isLt
    · apply List.isChain_ofFn.mpr
      intro k hk
      exact ⟨hb _ hk, ha _ hk⟩
  let e : ℕ → ℕ := fun s => if c = 1 then s+1 else C-s
  let a : ℕ := e 1 - 1
  have ec : e 0 = c := by rcases hc with hc | hc <;> simp [e, hc]; omega
  have ea : e 1 = a+1 := by dsimp [a, e]; split_ifs <;> omega
  have ab : a < C := by dsimp [a, e]; split_ifs <;> omega
  have eb (s : ℕ) (hs : s < C) : 0 < e s ∧ e s ≤ C := by
    dsimp [e]; split_ifs <;> omega
  have ei (s t : ℕ) (hs : s < C) (ht : t < C) (he : e s = e t) : s=t := by
    dsimp [e] at he; split_ifs at he <;> omega
  let wrap : (ℕ → ℕ × ℕ) → ℕ → ℕ × ℕ := fun f k =>
    if k < a then (1,k+1) else f (k-a)
  have wrapvalid (n : ℕ) (hn : 0 < n) (f : ℕ → ℕ × ℕ)
      (h0 : f 0 = (1,e 1)) (he : (f (n-1)).1 = C+1)
      (hb : ∀ k, k < n → B (f k))
      (ha : ∀ k, k+1 < n → A (f k) (f (k+1))) :
      let P := List.ofFn (fun i : Fin (a+n) => wrap f i.val)
      P.head? = some (1,1) ∧
      (∃ x, (x.1 = C+1 ∧ B x) ∧ P.getLast? = some x) ∧
      (∀ x, x ∈ P → B x) ∧ P.Chain' (fun a b => B b ∧ A a b) := by
    refine mkvalid (a+n) (by omega) (wrap f) ?_ ?_ ?_ ?_
    · dsimp [wrap]
      split_ifs with h
      · rfl
      · simpa [show a=0 by omega, show e 1=1 by omega] using h0
    · simpa [wrap, show ¬ a+n-1<a by omega,
        show a+n-1-a=n-1 by omega] using he
    · intro k hk
      dsimp [wrap]
      split_ifs with h
      · dsimp [B]; omega
      · exact hb _ (by omega)
    · intro k hk
      dsimp [wrap]
      split_ifs with h h'
      · dsimp [A]; simp only [abs_eq_max_neg]; omega
      · have hka : k+1=a := by omega
        rw [show k+1-a=0 by omega, h0]
        dsimp [A]; simp only [abs_eq_max_neg]; omega
      · omega
      · simpa [show k+1-a=(k-a)+1 by omega] using ha (k-a) (by omega)
  let f : ℕ → ℕ × ℕ := fun k =>
    if k = 2*C-2 then (C+1, e (C-1)) else ((k+1)/2+1, e (k/2+1))
  have f0 : f 0 = (1,e 1) := by simp [f, show ¬0=2*C-2 by omega]
  have fend : (f (2*C-2)).1 = C+1 := by simp [f]
  have fb (k : ℕ) (hk : k < 2*C-1) : B (f k) := by
    dsimp [f]
    split_ifs with h
    · have := eb (C-1) (by omega)
      dsimp [B]; omega
    · have := eb (k/2+1) (by omega)
      dsimp [B]; omega
  have fa (k : ℕ) (hk : k+1 < 2*C-1) : A (f k) (f (k+1)) := by
    dsimp [f, A, e]
    split_ifs <;> simp only [Prod.fst, Prod.snd, abs_eq_max_neg] <;> omega
  let P := List.ofFn (fun i : Fin (a+(2*C-1)) => wrap f i.val)
  have pv := wrapvalid (2*C-1) (by omega) f f0
    (by simpa [show 2*C-1-1=2*C-2 by omega] using fend) fb fa
  refine ⟨P, pv, ?_⟩
  intro i
  by_cases obs : ∃ S : Set (ℕ × ℕ),
      ((∀ r c, (r,c) ∈ S → (2 ≤ r ∧ r ≤ C) ∧ (1 ≤ c ∧ c ≤ C)) ∧
       (∀ r, (2 ≤ r ∧ r ≤ C) → ∃! c, (r,c) ∈ S) ∧
       (∀ r₁ c₁ r₂ c₂, (r₁,c₁) ∈ S → (r₂,c₂) ∈ S → c₁=c₂ → r₁=r₂)) ∧
      (2,c) ∈ S ∧ (P.get i ∈ S ∧ ∀ j : Fin P.length, j.val < i.val → P.get j ∉ S)
  swap
  · refine ⟨P, pv, ?_⟩
    intro S hs h2 hi x hx
    exact (obs ⟨S, hs, h2, hi⟩).elim
  obtain ⟨S₀, hs₀, h2₀, hi₀⟩ := obs
  have ib : i.val < a+(2*C-1) := by simpa [P] using i.isLt
  have hit₀ : wrap f i.val ∈ S₀ := by simpa [P, List.get_ofFn] using hi₀.1
  have ia : a ≤ i.val := by
    by_contra h
    have hw : wrap f i.val = (1,i.val+1) := by simp [wrap, show i.val<a by omega]
    rw [hw] at hit₀
    have := hs₀.1 _ _ hit₀
    omega
  let t := i.val-a
  let R := (t+1)/2
  have tb : t < 2*C-1 := by dsimp [t]; omega
  have ht₀ : f t ∈ S₀ := by simpa [wrap, show ¬i.val<a by omega] using hit₀
  have tn : t ≠ 2*C-2 := by
    intro h
    have : (C+1,e (C-1)) ∈ S₀ := by simpa [f,h] using ht₀
    have := hs₀.1 _ _ this
    omega
  have coord₀ : (R+1,e (t/2+1)) ∈ S₀ := by simpa [f,tn,R] using ht₀
  have rb : R ≤ C-1 := by
    have := hs₀.1 _ _ coord₀
    omega
  have r2 : 2 ≤ R := by
    have hh := hs₀.1 _ _ coord₀
    by_contra h
    have re : R+1=2 := by omega
    rw [re] at coord₀
    obtain ⟨d,hd,hdu⟩ := hs₀.2.1 2 ⟨by omega, by omega⟩
    have he : e (t/2+1) = e 0 := by
      rw [ec]
      exact (hdu _ coord₀).trans (hdu _ h2₀).symm
    have := ei (t/2+1) 0 (by omega) (by omega) he
    omega
  let g : ℕ → ℕ × ℕ := fun k =>
    if k+2 < 2*R then ((k+1)/2+1, e (k/2+1)) else
    if k+2 < 3*R then (R+1,e (3*R-3-k)) else
    (k+4-2*R,e 0)
  have g0 : g 0 = (1,e 1) := by simp [g, show 0+2<2*R by omega]
  have gend : (g (C+2*R-3)).1 = C+1 := by
    dsimp [g]; split_ifs <;> simp only [Prod.fst] <;> omega
  have gb (k : ℕ) (hk : k < C+2*R-2) : B (g k) := by
    dsimp [g]
    split_ifs with h h'
    · have := eb (k/2+1) (by omega)
      dsimp [B]; omega
    · have := eb (3*R-3-k) (by omega)
      dsimp [B]; omega
    · have := eb 0 (by omega)
      dsimp [B]; omega
  have ga (k : ℕ) (hk : k+1 < C+2*R-2) : A (g k) (g (k+1)) := by
    dsimp [g,A,e]
    split_ifs <;> simp only [Prod.fst,Prod.snd,abs_eq_max_neg] <;> omega
  let Q := List.ofFn (fun j : Fin (a+(C+2*R-2)) => wrap g j.val)
  have qv := wrapvalid (C+2*R-2) (by omega) g g0
    (by simpa [show C+2*R-2-1=C+2*R-3 by omega] using gend) gb ga
  refine ⟨Q, qv, ?_⟩
  intro S hs h2 hi x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  intro hmem
  by_cases ja : j.val < a
  · have hm : (1,j.val+1) ∈ S := by simpa [wrap,ja] using hmem
    have := hs.1 _ _ hm
    omega
  have jm : g (j.val-a) ∈ S := by simpa [wrap,ja] using hmem
  have coord : (R+1,e (t/2+1)) ∈ S := by
    simpa [P, List.get_ofFn, wrap, show ¬i.val<a by omega, f, tn, t, R] using hi.1
  by_cases early : (j.val-a)+2 < 2*R
  · have ji : j.val < i.val := by dsimp [R,t] at early; omega
    have jP : j.val < P.length := by simpa [P] using (show j.val < a+(2*C-1) by omega)
    have je : wrap f j.val = g (j.val-a) := by
      simp [wrap, ja, f, g, early, show j.val-a ≠ 2*C-2 by omega]
    apply hi.2 ⟨j.val,jP⟩ ji
    simpa only [P, List.get_ofFn, Fin.coe_cast, je] using jm
  · dsimp [g] at jm
    rw [if_neg early] at jm
    split_ifs at jm with middle
    · obtain ⟨d,hd,hdu⟩ := hs.2.1 (R+1) ⟨by omega, by omega⟩
      have he : e (3*R-3-(j.val-a)) = e (t/2+1) :=
        (hdu _ jm).trans (hdu _ coord).symm
      have hh := ei (3*R-3-(j.val-a)) (t/2+1) (by omega) (by omega) he
      dsimp [R] at early
      omega
    · have hr := hs.2.2 _ _ _ _ jm h2 ec
      omega
