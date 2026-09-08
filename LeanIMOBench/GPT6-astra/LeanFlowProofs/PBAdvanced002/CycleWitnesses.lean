import LeanFlowProofs.PBAdvanced002.ShortImageIterate
import Mathlib

theorem LeanFlowPB002.cycle_witnesses {V : Type*} [Fintype V] (R : V → V → Prop) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  ∃ (m : ℕ) (w : Fin m → V) (c : Fin m → ℕ),
    (∀ i : Fin m, 0 < c i ∧ w i ∈ F^[c i] ({w i} : Set V)) ∧
    Finset.sum Finset.univ c ≤ Fintype.card V ∧
    (∀ (v : V) (k : ℕ), 0 < k → v ∈ F^[k] ({v} : Set V) →
      ∃ i : Fin m,
        (∃ a : ℕ, w i ∈ F^[a] ({v} : Set V)) ∧
        (∃ b : ℕ, v ∈ F^[b] ({w i} : Set V))) := by 
  classical
  dsimp only
  let F : Set V → Set V := fun A => {y | ∃ x ∈ A, R x y}
  let E : V → V → Prop := fun x y => ∃ k, y ∈ F^[k] ({x} : Set V)
  have er (x : V) : E x x := ⟨0, by simp⟩
  have step (x y : V) (h : R x y) : E x y := ⟨1, x, by simp, h⟩
  have comp (a b : ℕ) (x y z : V)
      (h : y ∈ F^[a] ({x} : Set V)) (h' : z ∈ F^[b] ({y} : Set V)) :
      z ∈ F^[a+b] ({x} : Set V) := by
    induction b generalizing z with
    | zero => simpa using (show z = y from h') ▸ h
    | succ b ih =>
      rw [Function.iterate_succ_apply'] at h'
      rw [Nat.add_succ, Function.iterate_succ_apply']
      obtain ⟨u, hu, huz⟩ := h'
      exact ⟨u, ih u hu, huz⟩
  have et {x y z : V} (h : E x y) (h' : E y z) : E x z := by
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := h'
    exact ⟨a+b, comp a b x y z ha hb⟩
  let S : Setoid V := ⟨fun x y => E x y ∧ E y x,
    ⟨fun x => ⟨er x, er x⟩, fun h => ⟨h.2,h.1⟩,
      fun h h' => ⟨et h.1 h'.1, et h'.2 h.2⟩⟩⟩
  let Q := Quotient S
  let q : V → Q := Quotient.mk S
  have qe (x y : V) : q x = q y ↔ E x y ∧ E y x := Quotient.eq
  letI : Fintype Q := Fintype.ofFinite Q
  let C (s : Q) := {v : V // q v = s}
  let G (s : Q) : Set (C s) → Set (C s) :=
    fun A => {y | ∃ x ∈ A, R x.val y.val}
  have project (s : Q) (k : ℕ) (x y : C s)
      (h : y ∈ (G s)^[k] ({x} : Set (C s))) :
      y.val ∈ F^[k] ({x.val} : Set V) := by
    induction k generalizing y with
    | zero => simpa using congrArg Subtype.val (show y = x from h)
    | succ k ih =>
      rw [Function.iterate_succ_apply'] at h ⊢
      obtain ⟨z, hz, hzy⟩ := h
      exact ⟨z.val, ih z hz, hzy⟩
  have restrict (s : Q) (k : ℕ) (x y : C s)
      (h : y.val ∈ F^[k] ({x.val} : Set V)) :
      y ∈ (G s)^[k] ({x} : Set (C s)) := by
    induction k generalizing y with
    | zero => exact Subtype.ext (show y.val = x.val from h)
    | succ k ih =>
      rw [Function.iterate_succ_apply'] at h ⊢
      obtain ⟨z, hz, hzy⟩ := h
      have hxz : E x.val z := ⟨k, hz⟩
      have hzx : E z x.val := et (step z y.val hzy)
        ((qe x.val y.val).mp (x.property.trans y.property.symm)).2
      let z' : C s := ⟨z, ((qe x.val z).mpr ⟨hxz,hzx⟩).symm.trans x.property⟩
      exact ⟨z', ih z' hz, hzy⟩
  let Cyc (s : Q) := ∃ x : C s, ∃ k : ℕ, 0 < k ∧ x ∈ (G s)^[k] ({x} : Set (C s))
  have shortcycle (s : Q) (hs : Cyc s) :
      ∃ x : C s, ∃ k : ℕ, 0 < k ∧ x ∈ (G s)^[k] ({x} : Set (C s)) ∧ k ≤ Fintype.card (C s) := by
    obtain ⟨x, k, hk, hx⟩ := hs
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [Function.iterate_succ_apply'] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨h, hh, hp⟩ := LeanFlowPB002.short_image_iterate (fun a b : C s => R a.val b.val) n x y hy
    refine ⟨x, h+1, by omega, ?_, by omega⟩
    rw [Function.iterate_succ_apply']
    exact ⟨y, hp, hyx⟩
  let I := {s : Q // Cyc s}
  choose w c hc using (fun i : I => shortcycle i.val i.property)
  have hsum : (∑ i : I, c i) ≤ Fintype.card V := by
    calc
      (∑ i : I, c i) ≤ ∑ i : I, Fintype.card (C i.val) :=
        Finset.sum_le_sum (fun i _ => (hc i).2.2)
      _ = Fintype.card ((i : I) × C i.val) := Fintype.card_sigma.symm
      _ ≤ Fintype.card V := by
        apply Fintype.card_le_of_injective (fun p : (i : I) × C i.val => p.2.val)
        intro a b hab
        have hi : a.1 = b.1 := Subtype.ext (a.2.property.symm.trans ((congrArg q hab).trans b.2.property))
        cases a with
        | mk a x =>
          cases b with
          | mk b y =>
            dsimp only at hi hab
            subst b
            have hxy : x = y := Subtype.ext hab
            subst y
            rfl
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, (fun i => (w (e i)).val), (fun i => c (e i)), ?_, ?_, ?_⟩
  · intro i
    exact ⟨(hc (e i)).1, project _ _ _ _ (hc (e i)).2.1⟩
  · exact (e.sum_comp c).le.trans hsum
  · intro v k hk hv
    let v' : C (q v) := ⟨v, rfl⟩
    have hcy : Cyc (q v) := ⟨v', k, hk, restrict (q v) k v' v' hv⟩
    let i : I := ⟨q v, hcy⟩
    refine ⟨e.symm i, ?_⟩
    change E v (w (e (e.symm i))).val ∧ E (w (e (e.symm i))).val v
    rw [e.apply_symm_apply]
    exact (qe v (w i).val).mp (w i).property.symm

