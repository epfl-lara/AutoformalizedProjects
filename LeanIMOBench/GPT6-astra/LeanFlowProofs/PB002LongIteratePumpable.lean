import LeanFlowProofs.PB002LiftMutualReachability
import LeanFlowProofs.PB002LongIterateVisitsCycle
import LeanFlowProofs.PB002ShortImageIterate
import Mathlib

theorem LeanFlowPB002.long_iterate_pumpable {V : Type*} [Fintype V]
    (R : V → V → Prop) (P : ℕ) (hP : 0 < P)
    (m : ℕ) (w : Fin m → V) (c : Fin m → ℕ) :
  let F : Set V → Set V := fun A => {y : V | ∃ x ∈ A, R x y}
  (∀ i : Fin m, 0 < c i ∧ w i ∈ F^[c i] ({w i} : Set V)) →
  (∀ i : Fin m, c i ∣ P) →
  (∀ (v : V) (k : ℕ), 0 < k → v ∈ F^[k] ({v} : Set V) →
    ∃ i : Fin m,
      (∃ a : ℕ, w i ∈ F^[a] ({v} : Set V)) ∧
      (∃ b : ℕ, v ∈ F^[b] ({w i} : Set V))) →
  ∀ (ell : ℕ) (x y : V), Fintype.card V ≤ ell →
    y ∈ F^[ell] ({x} : Set V) →
    ∃ h : ℕ,
      h < 2 * Fintype.card V * P ∧ h % P = ell % P ∧
      (∀ j : ℕ, y ∈ F^[h + j * P] ({x} : Set V)) := by classical
  intro F hc hdvd hcover ell x y hell hy
  have cat : ∀ {U : Type _} (S : U → U → Prop) (a b : ℕ) (u v z : U),
      let H : Set U → Set U := fun A => {t | ∃ s ∈ A, S s t}
      v ∈ H^[a] ({u} : Set U) → z ∈ H^[b] ({v} : Set U) →
      z ∈ H^[a+b] ({u} : Set U) := by
    intro U S a b u v z H hv hz
    induction b generalizing z with
    | zero => simpa using (by simpa using hz : z = v) ▸ hv
    | succ b ih =>
      rw [Function.iterate_succ_apply'] at hz
      rw [Nat.add_succ, Function.iterate_succ_apply']
      obtain ⟨t, ht, htz⟩ := hz
      exact ⟨t, ih t ht, htz⟩
  have rep (k j : ℕ) (v : V) (hv : v ∈ F^[k] ({v} : Set V)) :
      v ∈ F^[j*k] ({v} : Set V) := by
    induction j with
    | zero => simp
    | succ j ih =>
      simpa [Nat.succ_mul] using cat R (j*k) k v v v ih hv
  let S : (V × Fin P) → (V × Fin P) → Prop :=
    fun p q => R p.1 q.1 ∧ q.2.val = (p.2.val + 1) % P
  let G : Set (V × Fin P) → Set (V × Fin P) :=
    fun A => {q | ∃ p ∈ A, S p q}
  have lift (k : ℕ) (u v : V) (r s : Fin P) :
      (v,s) ∈ G^[k] ({(u,r)} : Set (V × Fin P)) ↔
      v ∈ F^[k] ({u} : Set V) ∧ s.val = (r.val + k) % P := by
    induction k generalizing v s with
    | zero => simp [Fin.ext_iff, Nat.mod_eq_of_lt r.isLt]
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (∃ p ∈ G^[k] ({(u,r)} : Set (V × Fin P)),
        R p.1 v ∧ s.val = (p.2.val + 1) % P) ↔ _
      constructor
      · rintro ⟨⟨t,q⟩, ht, htv, hs⟩
        obtain ⟨ht, hq⟩ := (ih t q).mp ht
        refine ⟨⟨t, ht, htv⟩, ?_⟩
        simpa only [hq, Nat.mod_add_mod, Nat.add_assoc] using hs
      · rintro ⟨⟨t, ht, htv⟩, hs⟩
        let q : Fin P := ⟨(r.val+k)%P, Nat.mod_lt _ hP⟩
        refine ⟨(t,q), (ih t q).mpr ⟨ht, rfl⟩, htv, ?_⟩
        simpa only [q, Nat.mod_add_mod, Nat.add_assoc] using hs
  obtain ⟨v,a,b,d, hab, hd, hva, hyb, hvd⟩ :=
    LeanFlowPB002.long_iterate_visits_cycle R ell x y hell hy
  obtain ⟨i, hvi, hiv⟩ := hcover v d hd hvd
  let r0 : Fin P := ⟨0,hP⟩
  let ra : Fin P := ⟨a%P, Nat.mod_lt _ hP⟩
  let re : Fin P := ⟨ell%P, Nat.mod_lt _ hP⟩
  obtain ⟨s, ⟨e, he⟩, ⟨f, hf⟩⟩ :=
    LeanFlowPB002.lift_mutual_reachability R P hP v (w i) ra hvi hiv
  have hxa : (v,ra) ∈ G^[a] ({(x,r0)} : Set (V × Fin P)) :=
    (lift a x v r0 ra).mpr ⟨hva, by simp [ra,r0]⟩
  have hay : (y,re) ∈ G^[b] ({(v,ra)} : Set (V × Fin P)) :=
    (lift b v y ra re).mpr ⟨hyb, by simp [ra,re, ← hab, Nat.add_mod]⟩
  obtain ⟨a', ha', hxa'⟩ := LeanFlowPB002.short_image_iterate S (a+e)
    (x,r0) (w i,s) (cat S a e _ _ _ hxa he)
  obtain ⟨b', hb', hyb'⟩ := LeanFlowPB002.short_image_iterate S (f+b)
    (w i,s) (y,re) (cat S f b _ _ _ hf hay)
  have hwhole := (lift (a'+b') x y r0 re).mp (cat S a' b' _ _ _ hxa' hyb')
  refine ⟨a'+b', ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Fintype.card_fin] at ha' hb'
    nlinarith
  · simpa [r0,re] using hwhole.2.symm
  · intro j
    have hxw := ((lift a' x (w i) r0 s).mp hxa').1
    have hwy := ((lift b' (w i) y s re).mp hyb').1
    obtain ⟨q,hq⟩ := hdvd i
    have hp : w i ∈ F^[P] ({w i} : Set V) := by
      rw [hq, Nat.mul_comm]
      exact rep (c i) q (w i) (hc i).2
    have hj := rep P j (w i) hp
    have hh := cat R (a'+j*P) b' x (w i) y
      (cat R a' (j*P) x (w i) (w i) hxw hj) hwy
    convert hh using 1 <;> congr 1 <;> omega
